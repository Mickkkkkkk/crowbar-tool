package org.abs_models.crowbar.main

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.data.Stmt
import org.abs_models.crowbar.interfaces.translateExpression
import org.abs_models.crowbar.investigator.CounterexampleGenerator
import org.abs_models.crowbar.tree.LogicNode
import org.abs_models.crowbar.tree.StaticNode
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.tree.getStrategy
import org.abs_models.frontend.ast.*
import org.abs_models.frontend.typechecker.Type
import java.io.File
import java.io.PrintWriter
import java.io.StringWriter
import java.nio.file.Path
import kotlin.reflect.KClass
import kotlin.reflect.full.companionObject
import kotlin.reflect.full.memberFunctions
import kotlin.system.exitProcess

/*
A number of utility functions for user interaction and proof setup
 */
fun output(text : String, level : Verbosity = Verbosity.NORMAL){
    if(verbosity >= level)
        println(text)
}

/*
Loads an ABS model and returns the AST and the initialized repository.
 */
fun load(paths : List<Path>) : Pair<Model,Repository> {
    output("Crowbar  : loading files....")
    val input = paths.map{ File(it.toString()) }
    if(input.any { !it.exists() }) {
        if(reporting) throw Exception("file not found: $paths")
        System.err.println("file not found: $paths")
        exitProcess(-1)
    }

    output("Crowbar  : loading ABS model....")
    val model = try {
        org.abs_models.frontend.parser.Main().parse(input)
    } catch (e : Exception) {
        if(reporting) reportException("error during parsing, aborting", e)
        e.printStackTrace()
        System.err.println("error during parsing, aborting")
        exitProcess(-1)
    }
    if(model.hasParserErrors())
        throw Exception("Compilation failed with parse errors")
    if(model.hasTypeErrors())
        throw Exception("Compilation failed with type errors")

    val repos = Repository(model)


    //initialization: first read the types, then the function definitions and then the specifications
    FunctionRepos.init(model)
    ADTRepos.init(model)
    repos.populateClassReqs(model)
    repos.populateMethodReqs(model)
    return Pair(model, repos)
}


/***************************
 The following functions extract some specification from the AST.
 We only consider formulas as specification, other specifications do not need inheritance and can be directly retrieved.
 ****************************/
fun extractInheritedSpec(iDecl : InterfaceTypeUse, expectedSpec : String, mSig: MethodSig, default:Formula) : Formula? {
    for( miSig in iDecl.decl.findChildren(MethodSig::class.java))
        if(miSig.matches(mSig)) return extractSpec(miSig, expectedSpec,mSig.type, default)

    if(iDecl.decl.getChild(1) !is org.abs_models.frontend.ast.List<*>) throw Exception("Invalid specification AST ${iDecl.decl}")

    @Suppress("UNCHECKED_CAST")
    val uses = iDecl.decl.getChild(1) as org.abs_models.frontend.ast.List<InterfaceTypeUse>
    for(use in uses){
        val next = extractInheritedSpec(use, expectedSpec, mSig, default)
        if(next != null) return next
    }
    return null
}

fun extractInheritedSpec(mSig : MethodSig, expectedSpec : String, default:Formula = True) : Formula {
    val direct = extractSpec(mSig, expectedSpec, mSig.type,default)
    val conDecl = mSig.contextDecl
    if(conDecl is ClassDecl){
        for( iDecl in conDecl.implementedInterfaceUses){
            val next = extractInheritedSpec(iDecl, expectedSpec, mSig, default)
            if(next != null) return And(direct,next)
        }
    }
    return direct
}

fun<T : ASTNode<out ASTNode<*>>?> extractSpec(decl : ASTNode<T>, expectedSpec : String, returnType: Type, default:Formula = True, multipleAllowed:Boolean = true) : Formula {
    var ret : Formula? = null
    if(decl is FunctionDecl){
        for(annotation in decl.annotationList){
            if(!annotation.type.toString().endsWith(".Spec")) continue
            if(annotation.value !is DataConstructorExp) {
                throw Exception("Could not extract any specification from $decl because of the expected value")
            }
            val annotated = annotation.value as DataConstructorExp
            if(annotated.constructor != expectedSpec) continue
            val next = exprToForm(translateExpression(annotated.getParam(0) as Exp,decl.type, emptyMap(),true).first) //todo:check!
            ret = if(ret == null) next else And(ret, next)
            if(!multipleAllowed) break
        }
    }else if (decl is MethodImpl){
        ret = extractInheritedSpec(decl.methodSig,expectedSpec, default)
    }else {
        for (annotation in decl.nodeAnnotations){
            if(!annotation.type.toString().endsWith(".Spec")) continue
            if(annotation.value !is DataConstructorExp) {
                throw Exception("Could not extract any specification from $decl because of the expected value")
            }
            val annotated = annotation.value as DataConstructorExp
            if(annotated.constructor != expectedSpec) continue
            val next = exprToForm(translateExpression(annotated.getParam(0) as Exp,returnType, emptyMap(),true).first)//todo:check!
            ret = if(ret == null) next else And(ret, next)
            if(!multipleAllowed) break
        }
    }
    if(ret == null) {
        ret = default
        if(verbosity >= Verbosity.VVV)
            println("Crowbar-v: Could not extract $expectedSpec specification, using ${default.prettyPrint()}")
    }
    return ret
}

fun extractRoleSpec(classDecl: ClassDecl): Formula {
    return classDecl.annotations.filter {
        it.type.toString()
            .endsWith(".Spec") && it.value is DataConstructorExp && (it.value as DataConstructorExp).constructor == "Role"
    }.map {
        val roleAnnotation = it.value as DataConstructorExp

        if (roleAnnotation.getParam(0) !is StringLiteral)
            throw Exception("First argument of Role annotation should be role name as string")
        if (roleAnnotation.getParam(1) !is FieldUse)
            throw Exception("Second argument of Role annotation should be a field use")

        val roleString = (roleAnnotation.getParam(0) as StringLiteral).content
        val fieldUse = (roleAnnotation.getParam(1) as FieldUse)
        val field = Field(fieldUse.name + "_f", fieldUse.type)
        Predicate("hasRole", listOf(exprToTerm(field), Function("\"$roleString\""))) as Formula
    }.fold(True as Formula) { acc, elem -> And(acc, elem) }
}





/***************************
Utility to extract
 ****************************/
fun Model.extractAllClasses() : List<ClassDecl> =
     this.moduleDecls.filter { !it.name.startsWith("ABS.") }
                     .map { it.decls.filterIsInstance<ClassDecl>() }
                     .foldRight(emptyList()) { a, b -> a + b }

fun Model.extractFunctionDecl(moduleName: String, funcName: String) : FunctionDecl {
    val moduleDecl = moduleDecls.firstOrNull { it.name == moduleName }
    if(moduleDecl == null){
        System.err.println("module not found: $moduleName")
        exitProcess(-1)
    }
    val funcDecl : FunctionDecl? = moduleDecl.decls.firstOrNull { it is FunctionDecl && it.name == funcName } as FunctionDecl?
    if(funcDecl == null){
        if(reporting) throw Exception("function not found: ${moduleName}.$funcName")
        System.err.println("function not found: ${moduleName}.$funcName")
        exitProcess(-1)
    }
    return funcDecl
}

fun Model.extractClassDecl(moduleName: String, className: String) : ClassDecl {
    val moduleDecl = moduleDecls.firstOrNull { it.name == moduleName }
    if(moduleDecl == null){
        if(reporting) throw Exception("module not found: $moduleName")
        System.err.println("module not found: $moduleName")
        exitProcess(-1)
    }
    val classDecl : ClassDecl? = moduleDecl.decls.firstOrNull { it is ClassDecl && it.name == className } as ClassDecl?
    if(classDecl == null){
        if(reporting) throw Exception("class not found: ${moduleName}.${className}")
        System.err.println("class not found: ${moduleName}.${className}")
        exitProcess(-1)
    }
    return classDecl
}

fun FunctionDecl.exctractFunctionNode(usedType: KClass<out DeductType>) : SymbolicNode{
    val callTarget = usedType.memberFunctions.first { it.name == "exctractFunctionNode" }
    val obj = usedType.companionObject!!.objectInstance
    return callTarget.call(obj, this) as SymbolicNode
}
fun Model.exctractMainNode(usedType: KClass<out DeductType>) : SymbolicNode{
    val callTarget = usedType.memberFunctions.first { it.name == "exctractMainNode" }
    val obj = usedType.companionObject!!.objectInstance
    return callTarget.call(obj, this) as SymbolicNode
}

fun ClassDecl.extractInitialNode(usedType: KClass<out DeductType>) : SymbolicNode {
    val callTarget = usedType.memberFunctions.first { it.name == "extractInitialNode" }
    val obj = usedType.companionObject!!.objectInstance
    return callTarget.call(obj, this) as SymbolicNode
}

fun ClassDecl.extractMethodNode(usedType: KClass<out DeductType>, name : String, repos: Repository) : SymbolicNode {
    val callTarget = usedType.memberFunctions.first { it.name == "extractMethodNode" }
    val obj = usedType.companionObject!!.objectInstance
    return callTarget.call(obj, this, name, repos) as SymbolicNode
}




/***************************
Utility to start the symbolic execution
 ****************************/
var count = 0
fun executeNode(node : SymbolicNode, repos: Repository, usedType: KClass<out DeductType>, identifier: String = "unknown") : Boolean{
    output("Crowbar  : starting symbolic execution....")
    val pit = getStrategy(usedType,repos)
    pit.execute(node)

    output("Crowbar-v: symbolic execution tree:",Verbosity.V)
    output(node.debugString(0),Verbosity.V)

    if(!node.finishedExecution()){
        println(node.debugString(0))
        throw Exception("could not finish symbolic execution")
//        exitProcess(-1)
    }

    output("Crowbar  : closing open branches....")
    var closed = true
    for(l in node.collectLeaves()){
        when (l) {
            is LogicNode -> {
                count++
                output("Crowbar-v: "+ deupdatify(l.ante).prettyPrint()+"->"+deupdatify(l.succ).prettyPrint(), Verbosity.V)
                closed = closed && l.evaluate()
            }
            is StaticNode -> {
                output("Crowbar: open static leaf ${l.str}", Verbosity.SILENT)
            }
        }
    }

    if(!closed && investigate) {
        output("Crowbar  : failed to close node, starting investigator....")
        CounterexampleGenerator.investigateAll(node, identifier)
    }

    return closed
}

fun ClassDecl.executeAll(repos: Repository, usedType: KClass<out DeductType>): Boolean{
    val iNode = extractInitialNode(usedType)
    var totalClosed = executeNode(iNode, repos, usedType, "<init>")
    output("Crowbar  : Verification <init>: $totalClosed")

    for(m in methods){
        val node = extractMethodNode(usedType, m.methodSig.name, repos)
        val closed = executeNode(node, repos, usedType, m.methodSig.name)
        output("Crowbar  : Verification ${m.methodSig.name}: $closed")
        totalClosed = totalClosed && closed
    }
    return totalClosed
}

fun ClassDecl.executeAllREPORT(repos: Repository, usedType: KClass<out DeductType>): Boolean{
    try {
        val iNode = extractInitialNode(usedType)
        var totalClosed = executeNode(iNode, repos, usedType, "<init>")
        var csv = ""
        output("Crowbar  : Verification <init>: $totalClosed")
        for (m in methods) {
            csv += "${m.fileName};${(m.parent.parent as ClassDecl).name};${m.methodSig.name};"
            try {
                output("Crowbar  : Verification ${m.methodSig.name} started...")
                val node = extractMethodNode(usedType, m.methodSig.name, repos)
                val closed = executeNode(node, repos, usedType, m.methodSig.name)
                output("Crowbar  : Verification ${m.methodSig.name}: $closed")
                totalClosed = totalClosed && closed

                csv += "OK;NONE\n"
            } catch (e: Exception) {
                val sw = StringWriter()
                (if(e.cause != null)  e.cause else e)!!.printStackTrace(PrintWriter(sw))
                val cause = sw.toString()
                output("Crowbar  : Verification ${m.methodSig.name} failed due to exception:")
                output(sw.toString())
                csv += "ERR;${cause.split("\n")[0]}\n"
                totalClosed = false
            }
        }
        File("${reportPath}").appendText(csv)
        return totalClosed
    }catch (e: Exception) {
        val sw = StringWriter()
        (if(e.cause != null)  e.cause else e)!!.printStackTrace(PrintWriter(sw))
        val cause = sw.toString()
        val csv = "${this.fileName};${this.name};NONE;M_ERR;${cause.split("\n")[0]}\n"
        File("${reportPath}").appendText(csv)
        output("Crowbar  : Verification of initialNode failed due to exception")
        return false
    }

}

/***************************
General utility
 ****************************/
fun normalize(st : Stmt) : Stmt =
    when(st){
        is SeqStmt ->
            when(st.first){
                is SeqStmt -> normalize(SeqStmt(st.first.first,SeqStmt(st.first.second,st.second)))
                else -> SeqStmt(st.first, normalize(st.second))
            }
        else -> st
    }

fun getDeclaration(mSig: MethodSig, cDecl : ClassDecl): InterfaceDecl? =
     cDecl.implementedInterfaceUses.map{ getIDeclaration(mSig, it.decl as InterfaceDecl) }.firstOrNull()

fun getIDeclaration(mSig: MethodSig, iDecl : InterfaceDecl): InterfaceDecl?{
    for(mDecl in iDecl.allMethodSigs){
        if(mDecl.matches(mSig)) return iDecl
    }
    return iDecl.extendedInterfaceUseList.map{ getIDeclaration(mSig, it.decl as InterfaceDecl) }.firstOrNull()
}