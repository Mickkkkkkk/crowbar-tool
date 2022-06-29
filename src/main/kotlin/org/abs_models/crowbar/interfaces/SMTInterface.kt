package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.main.ADTRepos.libPrefix
import org.abs_models.crowbar.main.ADTRepos.objects
import org.abs_models.crowbar.main.ADTRepos.setUsedHeaps
import org.abs_models.crowbar.main.FunctionRepos.concretizeFunctionTosSMT
import org.abs_models.crowbar.types.booleanFunction
import org.abs_models.frontend.typechecker.DataTypeType
import org.abs_models.frontend.typechecker.Type
import java.io.File
import java.util.concurrent.TimeUnit

val mapBuiltinTypeSMT = mapOf(
    "ABS.StdLib.Int" to "Int",
    "ABS.StdLib.Float" to "Real",
    "ABS.StdLib.Bool" to "Bool",
    "ABS.StdLib.String" to "String",
    "Field" to "Int"
)

@Suppress("UNCHECKED_CAST")
fun generateSMT(ante : Formula, succ: Formula, modelCmd: String = "") : String {

    resetWildCards()
    val headerBlock =BlockProofElements(
        listOf(
            SolverOption("set-option :produce-models true"),
            SolverOption("set-logic ALL"),
            FunDecl("valueOf_Int", listOf("Int"), "Int"),
            FunDecl("hasRole", listOf("Int", "String"), "Bool"),
            bindToBuiltinSorts(mapBuiltinTypeSMT),
            DeclareConstSMT("Unit", "Int"),
            Assertion(Eq(Function("Unit"),Function("0"))),
            DeclareSortSMT("UNBOUND"))
                + getPrimitiveDecl(),
        "; static header",
        "; end static header")

    // application of update to generate pre and post condition
    var  pre = deupdatify(ante)
    var post = deupdatify(succ)
    val globaliterate = globalIterate(pre,post)

    val fieldsProofBlock = getFieldsProofBlock(pre,post)
    // generation of the generics occurring in pre and post condition

    val prePlaceholders = pre.iterate { it is Placeholder } as Set<Placeholder>
    val postPlaceholders = post.iterate { it is Placeholder } as Set<Placeholder>
    val allPhs = prePlaceholders.union(postPlaceholders)
    val placeholders = prePlaceholders.intersect(postPlaceholders)
    val globPlaceholders = prePlaceholders.union(postPlaceholders).map {  ProgVar("${it.name}_${it.concrType}", it.concrType)}


    // replacing placeholders in precondition
    (pre.iterate { it is Predicate }.toList() as List<Predicate>).map {
        oldPredicate ->
        var newFormula= (oldPredicate.iterate { el -> el is Placeholder && el in placeholders } as Set<Placeholder>).fold(oldPredicate) {
                acc:Formula, ph : Placeholder->
            And(acc, Predicate("=", listOf(ph, ProgVar("${ph.name}_${ph.concrType}", ph.concrType))))
        }
        val wildcards = oldPredicate.iterate { it is WildCardVar || it is Placeholder } as Set<ProgVar>
         newFormula= Exists(wildcards.toList(), newFormula)
        pre = replaceInFormula(pre as Formula, oldPredicate, newFormula)
    }

    // replacing placeholders in precondition
    post.iterate { it is Predicate }.map {
            oldPredicate ->
        if(placeholders.isNotEmpty()) {
            postPlaceholders.map {
                val globalPh= ProgVar("${it.name}_${it.concrType}", it.concrType)
                val newFormula = replaceInLogicElement(oldPredicate as Predicate, mapOf(Pair(it, globalPh))) as Predicate
                post = replaceInFormula(post as Formula, oldPredicate, newFormula)
            }
        }
    }

    globaliterate["GENERICS"]!!.map {
        ADTRepos.addGeneric((it as DataTypeConst).concrType!! as DataTypeType) }

    val vars =  globaliterate["VARS"]!! as Set<ProgVar>
    val heaps =  globaliterate["HEAPS"]!! as Set<Function>
    val funcs =  globaliterate["FUNCS"]!! as Set<Function>

    val preSMT =  (pre as Formula).toSMT()
    val negPostSMT = Not(post as Formula).toSMT()
    val functionDecl = FunctionRepos.toString()
    val concretizeFunctionTosSMT= concretizeFunctionTosSMT()
    //generation of translation for wildcards
    val wildcards: String = wildCardsConst.map { FunctionDeclSMT(it.key,it.value).toSMT("\n\t") }.joinToString("") { it }
    //generation of translation for fields and variable declarations
    val varsDecl = (vars.union(globPlaceholders).union(allPhs)).joinToString("\n\t"){"(declare-const ${it.name} ${
        translateType(it.concrType)}) ; ${it}\n" +
        if(it.concrType.isInterfaceType)
            "(assert (implements ${it.name} ${it.concrType.qualifiedName}))\n\t"
        else ""
    }


    //generation of translation for object "implements" assertions
    val objectImpl = heaps.joinToString("\n"){
        x:Function ->
        if(x.name in objects)
            objects[x.name]!!.types.joinToString("\n\t") {
                "(assert (implements " +
                        if(x.params.isNotEmpty()){
                        "(${x.name} " +
                        x.params.joinToString (" "){term -> term.toSMT()} +
                        ")  ${it.qualifiedName}))"}
                    else{
                        "${x.name} ${it.qualifiedName}))"
                        }

        }else ""

    }
    //generation of translation for object declaration
    val objectsDecl = heaps.joinToString("\n\t"){"(declare-fun ${it.name} (${it.params.joinToString (" "){
        term ->
        if(term is DataTypeConst) {
            ADTRepos.addGeneric(term.concrType!! as DataTypeType)
            genericTypeSMTName(term.concrType)
        }
        else if(term is Function && term.name in booleanFunction) "Bool"
        else { "Int"
        }
    }}) Int)"

    }

    //generation of translation for function declaration
    val funcsDecl = funcs.joinToString("\n") { "(declare-const ${it.name} Int)"}



    return """
;header
${headerBlock.toSMT("\t")}

;data type declaration
    ${ADTRepos.dTypesToSMT()}

;interface type declaration
    (declare-fun   implements (ABS.StdLib.Int Interface) Bool)
    (declare-fun   extends (Interface Interface) Bool)
    (assert (forall ((i1 Interface) (i2 Interface) (i3 Interface))
     (=> (and (extends i1 i2) (extends i2 i3))
      (extends i1 i3))))
      
    (assert (forall ((i1 Interface) (i2 Interface) (object ABS.StdLib.Int))
     (=> (and (extends i1 i2) (implements object i1))
      (implements object i2))))
      
      ${ADTRepos.interfaceExtendsToSMT()}
      
;generics declaration
    ${ADTRepos.genericsToSMT()}
;heaps declaration
    ${ADTRepos.heapsToSMT()}
;wildcards declaration
    $wildcards
    
; parametric functions decl
    $concretizeFunctionTosSMT
;functions declaration
    $functionDecl
;generic functions declaration :to be implemented and added
;    
${fieldsProofBlock.toSMT("\t")}
;variables declaration
    $varsDecl
;objects declaration
    $objectsDecl
    
;objects interface declaration
    $objectImpl
;funcs declaration
    $funcsDecl
    ; Precondition
    (assert $preSMT )
    ; Negated postcondition
    (assert $negPostSMT) 
    (check-sat)
    $modelCmd
    (exit)
    """.trimIndent()
}

/* https://stackoverflow.com/questions/35421699 */
fun String.runCommand(
        workingDir: File = File("."),
        timeoutAmount: Long = 60,
        timeoutUnit: TimeUnit = TimeUnit.SECONDS
): String? = try {
    ProcessBuilder(split("\\s".toRegex()))
            .directory(workingDir)
            .redirectOutput(ProcessBuilder.Redirect.PIPE)
            .redirectError(ProcessBuilder.Redirect.PIPE)
            .start().apply { waitFor(timeoutAmount, timeoutUnit) }
            .inputStream.bufferedReader().readText()
} catch (e: java.io.IOException) {
    e.printStackTrace()
    null
}


fun plainSMTCommand(smtRep: String) : String? {
    val path = "${tmpPath}out.smt2"
    File(path).writeText(smtRep)
    return "$smtPath $path".runCommand()
}

fun evaluateSMT(smtRep : String) : Boolean {
    val res = plainSMTCommand(smtRep)
    if(res != null && res.trim() == "unsat") return true
    if(res != null && res.trim() == "sat") return false
    if(res != null && res.trim() == "unknown") return false
    throw Exception("Error during SMT evaluation: $res")
}

fun evaluateSMT(ante: Formula, succ: Formula) : Boolean {
    val smtRep = generateSMT(ante, succ)
    if(verbosity >= Verbosity.VV) println("crowbar-v: \n$smtRep")
    return evaluateSMT(smtRep)
}

private val wildCardsConst = mutableMapOf<String,String>()

private var countWildCard = 0

fun createWildCard(dType: String,dTypeConcr: Type) : String{
    val wildCard = "_${countWildCard++}"
    if(dTypeConcr.simpleName in setOf("Pair","Triple"))
        wildCardsConst[wildCard] = genericSMTName(dTypeConcr.qualifiedName,dTypeConcr)
    else
        wildCardsConst[wildCard] = translateType(dTypeConcr)
    return wildCard
}

fun refreshWildCard(name: String, dType: String,dTypeConcr: Type) {
    if(dTypeConcr.simpleName in setOf("Pair","Triple"))
        wildCardsConst[name] = genericSMTName(dTypeConcr.qualifiedName,dTypeConcr)
    else
        wildCardsConst[name] = translateType(dTypeConcr)
}

fun resetWildCards() {
    wildCardsConst.clear()
    countWildCard = 0
}

    /*
    * Function that translates an ABS type into the SMT representation
    */
fun translateType(type:Type) : String{
    return if(type.isUnknownType)
        throw Exception("Unknown Type Cannot be Translated")
    else if (isGeneric(type)) {
        ADTRepos.addGeneric(type as DataTypeType)
        genericTypeSMTName(type)
    }else if(type.isTypeParameter)
        throw Exception("Parameter Type Cannot Be Translated")
    else
        libPrefix(type.qualifiedName)
}


fun getFieldsProofBlock(pre:LogicElement,post:LogicElement):BlockProofElements{
    val fields =  (pre.iterate { it is Field } + post.iterate { it is Field }) as Set<Field>
    return BlockProofElements(listOf(getFieldDecls(fields), getFieldsConstraints(fields)), "; FIELDS")
}



fun getFieldDecls(fields:Set<Field>):BlockProofElements{
    setUsedHeaps(fields.map{libPrefix(it.concrType.qualifiedName)}.toSet())
    return  BlockProofElements(fields.map { FieldDecl(it.name, "ABS.StdLib.Int") }, "; fields declaration") //todo change type to Interface
}

//generation of translation for fields contraints: each field has to be unique
fun getFieldsConstraints(fields:Set<Field>) : BlockProofElements{
    val fieldsConstraints1 = mutableListOf<ProofElement>()
    fields.forEach{
        f1 -> fields.minus(f1).forEach{
            f2 -> if(f1.concrType.qualifiedName == f2.concrType.qualifiedName)fieldsConstraints1+=Assertion(Not(Eq(f1,f2)))
        }
    }
    return BlockProofElements(fieldsConstraints1, "; fields constraints")
}

fun bindToBuiltinSorts(map : Map<String,String>) : BlockProofElements{
    return BlockProofElements(map.map { DefineSortSMT(it.key, it.value, listOf())}, "; builtin types")
}

//generation of translation for primitive
fun getPrimitiveDecl():BlockProofElements{
    val valueofs = listOf(FunDecl("valueOf_ABS_StdLib_Int", listOf("ABS.StdLib.Fut"), "Int"), FunDecl("valueOf_ABS_StdLib_Bool", listOf("ABS.StdLib.Fut"), "Bool"))
    return BlockProofElements(ADTRepos.primitiveDtypesDecl.filter{!it.type.isStringType}.map{ DeclareSortSMT(it.qualifiedName)} + valueofs,"; primitive declaration")
}

fun globalIterate(pre: LogicElement,post: LogicElement) : Map<String, Set<Term>>{

    val varsList = mutableSetOf<ProgVar>()
    val heapsList = mutableSetOf<Function>()
    val funcsList = mutableSetOf<Function>()
    val genericsList = mutableSetOf<DataTypeConst>()
    val elems = pre.iterate{it is DataTypeConst || it is ProgVar || it is Function } + post.iterate{it is DataTypeConst || it is ProgVar || it is Function }

    elems.forEach{
        if(it is DataTypeConst && isConcreteGeneric(it.concrType!!)) genericsList+=it
        if(it is ProgVar && it.name != "heap" && it.name !in specialHeapKeywords) varsList+=it
        if(it is Function && it.name.startsWith("NEW")) heapsList+=it
        if(it is Function && it.name.startsWith("f_")) funcsList+=it
    }

    return mapOf("VARS" to varsList,"HEAPS" to heapsList,"FUNCS" to funcsList, "GENERICS" to genericsList)
}