package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.main.ADTRepos.libPrefix
import org.abs_models.crowbar.main.ADTRepos.objects
import org.abs_models.crowbar.main.ADTRepos.setUsedHeaps
import org.abs_models.crowbar.main.FunctionRepos.concretizeFunctionTosSMT
import org.abs_models.frontend.typechecker.DataTypeType
import org.abs_models.frontend.typechecker.InterfaceType
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
    val headerBlock = getStaticHeader()

    // application of updates to generate pre- and post-condition
    var  pre = deupdatify(ante)
    var post = deupdatify(succ)

    val globaliterate = globalIterate(pre,post)

    val fieldsProofBlock = getFieldsProofBlock(globaliterate["FIELDS"] as Set<Field>)
    val varsProofBlock = getVarsProofBlock(globaliterate["VARS"] as Set<ProgVar>)

    val newContract = replacePredicateContainingPlaceholders(pre, post, globaliterate)
    pre = newContract.first
    post = newContract.second

    // generation of the generics occurring in pre and post condition
    globaliterate["GENERICS"]!!.map {
        ADTRepos.addGeneric((it as DataTypeConst).concrType!! as DataTypeType) }

    val heaps =  globaliterate["HEAPS"]!! as Set<Function>
    val funcs =  globaliterate["FUNCS"]!! as Set<Function>

    val proofObligation = ProofObligation(Assertion(pre as Formula), Assertion(Not(post as Formula)))
    val proofObligationSMT =  proofObligation.toSMT("\t")
    val functionDecl = FunctionRepos.toString()
    val concretizeFunctionTosSMT= concretizeFunctionTosSMT()

    //generation of translation for wildcards
    val wildcards: String = wildCardsConst.map { FunctionDeclSMT(it.key,it.value).toSMT("\n\t") }.joinToString("") { it }


    //generation of translation for object "implements" assertions
    val objectImpl = getObjectsDecls(heaps).toSMT()

    return """
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
${varsProofBlock.toSMT("\t")}
$objectImpl

$proofObligationSMT
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


fun getFieldsProofBlock(fields:Set<Field>):BlockProofElements{
    return BlockProofElements(listOf(getFieldDecls(fields), getFieldsConstraints(fields)), "FIELDS BLOCK","END FIELDS")
}
//generation of translation for variable declarations
fun getVarsProofBlock(vars:Set<ProgVar>) : BlockProofElements{
    val decls = mutableListOf<VarDecl>()
    val implementsAssertions = mutableListOf<Assertion>()
    vars.forEach {
        decls+=VarDecl(it.name, translateType(it.concrType))
        if(it.concrType is InterfaceType)
            implementsAssertions+=ImplementAssertion(it,it.concrType)
    }
    return BlockProofElements(decls + BlockProofElements(implementsAssertions, "Implement Assertions"), "Variable Declaration", "End Variable Declaration")
}


fun getFieldDecls(fields:Set<Field>):BlockProofElements{
    setUsedHeaps(fields.map{libPrefix(it.concrType.qualifiedName)}.toSet())
    return  BlockProofElements(fields.map { FieldDecl(it.name, "ABS.StdLib.Int") }, "Fields Declaration") //todo change type to Interface
}

//generation of translation for fields contraints: each field has to be unique
fun getFieldsConstraints(fields:Set<Field>) : BlockProofElements{
    val fieldsConstraints1 = mutableListOf<ProofElement>()
    fields.forEach{
        f1 -> fields.minus(f1).forEach{
            f2 -> if(f1.concrType.qualifiedName == f2.concrType.qualifiedName)fieldsConstraints1+=Assertion(Not(Eq(f1,f2)))
        }
    }
    return BlockProofElements(fieldsConstraints1, "Fields Constraints")
}

fun getObjectsDecls(objectsSet:Set<Function>):BlockProofElements{
    val objectDecls = mutableListOf<ObjectDecl>()
    val objectImplAssertion = mutableListOf<ImplementAssertion>()

    objectsSet.forEach {
        objectDecls+=ObjectDecl(it)
        if(it.name in objects )
            objects[it.name]!!.types.forEach{ type -> objectImplAssertion+=ImplementAssertion(it,type) }
    }

    return  BlockProofElements( listOf(
        BlockProofElements(objectDecls, "Object Declarations")) +
        BlockProofElements(objectImplAssertion, "Interface Implementation Assertions"),
        "OBJECTS",
        "END OBJECTS") //todo change type to Interface
}

fun bindToBuiltinSorts(map : Map<String,String>) : BlockProofElements{
    return BlockProofElements(map.map { DefineSortSMT(it.key, it.value, listOf())}, "Builtin Types")
}

//generation of translation for primitive
fun getPrimitiveDecl():BlockProofElements{
    val valueofs = listOf(FunDecl("valueOf_ABS_StdLib_Int", listOf("ABS.StdLib.Fut"), "Int"), FunDecl("valueOf_ABS_StdLib_Bool", listOf("ABS.StdLib.Fut"), "Bool"))
    return BlockProofElements(ADTRepos.primitiveDtypesDecl.filter{!it.type.isStringType}.map{ DeclareSortSMT(it.qualifiedName)} + valueofs,"Primitive Declaration")
}

fun globalIterate(pre: LogicElement,post: LogicElement) : Map<String, Set<Anything>>{

    val varsSet = mutableSetOf<ProgVar>()
    val heapsSet = mutableSetOf<Function>()
    val funcsSet = mutableSetOf<Function>()
    val genericsSet = mutableSetOf<DataTypeConst>()
    val predicatePre = mutableSetOf<Predicate>()
    val predicatePost = mutableSetOf<Predicate>()
    val placeholdersPre = mutableSetOf<Placeholder>()
    val placeholdersPost = mutableSetOf<Placeholder>()
    val fieldsSet =  mutableSetOf<Field>()

    val elemsPre = pre.iterate{it is DataTypeConst || it is ProgVar || it is Function || it is Predicate || it is Field}
    val elemsPost = post.iterate{it is DataTypeConst || it is ProgVar || it is Function || it is Predicate || it is Field}

    elemsPre.forEach{
        if(it is DataTypeConst && isConcreteGeneric(it.concrType!!)) genericsSet+=it
        if(it is ProgVar && it.name != "heap" && it.name !in specialHeapKeywords) varsSet+=it
        if(it is Function && it.name.startsWith("NEW")) heapsSet+=it
        else if(it is Function ) funcsSet+=it
        if(it is Predicate) predicatePre+=it
        if(it is Placeholder) {
            placeholdersPre += it
            varsSet+=ProgVar("${it.name}_${it.concrType}", it.concrType)
        }
        if(it is Field) fieldsSet+=it
    }

    elemsPost.forEach{
        if(it is DataTypeConst && isConcreteGeneric(it.concrType!!)) genericsSet+=it
        if(it is ProgVar && it.name != "heap" && it.name !in specialHeapKeywords) varsSet+=it
        if(it is Function && it.name.startsWith("NEW")) heapsSet+=it
        else if(it is Function ) funcsSet+=it
        if(it is Predicate) predicatePost+=it
        if(it is Placeholder) {
            placeholdersPost += it
            varsSet+=ProgVar("${it.name}_${it.concrType}", it.concrType)
        }
        if(it is Field) fieldsSet+=it
    }

    return mapOf(
        "VARS" to varsSet,
        "HEAPS" to heapsSet,
        "FUNCS" to funcsSet,
        "GENERICS" to genericsSet,
        "PREDICATES_PRE" to predicatePre,
        "PREDICATES_POST" to predicatePost,
        "PLACEHOLDERS_PRE" to placeholdersPre,
        "PLACEHOLDERS_POST" to placeholdersPost,
        "FIELDS" to fieldsSet
    )
}

fun replacePredicateContainingPlaceholders(pre: LogicElement, post: LogicElement, globalIterate:Map<String, Set<Anything>>): Pair<LogicElement, LogicElement> {
    var newPre = pre
    var newPost = post
    val predicatePre = globalIterate["PREDICATES_PRE"] as Set<Predicate>
    val predicatePost = globalIterate["PREDICATES_POST"] as Set<Predicate>
    val prePlaceholders = globalIterate["PLACEHOLDERS_PRE"] as Set<Placeholder>
    val postPlaceholders = globalIterate["PLACEHOLDERS_POST"] as Set<Placeholder>
    val placeholders = prePlaceholders.intersect(postPlaceholders)

    // replacing placeholders in precondition
    predicatePre.map {
            oldPredicate ->
        var newFormula= (oldPredicate.iterate { el -> el is Placeholder && el in placeholders } as Set<Placeholder>).fold(oldPredicate) {
                acc:Formula, ph : Placeholder->
            And(acc, Predicate("=", listOf(ph, ProgVar("${ph.name}_${ph.concrType}", ph.concrType))))
        }
        val wildcards = oldPredicate.iterate { it is WildCardVar || it is Placeholder } as Set<ProgVar>
            newFormula = Exists(wildcards.toList(), newFormula)
            newPre = replaceInFormula(newPre as Formula, oldPredicate, newFormula)
    }

    // replacing placeholders in postcondition
    predicatePost.map {
            oldPredicate ->
        if(postPlaceholders.isNotEmpty()) {
            postPlaceholders.map {
                val globalPh= ProgVar("${it.name}_${it.concrType}", it.concrType)
                val newFormula = replaceInLogicElement(oldPredicate as Predicate, mapOf(Pair(it, globalPh))) as Predicate
                newPost = replaceInFormula(newPost as Formula, oldPredicate, newFormula)
            }
        }
    }
    return Pair(newPre,newPost)
}

fun getStaticHeader():BlockProofElements{
    return BlockProofElements(
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
        "Header",
        "End Header")
}