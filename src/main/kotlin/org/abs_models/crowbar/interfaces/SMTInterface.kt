package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.main.ADTRepos.libPrefix
import org.abs_models.crowbar.main.ADTRepos.model
import org.abs_models.crowbar.main.ADTRepos.objects
import org.abs_models.crowbar.main.ADTRepos.setUsedHeaps
import org.abs_models.crowbar.main.FunctionRepos.concretizeFunctionTosSMT
import org.abs_models.crowbar.rule.FreshGenerator
import org.abs_models.frontend.typechecker.DataTypeType
import org.abs_models.frontend.typechecker.InterfaceType
import org.abs_models.frontend.typechecker.Type
import java.io.File
import java.util.concurrent.TimeUnit


val headerOptions = listOf(
    SolverOption("set-option :produce-models true"),
    SolverOption("set-logic ALL")
)

val mapBuiltinTypeSMT = mapOf(
    "ABS.StdLib.Int" to "Int",
    "ABS.StdLib.Float" to "Real",
    "ABS.StdLib.Bool" to "Bool",
    "ABS.StdLib.String" to "String",
    "Field" to "Int",
    "Interface" to "Int"
)

val mapBuiltinFunction = mapOf(
    "valueOf_Int" to Pair(listOf("Int"), "Int"),
    "hasRole" to Pair(listOf("Int", "String"), "Bool"),
    "implements" to Pair(listOf("ABS.StdLib.Int", "Interface"), "Bool"),
    "extends" to Pair(listOf("Interface", "Interface"), "Bool")
)

val staticAssertions = listOf(
    Eq(Function("Unit"),Function("0")),
    extendsProperty(),
    implementsProperty()
)

@Suppress("UNCHECKED_CAST")
fun generateSMT(ante : Formula, succ: Formula, modelCmd: String = "") : String {
    resetWildCards()
    val headerBlock = getStaticHeader()

    // application of updates to generate pre- and post-condition
    var  pre = deupdatify(ante)
    val post = deupdatify(succ)

    val globaliterate = globalIterate(pre,post)
    val unusedPlaceholders = globaliterate["UNUSED_PLACEHOLDERS"] as Set<Placeholder>
    val pairNewPreAndWildcards = replaceUnusedPlaceholdersWithWildcards(pre,unusedPlaceholders)
    pre = pairNewPreAndWildcards.first
    globaliterate["VARS"] = (globaliterate["VARS"] as Set<ProgVar>).plus(pairNewPreAndWildcards.second)
    globaliterate["VARS"] = (globaliterate["VARS"] as Set<ProgVar>).minus(unusedPlaceholders)

    val fieldsProofBlock = getFieldsProofBlock(globaliterate["FIELDS"] as Set<Field>)
    val varsProofBlock = getVarsProofBlock(globaliterate["VARS"] as Set<ProgVar>)

    // generation of the generics occurring in pre and post condition
    globaliterate["GENERICS"]!!.map {
        ADTRepos.addGeneric((it as DataTypeConst).concrType!! as DataTypeType) }

    val heaps =  globaliterate["HEAPS"]!! as Set<Function>
    val funcs =  globaliterate["FUNCS"]!! as Set<Function>

    val allFunctionsDecls = FunctionRepos.getCalledFunctionsNotInPO(funcs)

    val proofObligation = ProofObligation(Assertion(pre as Formula), Assertion(Not(post as Formula)))
    val proofObligationSMT =  proofObligation.toSMT("\t")
    val functionDecl = BlockProofElements(listOf(allFunctionsDecls.first, allFunctionsDecls.second),"FUNCTIONS").toSMT("\t")
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
      ${interfaceExtends().toSMT("\t")}
      
;generics declaration
    ${ADTRepos.genericsToSMT()}
;heaps declaration
    ${getHeapsDeclaration().toSMT("\t")}
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
fun translateType(type:Type, asReturnType :Boolean=false) : String{
    return if(type.isUnknownType)
        throw Exception("Unknown Type Cannot be Translated")
    else if (isGeneric(type)) {
        ADTRepos.addGeneric(type as DataTypeType)
        genericTypeSMTName(type)
    }else if(type.isTypeParameter) {
        println()
        throw Exception("Parameter Type Cannot Be Translated")
    }
    else if(type.isInterfaceType && asReturnType)
        "Interface"
    else if(type.isReferenceType && asReturnType)
        "Object"
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
        decls+=VarDecl(it.name, translateType(it.concrType, true))
        if(it.concrType is InterfaceType)
            implementsAssertions+=ImplementAssertion(it,it.concrType)
    }
    return BlockProofElements(decls + BlockProofElements(implementsAssertions, "Implement Assertions"), "Variable Declaration", "End Variable Declaration")
}


fun getFieldDecls(fields:Set<Field>):BlockProofElements{
    setUsedHeaps(fields.map{translateType(it.concrType)}.toSet())
    return  BlockProofElements(fields.map { FieldDecl(it.name, "Field") }, "Fields Declaration")
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

fun bindToBuiltinSorts(): BlockProofElements{
    return BlockProofElements(mapBuiltinTypeSMT.map { DefineSortSMT(it.key, it.value, listOf())}, "Builtin Types")
}

fun builtinFunctions(): BlockProofElements{
    return BlockProofElements(mapBuiltinFunction.map { FunDecl(it.key, it.value.first, it.value.second)}, "Builtin Functions")
}

//generation of translation for primitive
fun getPrimitiveDecl():BlockProofElements{
    val valueofs = listOf(FunDecl("valueOf_ABS_StdLib_Int", listOf("ABS.StdLib.Fut"), "Int"), FunDecl("valueOf_ABS_StdLib_Bool", listOf("ABS.StdLib.Fut"), "Bool"))
    return BlockProofElements(ADTRepos.primitiveDtypesDecl.filter{!it.type.isStringType}.map{ DeclareSortSMT(it.qualifiedName)} + valueofs,"Primitive Declaration")
}

fun globalIterate(pre: LogicElement,post: LogicElement) : MutableMap<String, Set<Anything>>{

    val varsSet = mutableSetOf<ProgVar>()
    val heapsSet = mutableSetOf<Function>()
    val funcsSet = mutableSetOf<Function>()
    val genericsSet = mutableSetOf<DataTypeConst>()
    val placeholdersPre = mutableSetOf<Placeholder>()
    val placeholdersPost = mutableSetOf<Placeholder>()
    val fieldsSet =  mutableSetOf<Field>()

    val cond = { it:Anything -> it is DataTypeConst || it is ProgVar || it is Function || it is Predicate || it is Field }
    val elemsPre = pre.iterate{cond(it)}
    val elemsPost = post.iterate{cond(it)}

    elemsPre.forEach{
        if(it is DataTypeConst && isConcreteGeneric(it.concrType!!)) genericsSet+=it
        if(it is ProgVar && it.name != "heap" && it.name !in specialHeapKeywords) varsSet+=it
        if(it is Function && it.name.startsWith("NEW")) heapsSet+=it
        else if(it is Function ) funcsSet+=it
        if(it is Placeholder) placeholdersPre += it
        if(it is Field) fieldsSet+=it
    }

    elemsPost.forEach{
        if(it is DataTypeConst && isConcreteGeneric(it.concrType!!)) genericsSet+=it
        if(it is ProgVar && it.name != "heap" && it.name !in specialHeapKeywords) varsSet+=it
        if(it is Function && it.name.startsWith("NEW")) heapsSet+=it
        else if(it is Function ) funcsSet+=it
        if(it is Placeholder) placeholdersPost += it
        if(it is Field) fieldsSet+=it
    }

    return mutableMapOf(
        "VARS" to varsSet,
        "HEAPS" to heapsSet,
        "FUNCS" to funcsSet,
        "GENERICS" to genericsSet,
        "UNUSED_PLACEHOLDERS" to placeholdersPre.minus(placeholdersPost),
        "FIELDS" to fieldsSet
    )
}

fun replaceUnusedPlaceholdersWithWildcards(pre: LogicElement, unusedPlaceholders: Set<Placeholder>): Pair<LogicElement,Set<WildCardVar>> {
    val newPre = pre
    val newWildCards = mutableSetOf<WildCardVar>()
    val placeholders = unusedPlaceholders.associate {
            val wildCardVar = FreshGenerator.getFreshWildCard(it.concrType)
            newWildCards.add(wildCardVar)
            Pair(it as Term, wildCardVar as Term)
     }

    return Pair(replaceInLogicElement(newPre, placeholders), newWildCards)
}

/**
 * @return block of proof for static header
 */
fun getStaticHeader():BlockProofElements{
    return BlockProofElements(
        listOf(
            BlockProofElements(headerOptions,"SOLVER OPTIONS"),
            bindToBuiltinSorts(),
            builtinFunctions(),
            DeclareConstSMT("Unit", "Int"),
            DeclareSortSMT("UNBOUND"))
                + staticAssertions.map { Assertion(it) }
                + getPrimitiveDecl(),
        "Header",
        "End Header")
}

/**
 * @return block of proof containing set of assertions for the interface extension property
 */
fun interfaceExtends() : BlockProofElements {
    val assertions = mutableListOf<Assertion>()
    ADTRepos.interfaceDecl.forEach { i1 ->
        i1.extendedInterfaceUseListNoTransform.forEach { i2 ->
            assertions+=ExtendsAssertion(i1.type as InterfaceType, i2.type as InterfaceType)
        }
    }
    return BlockProofElements(assertions, "Interface Extensions Assertions")
}

/**
 * @return block of proof corresponding to heap declaration
 */
fun getHeapsDeclaration() :BlockProofElements{
    val heaps = mutableListOf<BlockProofElements>()
    for (dtype in ADTRepos.dtypeMap) {
        heaps +=
            if(!conciseProofs || dtype.key in ADTRepos.usedHeaps)
                BlockProofElements(listOf(dtype.value), "Heap declaration for type ${dtype.key}")
            else
                EmptyProofBlock("\n; no fields of type ${dtype.key}: omitting declaration of ${dtype.value.heapType}")
    }
    return BlockProofElements(heaps, "HEAPS DECLARATION", "END HEAPS DECLARATION")
}

/**
 * @return the transitive property for interface extension
 */
fun extendsProperty() :LogicElement{
    val i1 = ProgVar("i1", model!!.intType)
    val i2 = ProgVar("i2", model!!.intType)
    val i3 = ProgVar("i3", model!!.intType)
    val property = "extends"
    return Forall(
        listOf(i1,i2,i3),
        Impl(
            And(
                Predicate(property, listOf(i1,i2)),
                Predicate(property, listOf(i2,i3))
            ),
            Predicate(property, listOf(i1,i3))
        )
    )
}

/**
 * @return the LogicElement corresponding to the inference of implements property
 */
fun implementsProperty() :LogicElement{
    val i1 = ProgVar("i1", model!!.intType)
    val i2 = ProgVar("i2", model!!.intType)
    val obj = ProgVar("obj", model!!.intType)
    return Forall(
        listOf(i1,i2,obj),
        Impl(
            And(
                Predicate("extends", listOf(i1,i2)),
                Predicate("implements", listOf(obj,i1))
            ),
            Predicate("implements", listOf(obj,i2))
        )
    )
}