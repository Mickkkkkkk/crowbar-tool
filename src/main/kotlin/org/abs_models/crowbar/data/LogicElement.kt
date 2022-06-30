package org.abs_models.crowbar.data

import org.abs_models.crowbar.interfaces.*
import org.abs_models.crowbar.main.ADTRepos
import org.abs_models.crowbar.main.FunctionRepos
import org.abs_models.crowbar.types.getReturnType
import org.abs_models.frontend.typechecker.DataTypeType
import org.abs_models.frontend.typechecker.Type


/**
 *   Standard data structures for logic, as well as the translation between terms and expressions.
 */

interface LogicElement: Anything {
    fun toSMT(indent:String="") : String //isInForm is set when a predicate is expected, this is required for the interpretation of Bool Terms as Int Terms
}
interface Formula: LogicElement
interface Term : LogicElement

val binaries = listOf(">=","<=","<",">","=","!=","+","-","*","/","&&","||")


data class FormulaAbstractVar(val name : String) : Formula, AbstractVar {
    override fun prettyPrint(): String {
        return name
    }
    override fun toSMT(indent:String) : String = name
}

data class Function(val name : String, val params : List<Term> = emptyList()) : Term {
    override fun prettyPrint(): String {
        return prettyPrintFunction(params, name)
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = params.fold(super.iterate(f)) { acc, nx ->
        acc + nx.iterate(
            f
        )
    }

    override fun toSMT(indent:String): String {

        if(name == "valueOf") {
            if(params[0] is ProgVar)
                return "(valueOf_${
                    ADTRepos.libPrefix(((params[0] as ProgVar).concrType as DataTypeType).typeArgs[0].qualifiedName).replace(".", "_")} ${(params[0] as ProgVar).name})"
            else
                throw Exception("parameter of \"valueOf\" expects Progvar or Future, actual value: ${params[0]}")
        }
        if(name == "select") {
            val field =  (params[1] as Field)
            val heapType = ADTRepos.libPrefix(
                if(field.concrType.isUnknownType)
                    throw Exception("selecting UnknownType")
                else
                    (params[1] as Field).concrType.toString())

            val fieldName = params[1].toSMT()
            return "(select ${filterHeapTypes(params[0], heapType,(params[1] as Field).concrType)} $fieldName)"
        }

        if(params.isEmpty()) {
            if(name.startsWith("-")) return "(- ${name.substring(1)})" //CVC4 requires -1 to be passed as (- 1)
            return name
        }
        val list = params.fold("") { acc, nx -> acc + " ${nx.toSMT()}" }
        if(name in FunctionRepos.parametricFunctions)
            return getSMT(FunctionRepos.concretizeNameToSMT(this), list)
        if(name in FunctionRepos.genericFunctions) {
            return ("(${FunctionRepos.genericFunctionsName(this)} $list)")
        }
        val realName = if(name == "%") "mod" else name
        return getSMT(realName, list)
    }
}

fun isGeneric(type : Type?) : Boolean = type != null && !type.isFutureType && type is DataTypeType && type.numTypeArgs() > 0
fun isConcreteGeneric(type: Type?) :Boolean = isGeneric(type) && ((type as DataTypeType).typeArgs.isEmpty() || type.typeArgs.all{ x -> !x.isTypeParameter && (!isGeneric(x) || isConcreteGeneric(x))})
fun isNotWellKnown(dataTypeConst:DataTypeConst) = dataTypeConst.concrType.toString().contains("<UNKNOWN>")
fun isUnboundGeneric(dataTypeConst:DataTypeConst) : Boolean = isGeneric(dataTypeConst.concrType) && dataTypeConst.toString().contains("Unbound Type")
fun isBoundGeneric(type : Type?) : Boolean = isGeneric(type) && !(type as DataTypeType).toString().contains("Unbound Type")

data class DataTypeConst(val name : String, val concrType: Type?, val params : List<Term> = emptyList()) : Term {

    init{
        if( name == "ABS.StdLib.Cons" && params.size < 2)
            throw Exception("too few parameters")
    }

    override fun prettyPrint(): String =
        name + ":" + concrType!!+"("+params.map { p -> p.prettyPrint() }.fold("") { acc, nx -> "$acc,$nx" }
            .removePrefix(",") + ")"

    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = params.fold(super.iterate(f)) { acc, nx ->  acc + nx.iterate(f) }

    override fun toSMT(indent:String): String {
        val back = genericSMTName(name, concrType!!)
        if(params.isEmpty())
            return back
        val list = params.fold("") { acc, nx -> acc + " ${nx.toSMT()}" }
        return "($back $list)"
    }

    fun placeholdersToSMT(): Map<Placeholder, List<String>> {
        val params = this.params
        val mapMatch = mutableMapOf <Placeholder, List<String>>()
        var count = 0;

        params.forEach {
            val functionName = "${name}_${count++}"

            when(it) {
                is Placeholder -> mapMatch[it] = listOf(functionName)
                is DataTypeConst -> it.placeholdersToSMT().forEach { mapping ->
                    mapMatch[mapping.key] = listOf(functionName) + mapping.value
                }
            }
        }
        return mapMatch
    }

    fun concreteParamsToSMT(): Map<Term, List<String>> {
        val params = this.params
        val mapMatch = mutableMapOf <Term, List<String>>()
        var count = 0;

        params.forEach {
            val functionName = "${name}_${count++}"

            when(it) {
                is DataTypeConst -> it.concreteParamsToSMT().forEach { mapping ->
                    mapMatch[mapping.key] = listOf(functionName) + mapping.value
                }
                !is Placeholder -> mapMatch[it] = listOf(functionName)

            }
        }
        return mapMatch
    }

}

fun extractPatternMatching(match: Term, branchTerm: DataTypeConst, freeVars: Set<String>): Formula {
    var countParameter = 0
    return branchTerm.params.foldRight(
        if(branchTerm.concrType!!.isBoolType)
            Eq(match, branchTerm)
        else
            Is(branchTerm.name, match)

    ) { nx, acc: Formula ->
        val parameter = Function("${branchTerm.name}_${countParameter++}", listOf(match))
        And(
            acc,
            if (nx is DataTypeConst) {
                extractPatternMatching(
                    parameter,
                    nx,
                    freeVars
                )
            } else if (nx is ProgVar && nx.name in freeVars)
                Eq(parameter, nx)
            else
                True
        )
    }
}

data class Case(val match : Term, val expectedType :String, val branches : List<BranchTerm>, val freeVars : Set<String>,val expectedTypeConcr :Type) : Term {
    private lateinit var wildCardName: String

    override fun prettyPrint(): String {
        return "case ${match.prettyPrint()}{\n\t${branches.joinToString("\n\t") { it.prettyPrint()} }\n}"
    }

    override fun toSMT(indent:String): String {

        if (branches.isNotEmpty() ){
            if(!::wildCardName.isInitialized)
                wildCardName = createWildCard(expectedType,expectedTypeConcr)
            else
                refreshWildCard(wildCardName, expectedType,expectedTypeConcr)

            val firstMatchTerm = Function(wildCardName)
            val branchTerm = branches.foldRight(firstMatchTerm as Term) { branchTerm: BranchTerm, acc: Term ->
                if(branchTerm.matchTerm is DataTypeConst && isGeneric(branchTerm.matchTerm.concrType)){
                    val matches =
                        if(match is ProgVar && match.name == "data")
                            True
                        else
                            branchTerm.matchTerm.concreteParamsToSMT().map {
                                Predicate("=", listOf(it.key, it.value.fold(match){
                                        acc: Term, s: String -> Function(s, listOf(acc))
                                }))
                    }.fold(True){accFormula: Formula, predicate: Predicate ->  And(accFormula,predicate)}

                    val map = branchTerm.matchTerm.placeholdersToSMT()
                    map.forEach{
                        ADTRepos.placeholdersMap[it.key] = it.value.fold(match){acc,nx ->
                            Function(nx, listOf(acc))
                        }
                    }
                    val newMatchSMT = And(Is(genericSMTName(branchTerm.matchTerm.name, branchTerm.matchTerm.concrType!!), match), matches)
                    var branch = branchTerm.branch
                    val placeholders = branch.iterate { it is Placeholder }
                    if(placeholders.isNotEmpty())
                        branch = replaceInTerm(branch, ADTRepos.placeholdersMap.filter { it.key in placeholders } as Map<Term,Term>)
                    Ite(newMatchSMT, branch, acc)
                }else
                {

                    val matchSMT =
                        if (branchTerm.matchTerm is DataTypeConst)
                            extractPatternMatching(match, branchTerm.matchTerm, freeVars)
                        else if (branchTerm.matchTerm is ProgVar && branchTerm.matchTerm.name in freeVars)
                            Eq(match, branchTerm.matchTerm)
                        else
                            True
                    var placeholderToBeReplaced: Set<Placeholder>
                    val branch =
                    if (branchTerm.matchTerm is DataTypeConst) {
                        placeholderToBeReplaced =  branchTerm.branch.iterate { it is Placeholder } as Set<Placeholder>
                        val mapPlaceholderToFunctions = placeholderToBeReplaced.associate {
                            Pair(it,
                                listNamesToFunction(match,
                            getFunctionForDataTypeConstElem(branchTerm.matchTerm, it)))
                        }

                        if(mapPlaceholderToFunctions.isNotEmpty())
                            replaceInTerm(branchTerm.branch, mapPlaceholderToFunctions as Map<Term, Term>)
                        else {
                            val list = getFunctionForDataTypeConstElem(branchTerm.matchTerm, branchTerm.branch)

                            if (list.isNotEmpty())
                                list.foldRight(match) { functionName: String, function: Term ->
                                    Function(functionName, listOf(function))
                                }
                            else branchTerm.branch
                        }
                    }else
                            branchTerm.branch


                    Ite(matchSMT, branch, acc)
                }
            }
            return branchTerm.toSMT()
        }else
            throw Exception("No branches")
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + match.iterate(f) + branches.fold(super.iterate(f)) { acc, nx ->
        acc + nx.iterate(
            f
        )
    }
}

data class BranchTerm(val matchTerm : Term, val branch : Term) :Term {
    override fun toSMT(indent:String): String {
        return "$indent(${matchTerm.toSMT()} ${branch.toSMT()})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + matchTerm.iterate(f) + branch.iterate(f)

}
data class UpdateOnTerm(val update : UpdateElement, val target : Term) : Term {
    override fun prettyPrint(): String {
        return "{"+update.prettyPrint()+"}"+target.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + update.iterate(f) + target.iterate(f)
    override fun toSMT(indent:String) : String = throw Exception("Updates are not translatable to Z3")
}
data class Impl(val left : Formula, val right : Formula) : Formula {
    override fun prettyPrint(): String {
        return "(${left.prettyPrint()}) -> (${right.prettyPrint()})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f) + right.iterate(f)
    override fun toSMT(indent:String) : String = "(=> ${left.toSMT()} ${right.toSMT()})"
}
data class And(val left : Formula, val right : Formula) : Formula {
    override fun prettyPrint(): String {
        if(left == True) return right.prettyPrint()
        if(right == True) return left.prettyPrint()
        return "(${left.prettyPrint()}) /\\ (${right.prettyPrint()})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f) + right.iterate(f)
    override fun toSMT(indent:String) : String = "(and ${left.toSMT()} ${right.toSMT()})"
}
data class Or(val left : Formula, val right : Formula) : Formula {
    override fun prettyPrint(): String {
        if(left == False) return right.prettyPrint()
        if(right == False) return left.prettyPrint()
        return "(${left.prettyPrint()}) \\/ (${right.prettyPrint()})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f) + right.iterate(f)
    override fun toSMT(indent:String) : String = "(or ${left.toSMT()} ${right.toSMT()})"
}
data class Not(val left : Formula) : Formula {
    override fun prettyPrint(): String {
        return "!"+left.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f)
    override fun toSMT(indent:String) : String = "(not ${left.toSMT()})"
}
class Predicate(val name : String, val params : List<Term> = emptyList()) : Formula {
    override fun prettyPrint(): String {
        return prettyPrintFunction(params, name)
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = params.fold(super.iterate(f)) { acc, nx ->
        acc + nx.iterate(
            f
        )
    }

    override fun toSMT(indent:String) : String {
        if(params.isEmpty()) return name
        val list = if(name == "=") {
            val boundTerms = boundTerms(params[0], params[1])
            val boundParam0 = boundTerms.first
            val boundParam1 = boundTerms.second
            listOf(boundParam0,boundParam1)
        } else params
        return getSMT(name, list.fold("") { acc, nx -> acc + " ${nx.toSMT()}" })
    }

    override fun equals(other: Any?): Boolean {
        return other is Predicate &&
                other.name == name &&
                other.params == params
    }

}

class Exists(elems:List<ProgVar>, formula:Formula): Quantifier("exists", elems,formula){
}

open class Quantifier(val name:String, val elems:List<ProgVar>, val formula:Formula) : Formula{
    override fun toSMT(indent: String): String {
        return  if(elems.isEmpty()) formula.toSMT()
        else "($name (${elems.joinToString(" ") { "(${it.name} ${translateType(it.concrType)})" }}) ${formula.toSMT()})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = elems.fold(super.iterate(f)) { acc, nx ->
        acc + nx.iterate(
            f
        ) + formula.iterate(f)
    }
}

data class UpdateOnFormula(val update : UpdateElement, val target : Formula) : Formula {
    override fun prettyPrint(): String {
        return "{"+update.prettyPrint()+"}"+target.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + update.iterate(f) + target.iterate(f)
    override fun toSMT(indent:String) : String = throw Exception("Updates are not translatable to Z3")
}

data class Ite(val condition :Formula, val term1 : Term, val term2 : Term) : Term{
    override fun toSMT(indent:String): String {
        return "(ite ${condition.toSMT()}" +
                "\n\t\t$indent${term1.toSMT("$indent\t")}" +
                "\n\t\t$indent${term2.toSMT("$indent\t")})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + condition.iterate(f) + term1.iterate(f)+ term2.iterate(f)
}

data class Is(val typeName : String, val term : Term) :Formula{
    override fun toSMT(indent:String): String {
        return "((_ is $typeName) ${term.toSMT()})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + term.iterate(f)
}


data class Eq(val term1: Term, val term2 : Term) : Formula{
    override fun toSMT(indent:String): String {
        return "(= ${term1.toSMT()} ${term2.toSMT()})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + term1.iterate(f)+ term2.iterate(f)
}

object True : Formula {
    override fun prettyPrint(): String {
        return "true"
    }
    override fun toSMT(indent:String) : String = "true"
}
object False : Formula {
    override fun prettyPrint(): String {
        return "false"
    }
    override fun toSMT(indent:String) : String = "false"
}

val specialHeapKeywords = mapOf(OldHeap.name to OldHeap, LastHeap.name to LastHeap)
val specialKeywordNoHeap = setOf("match")
val specialKeywords = specialHeapKeywords.keys + setOf("match")

data class HeapType(val name: String) : Type() {
    override fun copy(): Type {
        return this
    }
    override fun getSimpleName(): String {
        return name
    }

}

data class ImplementsForm(val variable : Term, val interfaceType: Type) : Formula{
    override fun toSMT(indent:String) : String = "(implements ${variable.toSMT()} ${interfaceType.qualifiedName})"
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + variable.iterate(f)
}

data class ImplementsTerm(val variable : Term, val interfaceType: Type) : Term{
    override fun toSMT(indent:String) : String = "(implements ${variable.toSMT()} ${interfaceType.qualifiedName})"
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + variable.iterate(f)
}




//constants for the special heaps and functions for futures and the theory of arrays on heaps
object Heap : ProgVar("heap",  HeapType("Heap"))
object OldHeap : ProgVar("old",  HeapType("Heap"))
object LastHeap : ProgVar("last",  HeapType("Heap"))

fun store(field: Field, value : Term) : Function = Function("store", listOf(Heap, field, value))
fun select(field : Field, heap: ProgVar = Heap) : Function = Function("select", listOf(heap, field))
fun anon(heap : Term) : Function = Function("anon", listOf(heap))
fun poll(term : Term) : Function = Function("poll", listOf(term))
fun readFut(term : Expr) : Expr = SExpr("valueOf", listOf(term))

//Translates an expression into a term. specialKeyword is the name of the used heap
fun exprToTerm(input : Expr, specialKeyword : String="NONE") : Term {
    return when(input){
        is ProgVar -> input
        is Field -> {
            if(specialKeyword != "NONE" && specialHeapKeywords.containsKey(specialKeyword))
                select(input, specialHeapKeywords[specialKeyword] as ProgVar)
            else if(specialKeyword != "NONE")
                throw Exception("The special heap keyword $specialKeyword is not supported")
            else
                select(input)
        }
        is PollExpr -> poll(exprToTerm(input.e1))
        is Const -> Function(input.name)
        is SExpr -> {
            if (specialHeapKeywords.containsKey(input.op)) {
                if (input.e.size == 1)
                    exprToTerm(input.e[0], input.op)
                else
                    throw Exception("Special keyword ${input.op} must have one argument, actual arguments size:" + input.e.size)
            }
            else
                Function(input.op, input.e.map { ex -> exprToTerm(ex, specialKeyword) })
        }
        is DataTypeExpr -> DataTypeConst(input.name, input.concrType, input.e.map { ex -> exprToTerm(ex, specialKeyword) })

        is CaseExpr -> {
            val match =exprToTerm(input.match)
            Case(match, input.expectedType, input.content.map { ex -> BranchTerm(exprToTerm(ex.matchTerm, specialKeyword), exprToTerm(ex.branch, specialKeyword)) },input.freeVars,input.expectedTypeConcr)
        }
        is ImplementsExpr -> ImplementsTerm(exprToTerm(input.variable),input.interfaceType)

        else -> throw Exception("Expression cannot be converted to term: ${input.prettyPrint()} (${input.javaClass})")
    }
}

//transates an expression of boolean type into a formula
fun exprToForm(input : Expr, specialKeyword : String="NONE") : Formula {
    if(input is SExpr && input.op == "&&" && input.e.size ==2 ) return And(exprToForm(input.e[0], specialKeyword), exprToForm(input.e[1], specialKeyword))
    if(input is SExpr && input.op == "||" && input.e.size ==2 ) return Or(exprToForm(input.e[0], specialKeyword), exprToForm(input.e[1], specialKeyword))
    if(input is SExpr && input.op == "->" && input.e.size ==2 ) return Impl(exprToForm(input.e[0], specialKeyword), exprToForm(input.e[1], specialKeyword))
    if(input is SExpr && input.op == "!" && input.e.size ==1 ) return Not(exprToForm(input.e[0]))
    if(input is SExpr && input.op == "!=") return Not(exprToForm(SExpr("=",input.e), specialKeyword))
    if(input is ImplementsExpr) return ImplementsForm(exprToTerm(input.variable), input.interfaceType)

    if(input is SExpr){
        if (specialHeapKeywords.containsKey(input.op)){//todo: fix for last
            if(input.e.size == 1) {
                return exprToForm(input.e[0], input.op)
            } else
                throw Exception("Special keywords must have one argument, actual arguments size:" + input.e.size)
        }
//        return if(input.op != "=") Predicate(input.op, input.e.map { ex -> exprToTerm(ex, specialKeyword) })
//            else{
//
//            val params = input.e.map { ex -> exprToTerm(ex, specialKeyword) }
//            val boundedTerms = boundTerms(params[0],params[1])
//                Predicate(input.op, listOf(boundedTerms.first,boundedTerms.second))
//            }
        return Predicate(input.op, input.e.map { ex -> exprToTerm(ex, specialKeyword) })
    }
    if(input is Field || input is ProgVar || input is Const)
        return exprToForm(SExpr("=",listOf(input, Const("true"))), specialKeyword)
    throw Exception("Expression cannot be converted to formula: $input")
}

//applies all updates
fun deupdatify(input: LogicElement) : LogicElement {
    return when(input){
        is UpdateOnTerm -> deupdatify(apply(input.update, input.target))
        is UpdateOnFormula -> deupdatify(apply(input.update, input.target))
        is Function -> Function(input.name, input.params.map { p -> deupdatify(p) as Term })
        is Predicate -> Predicate(input.name, input.params.map { p -> deupdatify(p) as Term })
        is Impl -> Impl(deupdatify(input.left) as Formula, deupdatify(input.right) as Formula)
        is And -> And(deupdatify(input.left) as Formula, deupdatify(input.right) as Formula)
        is Or -> Or(deupdatify(input.left) as Formula, deupdatify(input.right) as Formula)
        is Not -> Not(deupdatify(input.left) as Formula)
        else -> input
    }
}

fun replaceInFormula(input: Formula, oldPredicate: Formula, newFormula: Formula) : Formula {
    return when(input){
        is Predicate -> if (input == oldPredicate) newFormula else input
        is Impl -> Impl(replaceInFormula(input.left,oldPredicate, newFormula), replaceInFormula(input.right,oldPredicate, newFormula))
        is And -> And(replaceInFormula(input.left,oldPredicate, newFormula), replaceInFormula(input.right,oldPredicate, newFormula))
        is Or -> Or(replaceInFormula(input.left,oldPredicate, newFormula), replaceInFormula(input.right,oldPredicate, newFormula))
        is Not -> Not(replaceInFormula(input.left,oldPredicate, newFormula))
        is Exists -> Exists(input.elems, replaceInFormula(input.formula,oldPredicate,newFormula))
        else -> input
    }
}

fun replaceInLogicElement(input: LogicElement, map : Map<Term,Term>) : LogicElement{
    return if(input in map) map[input]!!
    else
    return when(input){
        is DataTypeConst -> DataTypeConst(input.name, input.concrType, input.params.map { p -> replaceInLogicElement(p, map) as Term })
        is Function -> Function(input.name, input.params.map { p -> replaceInLogicElement(p, map) as Term })
        is Predicate -> Predicate(input.name, input.params.map {
                p -> replaceInLogicElement(p, map) as Term
        })
        is Impl -> Impl(replaceInLogicElement(input.left, map) as Formula, replaceInLogicElement(input.right,map) as Formula)
        is And -> And(replaceInLogicElement(input.left,map) as Formula, replaceInLogicElement(input.right,map) as Formula)
        is Or -> Or(replaceInLogicElement(input.left,map) as Formula, replaceInLogicElement(input.right,map) as Formula)
        is Not -> Not(replaceInLogicElement(input.left,map) as Formula)
        is Ite -> Ite(replaceInLogicElement(input.condition,map) as Formula, replaceInLogicElement(input.term1,map) as Term,replaceInLogicElement(input.term2,map) as Term)
        else -> input
    }
}

fun replaceInTerm(input: Term, map : Map<Term,Term>) : Term{
    return if(input in map) map[input]!!
    else
        when(input){
            is DataTypeConst -> DataTypeConst(input.name, input.concrType, input.params.map { p -> replaceInTerm(p, map)  })
            is Function -> Function(input.name, input.params.map { p -> replaceInTerm(p, map)})
            is Ite -> Ite(replaceInLogicElement(input.condition,map) as Formula, replaceInTerm(input.term1,map),replaceInTerm(input.term2,map))
            is Case -> Case(replaceInTerm(input.match,map), input.expectedType,input.branches.map { replaceInTerm(it,map) } as List<BranchTerm>,input.freeVars,input.expectedTypeConcr)
            is BranchTerm -> BranchTerm(replaceInTerm(input.matchTerm,map),replaceInTerm(input.branch,map))
            else -> input
        }
}

fun apply(update: UpdateElement, input: LogicElement) : LogicElement {
    return when(update) {
        is EmptyUpdate -> input
        is ElementaryUpdate -> subst(input, update.lhs, update.rhs)
        is ChainUpdate -> apply(update.left, apply(update.right, input))
        else -> input
    }
}


fun subst(input: LogicElement, map: Map<LogicElement,LogicElement>) : LogicElement {
    if(map.containsKey(input)) return map.getValue(input)
    when(input){
        is EmptyUpdate -> return EmptyUpdate
        is ElementaryUpdate -> return ElementaryUpdate(input.lhs, subst(input.rhs, map) as Term)
        is ChainUpdate -> {
            if(map.keys.any { it is ProgVar && input.left.assigns(it)}) return ChainUpdate(subst(input.left, map) as UpdateElement, input.right)
            return ChainUpdate(subst(input.left, map) as UpdateElement, subst(input.right, map) as UpdateElement)
        }
        is DataTypeConst -> return DataTypeConst(input.name, input.concrType, input.params.map { p -> subst(p, map) as Term })
        is Function -> return Function(input.name, input.params.map { p -> subst(p, map) as Term })
        is Predicate -> return Predicate(input.name, input.params.map { p -> subst(p, map) as Term })
        is Impl -> return Impl(subst(input.left, map) as Formula, subst(input.right, map) as Formula)
        is And -> return And(subst(input.left, map) as Formula, subst(input.right, map) as Formula)
        is Or -> return Or(subst(input.left, map) as Formula, subst(input.right, map) as Formula)
        is Not -> return Not(subst(input.left,map) as Formula)
        is ImplementsTerm -> return ImplementsTerm(subst(input.variable, map)  as Term, input.interfaceType)
        is ImplementsForm -> return ImplementsForm(subst(input.variable, map)  as Term, input.interfaceType)
        is UpdateOnTerm -> {
            if(map.keys.any { it is ProgVar && input.update.assigns(it)}) return UpdateOnTerm(subst(input.update, map) as UpdateElement, input.target)
            return UpdateOnTerm(subst(input.update, map) as UpdateElement, subst(input.target, map) as Term)
        }
        is UpdateOnFormula -> {
            if(map.keys.any { it is ProgVar && input.update.assigns(it)}) return UpdateOnFormula(subst(input.update, map) as UpdateElement, input.target)
            return UpdateOnFormula(subst(input.update, map) as UpdateElement, subst(input.target, map) as Formula)
        }
        else -> return input
    }
}
fun subst(input: LogicElement, elem : ProgVar, term : Term) : LogicElement = subst(input, mapOf(Pair(elem,term)))


fun valueOfFunc(t : Term) = Function("valueOf", listOf(t))

fun prettyPrintFunction(params: List<Term>, name: String):String{
    if(params.isEmpty()) return name
    if(binaries.contains(name) && params.size == 2) return params[0].prettyPrint() + name + params[1].prettyPrint()
    return name+"("+params.map { p -> p.prettyPrint() }.fold("") { acc, nx -> "$acc,$nx" }.removePrefix(",") + ")"
}

fun boundGeneric(bindingType: Type, unboundTerm: Term): Term {
    if (unboundTerm is Function)
        return unboundTerm
    if (unboundTerm is ProgVar)
        return ProgVar(unboundTerm.name, bindingType)
    if (unboundTerm is Field)
        return Field(unboundTerm.name, bindingType)
    val bindingTypeHasArgs = bindingType is DataTypeType && bindingType.hasTypeArgs()
    val unboundTermHasArgs =
        unboundTerm is DataTypeConst && unboundTerm.concrType is DataTypeType && unboundTerm.concrType.hasTypeArgs()

    if (bindingTypeHasArgs != unboundTermHasArgs || (bindingType as DataTypeType).numTypeArgs() != ((unboundTerm as DataTypeConst).concrType as DataTypeType).numTypeArgs()) {
        if (bindingType.isBoundedType && unboundTerm is DataTypeConst){
            if(unboundTerm.concrType!!.isUnknownType)
                return DataTypeConst(unboundTerm.name, bindingType, unboundTerm.params)
            return unboundTerm
        }

        throw Exception("Term with unbound type \n$unboundTerm \nnot matching with binding type \n$bindingType")
    }

    val bindingTypeArgs =
        if (bindingType.simpleName != "List" && bindingType.simpleName != "Set" && bindingType.simpleName != "Map") {

            if (bindingType.numTypeArgs() < unboundTerm.params.size)
                throw Exception("Cannot bind recursive types that are not List or Set")
            bindingType.typeArgs
        } else {
            listOf(bindingType.typeArgs[0], bindingType)
        }


    return DataTypeConst(
        unboundTerm.name,
        bindingType,
        bindingTypeArgs.zip(unboundTerm.params).map<Pair<Type, Term>, Term> { boundGeneric(it.first, it.second) })
}


fun boundTerms(term1:Term, term2: Term):Pair<Term,Term>{
    var boundTerm1 = term1
    var boundTerm2 = term2

    val term1IsUnbound = term1 is DataTypeConst && isUnboundGeneric(term1)
    val term2IsUnbound = term2 is DataTypeConst && isUnboundGeneric(term2)
    val term1NotWellKnown = term1 is DataTypeConst && isNotWellKnown(term1)
    val term2NotWellKnown = term2 is DataTypeConst && isNotWellKnown(term2)

    if((term1NotWellKnown && term2NotWellKnown))
        throw Exception("Impossible to bind type: \n$boundTerm1 and \n$boundTerm2")
    val term1fullyBounded = !term1IsUnbound && !term1NotWellKnown
    val term2fullyBounded = !term2IsUnbound && !term2NotWellKnown

    if((!term1fullyBounded && !term2NotWellKnown)){
        boundTerm1 = boundGeneric(getReturnType(term2), term1)
    }else if(!term2fullyBounded ) {
        boundTerm2 = boundGeneric(getReturnType(term1), term2)
    }

    if(term1 is WildCardVar) {
        boundTerm1 = boundTerm2
    } else if(term2 is WildCardVar) {
        boundTerm2 = boundTerm1
    }

    return Pair(boundTerm1,boundTerm2)
}


fun getFunctionForDataTypeConstElem(dataTypeConst: DataTypeConst, elem : Term) : List<String>{
    var index = -1
    index = (dataTypeConst.params.indexOf(elem))
    if (index != -1) return  listOf("${dataTypeConst.name}_$index")
    else{
        for (param in dataTypeConst.params){
            index++
            if(param is DataTypeConst) {
                val innerList = getFunctionForDataTypeConstElem(param,elem)
                if(innerList.isNotEmpty())
                    return listOf("${dataTypeConst.name}_$index") + innerList
            }
        }
    }
    return listOf()

}


fun listNamesToFunction(term:Term, functionNames:List<String>): Function{
    return functionNames.foldRight(term) { functionName: String, function: Term ->
        Function(
            functionName,
            listOf(function)
        )
    } as Function
}