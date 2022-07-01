package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.main.ADTRepos
import org.abs_models.crowbar.types.getReturnType
import org.abs_models.frontend.ast.DataTypeDecl
import org.abs_models.frontend.ast.ExceptionDecl
import org.abs_models.frontend.ast.InterfaceDecl
import org.abs_models.frontend.typechecker.DataTypeType
import org.abs_models.frontend.typechecker.InterfaceType
import org.abs_models.frontend.typechecker.Type

/*
 * This file contains the data structures for the SMT translation
 */
interface ProofElement: Anything {
    fun toSMT(indent:String="") : String //isInForm is set when a predicate is expected, this is required for the interpretation of Bool Terms as Int Terms
}


data class HeapDecl(val dtype: String) : ProofElement {

    fun name(str: String) = "${str}_${(if(dtype == "Int"){"Int"}else{dtype}).replace(".", "_")}"
    val anon :String = name("anon")
    val old :String  = name("old")
    val last :String = name("last")
    val heap :String = name("heap")
    val heapType :String = name("Heap")
    val field :String = "Field"

    override fun toSMT(indent:String): String {

        var ret = "\n; $dtype Heap declaration"
        ret += DefineSortSMT(heapType, "(Array $field ${ADTRepos.libPrefix(dtype)})").toSMT("\n")//todo: refactor hard-code
        ret += DeclareConstSMT(heap, heapType).toSMT("\n")
        ret += DeclareConstSMT(old, heapType).toSMT("\n")
        ret += DeclareConstSMT(last, heapType).toSMT("\n")
        ret += FunctionDeclSMT(anon, heapType, listOf(heapType)).toSMT("\n")
        return ret
    }
}

data class GenericTypeDecl(val dTypeDecl : DataTypeDecl, val concreteMap : Map<Type, Type>, val concreteTypes : List<Type>):
    ProofElement {

    fun getDecl() : List<Term>{
        val additionalName ="_${concreteTypes.joinToString("_") {
            if(it.qualifiedName != "Unbound Type")
                genericTypeSMTName(it)
            else "UNBOUND"}}"
        val  genericTypeName = "${dTypeDecl.qualifiedName}$additionalName"
        val valueOf  =
            FunctionDeclSMT("valueOf_${genericTypeName.replace(".", "_")}", genericTypeName, listOf("ABS.StdLib.Fut"))

        val dTypeValDecl = mutableListOf<Term>()
        for (dataConstructor in dTypeDecl.dataConstructorList) {
            var count = 0

            dTypeValDecl.add(
                ArgsSMT("${dataConstructor.qualifiedName}$additionalName",
                    dataConstructor.constructorArgList.map {
                        if (!isGeneric(it.type)) {
                            ArgsSMT(
                                "${dataConstructor.qualifiedName}_${count++}",
                                listOf(
                                    Function(
                                        if (concreteMap[it.type]!!.qualifiedName != "Unbound Type") {
                                            genericTypeSMTName(concreteMap[it.type]!!)
                                        } else "UNBOUND"
                                    )
                                )
                            )
                        } else {
                            ArgsSMT(
                                "${dataConstructor.qualifiedName}_${count++}",
                                listOf(
                                    Function(it.type.qualifiedName + "_" +
                                            (it.type as DataTypeType).typeArgs.joinToString("_") { type ->
                                                if (concreteMap[type]!!.qualifiedName != "Unbound Type") {
                                                    genericTypeSMTName(concreteMap[type]!!)
                                                } else "UNBOUND"
                                            }


                                    )
                                )
                            )

                        }
                    })
            )
        }

        val name = ArgsSMT("$genericTypeName 0")
        val declaration = ArgSMT(dTypeValDecl)
        return listOf(name, declaration, valueOf)
    }

    override fun toSMT(indent: String): String {
        val additionalName ="_${concreteTypes.joinToString("_") { 
                    if(it.qualifiedName != "Unbound Type")
                        genericTypeSMTName(it)
                    else "UNBOUND"}}"
        val  genericTypeName = "${dTypeDecl.qualifiedName}$additionalName"
        val valueOf  = "(declare-fun   valueOf_${genericTypeName.replace(".","_")} (ABS.StdLib.Fut) $genericTypeName)\n"
        val dTypeValDecl = mutableListOf<Term>()
        for (dataConstructor in dTypeDecl.dataConstructorList) {
            var count = 0
            dTypeValDecl.add(
                ArgsSMT("${dataConstructor.qualifiedName}$additionalName",
                    dataConstructor.constructorArgList.map {
                        ArgsSMT(
                            "${dataConstructor.qualifiedName}_${count++}",
                            listOf(
                                Function(
                                    if (concreteMap[it.type]!!.qualifiedName != "Unbound Type")
                                        genericTypeSMTName(concreteMap[it.type]!!)
                                    else "UNBOUND"
                                )
                            )
                        )
                    })
            )
        }
        val decl = Function(
            "declare-datatypes", (
                    listOf(
                        ArgSMT(listOf(ArgsSMT("$genericTypeName 0"))),
                        ArgSMT(listOf(ArgSMT(dTypeValDecl)))
                    ))
        )
        return decl.toSMT() + "\n$valueOf"
    }
}

data class DataTypesDecl(val dTypesDecl: List<DataTypeDecl>, val exceptionDecl: MutableList<ExceptionDecl>, val interfaceDecl: MutableList<InterfaceDecl> ) :
    ProofElement {
    override fun toSMT(indent:String): String {
        var valueOfs = ""
        if(dTypesDecl.isNotEmpty()) {
            val dTypeDecl = mutableListOf<ArgsSMT>()
            val dTypeValsDecl = mutableListOf<Term>()
            //exceptions
            dTypeDecl.add(ArgsSMT("ABS.StdLib.Exception", listOf(Function("0"))))
            val dTypeValDecl = mutableListOf<Term>()
            for(ex in exceptionDecl){
                val v = ArgsSMT(ex.qualifiedName, listOf())
                dTypeValDecl.add(v)
            }
            dTypeValsDecl.add(ArgSMT(dTypeValDecl))


            dTypeDecl.add(ArgsSMT("Interface", listOf(Function("0"))))
            val dTypeValDecl1 = mutableListOf<Term>()
            for(ex in interfaceDecl){
                val v = ArgsSMT(ex.qualifiedName, listOf())
                dTypeValDecl1.add(v)
            }
            dTypeValsDecl.add(ArgSMT(dTypeValDecl1))

            //normal data types
            for (dType in dTypesDecl) {
                valueOfs += "(declare-fun   valueOf_${dType.qualifiedName.replace(".","_")} (ABS.StdLib.Fut) ${dType.qualifiedName})\n"
                dTypeDecl.add(ArgsSMT(dType.qualifiedName, listOf(Function("0"))))
                val dTypeValDecl = mutableListOf<Term>()
                for (dataConstructor in dType.dataConstructorList) {
                    var count = 0
                    dTypeValDecl.add(
                        ArgsSMT(dataConstructor.qualifiedName,
                            dataConstructor.constructorArgList.map {
                                ArgsSMT(
                                    "${dataConstructor.qualifiedName}_${count++}",
                                    listOf(Function(ADTRepos.libPrefix(it.type.qualifiedName)))
                                )
                            })
                    )
                }
                dTypeValsDecl.add(ArgSMT(dTypeValDecl))
            }

            val decl = Function(
                "declare-datatypes", (
                        listOf(
                            ArgSMT(dTypeDecl),
                            ArgSMT(dTypeValsDecl)
                        ))
            )

            return "; DataTypes declaration\n${decl.toSMT()}\n$valueOfs"
        }
        return ""
    }
}

data class ArgsSMT(val name : String, val params : List<Term> = emptyList()) : Term {
    override fun toSMT(indent:String) : String {
        if(params.isEmpty())
            return "($name)"

        val list = params.joinToString (" "){it.toSMT()}
        return "($name $list)"
    }
}

data class ArgSMT(val params : List<Term> = emptyList()) : Term {
    override fun toSMT(indent:String): String {
        val list = params.joinToString (" "){it.toSMT()}
        return "\n\t($list)"
    }
}

data class FunctionDeclSMT(val name : String, val type: String, val params :List<String> = listOf()) : ProofElement,
    Term {
    override fun toSMT(indent:String): String {
        return "$indent(declare-fun $name (${params.joinToString(" ") {it}}) $type)"
    }
}

data class DefineSortSMT(val name :String, val type: String, val params :List<String> = listOf()): ProofElement {
    override fun toSMT(indent:String): String {
        return "$indent(define-sort $name (${params.joinToString(" ") {it}}) $type)"
    }
}

data class DeclareSortSMT(val name :String): ProofElement {
    override fun toSMT(indent:String): String {
        return "$indent(declare-sort $name 0)"
    }
}

open class DeclareConstSMT(val name :String, val type: String): ProofElement {
    override fun toSMT(indent:String): String {
        return "$indent(declare-const $name $type)"
    }
}

open class FunDecl(val name:String,val typeParams:List<String>, val type:String):ProofElement{
    override fun toSMT(indent: String): String {
        return "$indent(declare-fun $name (${typeParams.joinToString(" ")}) $type)"
    }

}

class SolverOption(val option:String):ProofElement{
    override fun toSMT(indent: String): String {
        return "$indent($option)"
    }

}

class HeapElem(function:Function) : Term {
    override fun toSMT(indent: String): String {
        TODO("Not yet implemented")
    }
}

class VarDecl(name :String, type: String) : DeclareConstSMT(name,type)

class FieldDecl(name :String, type: String) : DeclareConstSMT(name,type)

class ObjectDecl(obj :Function) : FunDecl(obj.name,obj.params.map { translateType(getReturnType(it)) }, "Int")

open class BlockProofElements(val proofElement: List<ProofElement>, val header: String, val footer:String="") :ProofElement{
    override fun toSMT(indent: String): String {
        val comment = ";"
        var block = "$indent$comment$header\n"
        block+=proofElement.joinToString("$indent\n") { it.toSMT(indent) }
        return "$block${if(footer.isNotBlank()) "\n$indent$comment$footer" else ""}"
    }
}

class EmptyProofBlock(val reason:String) : BlockProofElements(listOf(), reason)

open class Assertion(val logicElement: LogicElement) :ProofElement{
    override fun toSMT(indent: String): String {
        return "$indent(assert ${logicElement.toSMT(indent)})"
    }
}

data class ExtendsAssertion(val type1: InterfaceType, val type2:InterfaceType) : Assertion(Predicate("extends", listOf(ProofType(type1), ProofType(type2))))

data class ImplementAssertion(val term: Term, val type:Type) : Assertion(Predicate("implements", listOf(term,
    ProofType(type))))

data class ProofType(val type: Type) : Term {
    override fun toSMT(indent: String): String {
        return type.qualifiedName
    }
}

class ProofObligation(pre:Assertion, post:Assertion):BlockProofElements(listOf(pre, BlockProofElements(listOf(post), "Negated Postcondition")),"Precondition")


// Crowbar uses type-agnostic heaps internally that can store any data type
// For SMT translation, we have to use separate heaps for different types
// Therefore, we have to translate the generic heap expressions to properly
// typed ones
fun filterHeapTypes(term : Term, dtype: String, concrType: Type?=null) : String{
    val smtdType =
        if (concrType == null)
            ADTRepos.getSMTDType(dtype)
         else {
            ADTRepos.getSMTDType(genericTypeSMTName(concrType))
        }

    val concrTypeStr = concrType?.toString() ?: dtype

    if (term is Function) {
        // Remove stores that do not change the sub-heap for type dType
        if(term.name == "store") {


            if ((concrType!=null && (term.params[1] as Field).concrType == concrType))
                return "(store " +
                        "${filterHeapTypes(term.params[0], concrTypeStr, concrType)} " +
                        "${term.params[1].toSMT()} " +
                        "${term.params[2].toSMT()})"
            else
                return filterHeapTypes(term.params[0], concrTypeStr, concrType)
        // Rewrite generic anon to correctly typed anon function
        }
        else if (term.name == "anon")
            return "(${smtdType.anon} ${filterHeapTypes(term.params[0], concrTypeStr, concrType)})"
        else
            throw Exception("${term.prettyPrint()}  is neither an heap nor anon or store function")

    }
    // Rewrite generic heap variables to correctly typed sub-heap variables
    else if(term is ProgVar && term.concrType is HeapType){
        return when (term) {
            is OldHeap -> smtdType.old
            is LastHeap -> smtdType.last
            is Heap -> smtdType.heap
            else -> term.name
        }
    }
    else
        throw Exception("${term.prettyPrint()}  is neither an heap nor anon or store function")

}

fun genericTypeSMTName(type : Type) :String{
    return genericSMTName(if (!type.qualifiedName.contains(".")) type.toString() else type.qualifiedName, type)
}

fun genericSMTName(name :String, type : Type) : String =
        if(isGeneric(type))
            "${name}_${
                (type as DataTypeType).typeArgs.joinToString("_") { 
                if(it.toString() == "Unbound Type" || it.isUnknownType)
                    "UNBOUND"
                else {
                    genericTypeSMTName(it)
                }
            }}"
        else name

fun getSMT(name: String, params: String): String{
    val ret =
        when(name) {
            "!=" -> "not ${getSMT("=", params)}"
            "||" -> "or $params"
            "&&" -> "and $params"
            "!" -> "not $params"
            else -> "$name $params"
        }
    return "($ret)"
}
