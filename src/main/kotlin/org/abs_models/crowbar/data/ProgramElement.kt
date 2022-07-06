package org.abs_models.crowbar.data

import org.abs_models.frontend.typechecker.Type
import org.abs_models.frontend.typechecker.UnknownType

/**
 *  IR for ABS
 *  Essentially the same as the ABS AST, but without all the properties needed for compilation and normalized (all expressions have a target)
 */

interface ProgramElement: Anything

interface PP: ProgramElement
data class PPId(val id: Int): PP, ProgramElement {
    override fun prettyPrint(): String {
        return "pp:$id"
    }
}

data class PPAbstractVar(val name : String) : PP, AbstractVar {
    override fun prettyPrint(): String {
        return name
    }
}

interface Stmt: ProgramElement {
    fun hasReturn(): Boolean = false
}

data class StmtAbstractVar(val name : String) : Stmt, AbstractVar {
    override fun prettyPrint(): String = name
}


data class ExprStmt(val expr: Expr) : Stmt {
    override fun prettyPrint(): String = expr.prettyPrint()
}

data class AssignStmt(val lhs : Location, val rhs : Expr) : Stmt {
    override fun prettyPrint(): String {
        return lhs.prettyPrint()+" = "+rhs.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + lhs.iterate(f) + rhs.iterate(f)
}

data class AllocateStmt(val lhs : Location, val rhs : Expr) : Stmt {
    override fun prettyPrint(): String {
        return lhs.prettyPrint()+" = new "+rhs.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + lhs.iterate(f) + rhs.iterate(f)
}

data class SyncStmt(val lhs : Location, val rhs : Expr, val resolves : ConcreteStringSet, val pp : PP) : Stmt {
    override fun prettyPrint(): String {
        return lhs.prettyPrint()+" =  "+rhs.prettyPrint()+".get"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + lhs.iterate(f) + rhs.iterate(f)
}

object SkipStmt : Stmt {
    override fun prettyPrint(): String {
        return "skip"
    }
}

object ScopeMarker : Stmt {
    override fun prettyPrint() = ""
}

data class SeqStmt(val first : Stmt, val second : Stmt) : Stmt {
    override fun prettyPrint(): String {
        return first.prettyPrint()+";"+second.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + first.iterate(f) + second.iterate(f)
    override fun hasReturn(): Boolean = first.hasReturn() || second.hasReturn()
}

data class ReturnStmt(val resExpr : Expr) : Stmt {
    override fun prettyPrint(): String {
        return "return "+resExpr.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + resExpr.iterate(f)
    override fun hasReturn(): Boolean = true
}

data class IfStmt(val guard : Expr, val thenStmt : Stmt, val elseStmt : Stmt) : Stmt {
    override fun prettyPrint(): String {
        return "if( ${guard.prettyPrint()} ){ ${thenStmt.prettyPrint()} } else { ${elseStmt.prettyPrint()} }"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> =
        super.iterate(f) + guard.iterate(f) + thenStmt.iterate(f) + elseStmt.iterate(f)
    override fun hasReturn(): Boolean = thenStmt.hasReturn() || elseStmt.hasReturn()
}

data class Branch(val matchTerm : Expr, val branch : Stmt) : Anything {
    override fun prettyPrint(): String {
        return matchTerm.prettyPrint()+" => "+branch.prettyPrint()
    }

    override fun iterate(f: (Anything) -> Boolean): Set<Anything> {
        return super.iterate(f) + matchTerm.iterate(f) + branch.iterate(f)
    }
}

data class TryPushStmt(val scope: ConcreteExceptionScope) : Stmt {
    override fun prettyPrint(): String {
        return "excepPush " + scope.prettyPrint()
    }
}

data class ThrowStmt(val excep : Expr) : Stmt {
    override fun prettyPrint(): String {
        return "throw " + excep.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean): Set<Anything> {
        return super.iterate(f) + excep.iterate(f)
    }
}
data class TryPopStmt(val id : PP) : Stmt {
    override fun prettyPrint(): String = "excepPop($id)"
}
interface AbsBranchList : Anything{
    fun hasReturn(): Boolean
}

data class BranchList (val content : List<Branch>) : AbsBranchList {
    override fun prettyPrint(): String =
        content.joinToString { it.prettyPrint()}


    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> =
        content.fold(emptySet()) { acc, branch -> acc + branch.matchTerm.iterate(f) + branch.branch.iterate(f) }

    override fun hasReturn(): Boolean =
        content.fold(false) { acc, branch -> acc || branch.branch.hasReturn() }
}

data class BranchAbstractListVar(val name : String) : AbsBranchList, AbstractVar {
    override fun prettyPrint(): String = name
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = emptySet()
    override fun hasReturn(): Boolean = false
}

data class BranchStmt(val match : Expr, val branches : AbsBranchList) : Stmt {
    override fun prettyPrint(): String {
        return "case ${match.prettyPrint()}{ ${branches.prettyPrint() }}"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> =
        branches.iterate(f)

    override fun hasReturn(): Boolean =
        branches.hasReturn()
}

data class WhileStmt(val guard : Expr, val bodyStmt : Stmt, val id : PP, val invar : Formula = True) : Stmt {
    override fun prettyPrint(): String {
        return "while{${id.prettyPrint()}}( ${guard.prettyPrint()} ){ ${bodyStmt.prettyPrint()} }"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> =
        super.iterate(f) + guard.iterate(f) + bodyStmt.iterate(f) + id.iterate(f) + invar.iterate(f)
    override fun hasReturn(): Boolean = bodyStmt.hasReturn()
}

data class AwaitStmt(val resExpr : Expr, val id : PP) : Stmt {
    override fun prettyPrint(): String {
        return "await{${id.prettyPrint()}} "+resExpr.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + resExpr.iterate(f) + id.iterate(f)
}

data class CallStmt(val lhs : Location, val target : Expr, val resExpr : CallingExpr) : Stmt {
    override fun prettyPrint(): String {
        return "${lhs.prettyPrint()} = ${target.prettyPrint()}!${resExpr.prettyPrint()}"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + target.iterate(f) + resExpr.iterate(f)
}

data class SyncCallStmt(val lhs : Location, val target : Expr, val resExpr : SyncCallingExpr) : Stmt {
    override fun prettyPrint(): String {
        return "${lhs.prettyPrint()} = ${target.prettyPrint()}.${resExpr.prettyPrint()}"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + target.iterate(f) + resExpr.iterate(f)
}

data class AssertStmt(val expr : Expr) : Stmt {
    override fun prettyPrint(): String {
        return "assert ${expr.prettyPrint()}}"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + expr.iterate(f)
}

interface Expr : ProgramElement {
    var absExp: org.abs_models.frontend.ast.Exp?
}


data class ExprAbstractVar(val name : String) : Expr, AbstractVar {
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return name
    }
}

interface CallingExpr : Expr
data class CallExprAbstractVar(val name : String) : CallingExpr, AbstractVar {
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return name
    }
}

interface SyncCallingExpr : Expr
data class SyncCallExprAbstractVar(val name : String) : SyncCallingExpr, AbstractVar {
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return name
    }
}

data class CallExpr(val met : String, val e : List<Expr>) : CallingExpr{
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return met+"("+ e.joinToString(",") { p -> p.prettyPrint() } + ")"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = e.fold(super.iterate(f)) { acc, nx ->
        acc + nx.iterate(
            f
        )
    }
}

data class SyncCallExpr(val met : String, val e : List<Expr>) : SyncCallingExpr{
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return met+"("+ e.joinToString(",") { p -> p.prettyPrint() } + ")"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = e.fold(super.iterate(f)) { acc, nx ->
        acc + nx.iterate(
            f
        )
    }
}

data class PollExpr(val e1 : Expr) : Expr {
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return e1.prettyPrint()+"?"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + e1.iterate(f)
}

data class SExpr(val op : String, val e : List<Expr>) : Expr {
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        if(e.isEmpty()) return op
        return op+"("+ e.joinToString(",") { p -> p.prettyPrint() } + ")"
    }    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = e.fold(super.iterate(f)) { acc, nx ->
        acc + nx.iterate(
            f
        )
    }

}

data class ImplementsExpr(val variable : Expr, val interfaceType : Type) : Expr {
    override var absExp: org.abs_models.frontend.ast.Exp? = null
}

data class Const(val name : String, val concrType: Type? = null)  : Expr {
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return name
    }
}

data class DataTypeExpr(val name : String, val dType : String,val concrType: Type?, val e : List<Expr>)  : Expr {
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return "$name:$dType(${e.joinToString(",") { p -> p.prettyPrint() }})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = e.fold(super.iterate(f)) { acc, nx ->
        acc + nx.iterate(
            f
        )
    }
}

data class CaseExpr(val match: Expr, val expectedType:String, val content: List<BranchExpr>, val freeVars : Set<String>, val expectedTypeConcr:Type) : Expr{
    override var absExp: org.abs_models.frontend.ast.Exp? = null

    override fun prettyPrint(): String {
        return "case ${match.prettyPrint()}{\n\t${content.joinToString("\n\t") { it.prettyPrint()} }\n}"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> =
        content.fold(emptySet()) { acc, branch -> acc + branch.matchTerm.iterate(f) + branch.branch.iterate(f) }

}

data class BranchExpr(val matchTerm : Expr, val branch : Expr) {
    fun prettyPrint(): String {
        return matchTerm.prettyPrint()+" => "+branch.prettyPrint()
    }
}

interface Location : Expr
data class LocationAbstractVar(val name : String) : Location, AbstractVar{
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return name
    }
}
//name must end with _f when using automatic translation
open class Field(val name : String, val concrType :Type = UnknownType.INSTANCE) : Location, Term {

    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return "this.$name : ${concrType}"
    }
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as Field

        if (name != other.name) return false

        return true
    }

    override fun hashCode(): Int {
        return name.hashCode()
    }
    override fun toSMT(indent:String) : String = name
}

open class ProgVar(open val name: String, open val concrType: Type = UnknownType.INSTANCE) : Location, Term {

    override fun toString(): String {
        return prettyPrint()
    }
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return "$name:${concrType}"
    }

    //this ignores the type
    override fun equals(other: Any?): Boolean {
        if (this === other) return true

        if (javaClass != other?.javaClass) return false

        other as ProgVar

        if (name != other.name) return false

        return true
    }

    override fun hashCode(): Int {
        return name.hashCode()
    }
    override fun toSMT(indent:String) : String = name
}

data class Placeholder(override val name:String, override val concrType:Type) :ProgVar(name,concrType){
    override fun equals(other: Any?): Boolean {
        return super.equals(other)
    }
    override fun hashCode(): Int {
        return super.hashCode()
    }
}
data class WildCardVar(override val name:String, override val concrType:Type) :ProgVar(name,concrType){
    override fun equals(other: Any?): Boolean {
        return super.equals(other)
    }

    override fun hashCode(): Int {
        return super.hashCode()
    }
}
data class ReturnVar(override val concrType: Type) : ProgVar("result", concrType){

    override fun equals(other: Any?): Boolean {
        return super.equals(other)
    }

    override fun hashCode(): Int {
        return super.hashCode()
    }
}

fun appendStmt(stmt : Stmt, add : Stmt) : Stmt {
    return when(stmt){
        is SeqStmt -> {
            val (first, next) = stmt
            SeqStmt(first,appendStmt(next,add))
        }
        else -> SeqStmt(stmt, add)
    }
}

fun unitExpr() : Expr = SExpr("Unit", emptyList())
