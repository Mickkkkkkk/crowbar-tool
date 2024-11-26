package org.abs_models.crowbar.data

/**
 *  Data structures for updates
 */

interface UpdateElement: LogicElement {
    fun assigns(v : ProgVar) : Boolean
    override fun toSMT(indent:String) : String = throw Exception("Updates are not translatable to SMT-LIB")
}
object EmptyUpdate : UpdateElement {
    override fun prettyPrint(): String ="empty"
    override fun assigns(v : ProgVar) : Boolean = false
}
data class ChainUpdate(val left : UpdateElement, val right: UpdateElement) : UpdateElement {
    override fun prettyPrint(): String = left.prettyPrint()+ "}{"+right.prettyPrint()
    override fun assigns(v : ProgVar) : Boolean = left.assigns(v) || right.assigns(v)
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f) + right.iterate(f)
}
data class ElementaryUpdate(val lhs : ProgVar, val rhs : Term) : UpdateElement {
    override fun prettyPrint(): String = lhs.prettyPrint() + " := "+rhs.prettyPrint()
    override fun assigns(v : ProgVar) : Boolean = lhs == v
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + lhs.iterate(f) + rhs.iterate(f)
}


// Normalizing to easier remove ElementaryUpdates. 
// Nomalized here means no ChainUpdates on the left-hand side of a ChainUpdate.
// Essentially end up with a linked-list structure. This is fine as the tree structure
// of ChainUpdates have no semantics other than the sequence of the "leafs"
fun normalizeUpdate(updt : UpdateElement) : UpdateElement =
    when(updt) {
        is ChainUpdate ->
            when(updt.left){
                is ChainUpdate -> normalizeUpdate(ChainUpdate(updt.left.left, ChainUpdate(updt.left.right,updt.right)))
                else -> ChainUpdate(updt.left, normalizeUpdate(updt.right))
            }
        else -> updt
    }
fun removeDuplicateElementaryFromNormalized(updt: UpdateElement) : UpdateElement = 
    when (updt) {
        is ChainUpdate -> {
            if (updt.left is ElementaryUpdate && updt.right.assigns(updt.left.lhs))
            removeDuplicateElementaryFromNormalized(apply(updt.left, updt.right) as UpdateElement)
            else ChainUpdate(updt.left, removeDuplicateElementaryFromNormalized(updt.right))
        }
        else -> updt
    }
fun simplifyUpdate(updt: UpdateElement) : UpdateElement = removeDuplicateElementaryFromNormalized(normalizeUpdate(updt))

fun getBetterAtTesting(): UpdateElement {
    val updt1: UpdateElement = ChainUpdate(
            ChainUpdate(
                ElementaryUpdate(ProgVar("x"), exprToTerm((Const("a"))))
                , ElementaryUpdate(ProgVar("y"), ProgVar("x"))
            )
            , ElementaryUpdate(ProgVar("x"), exprToTerm((Const("c"))))
    )
    val updt2: UpdateElement = ChainUpdate(
            ChainUpdate(
                ElementaryUpdate(ProgVar("x"), exprToTerm((Const("a"))))
                , ElementaryUpdate(ProgVar("x"), exprToTerm(Const("b")))
            )
            , ElementaryUpdate(ProgVar("y"), (ProgVar("x")))
    ) 
    val updt3: UpdateElement = ChainUpdate(
            ChainUpdate(
                ElementaryUpdate(ProgVar("x"), exprToTerm((Const("a"))))
                , ElementaryUpdate(ProgVar("x"), ProgVar("x"))
            )
            , ElementaryUpdate(ProgVar("y"), (ProgVar("x")))
    ) 

    println("\nSimplify: {x:=a}{y:=x}{x:=c}:{${simplifyUpdate(updt1).prettyPrint()}}")
    println("\nSimplify: {x:=a}{x:=b}{y:=x}:{${simplifyUpdate(updt2).prettyPrint()}}")
    println("\nSimplify: {x:=a}{x:=x}{y:=x}:{${simplifyUpdate(updt3).prettyPrint()}}")

    return updt1
}