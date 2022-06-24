package org.abs_models.crowbar.tree

import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.data.Impl
import org.abs_models.crowbar.data.SymbolicState
import org.abs_models.crowbar.interfaces.evaluateSMT
import org.abs_models.crowbar.rule.containsAbstractVar

/* general interface for all kinds of nodes */
interface SymbolicTree : InfoNode{
    fun finishedExecution() : Boolean
    fun debugString(steps : Int) : String
    fun collectLeaves() : List<SymbolicLeaf>
    fun hasAbstractVar() : Boolean
    fun normalize()
    fun collectInferenceLeaves() : List<StaticNode> = this.collectLeaves().filterIsInstance<StaticNode>()
}


/* general interface for all kinds of leaves */
interface SymbolicLeaf : SymbolicTree{
    fun evaluate() : Boolean
}


data class StaticNode(val str : String) : SymbolicLeaf{
    override fun finishedExecution() : Boolean = true
    override fun debugString(steps : Int) : String = "NOT IMPLEMENTED"
    override fun collectLeaves() : List<SymbolicLeaf> = listOf(this)
    override fun evaluate() : Boolean = false
    override fun hasAbstractVar() : Boolean = false
    override fun normalize() = Unit
    override var info: NodeInfo  = NoInfo()
}

interface InfoNode {
    var info: NodeInfo
}

data class LogicNode(
    val ante: Formula,
    val succ : Formula,
    override var info: NodeInfo = NoInfo()
) : InfoNode, SymbolicLeaf{
    private var isEvaluated = false
    private var isValid = false
    override fun evaluate() : Boolean{
        if(isEvaluated) return isValid
        isValid = evaluateSMT(ante,succ)
        isEvaluated = true
        return isValid
    }

    fun toFormula() : Formula = Impl(ante, succ)

    override fun finishedExecution() : Boolean = true
    override fun debugString(steps : Int) : String = "\t".repeat(steps)+ante.prettyPrint()+" --> "+succ.prettyPrint()+"\n"
    override fun collectLeaves() : List<SymbolicLeaf> = listOf(this)
    override fun hasAbstractVar() : Boolean = containsAbstractVar(ante) || containsAbstractVar(succ)
    override fun normalize() = Unit
}

/*
We distinguish between the symbolic execution state (in the SymbolicState) and the SymbolicNode, which is a node in the proof tree.
 */
data class SymbolicNode(
    val content : SymbolicState,
    var children : List<SymbolicTree> = emptyList(),
    override var info: NodeInfo = NoInfo()
) : InfoNode, SymbolicTree{
    override fun finishedExecution() : Boolean {
        return children.isNotEmpty() && children.fold(true) { acc, nx -> acc && nx.finishedExecution() }
    }

    override fun debugString(steps : Int) : String {
        var res = "\t".repeat(steps)+content.prettyPrint()+"\n"
        for(child in children){
            res += child.debugString(steps+1)
        }
        return res
    }

    override fun hasAbstractVar() : Boolean = containsAbstractVar(content)
    override fun collectLeaves() : List<SymbolicLeaf> = children.fold(emptyList()) { acc, nx -> acc + nx.collectLeaves() }
    override fun normalize() {
        content.modality.remainder = org.abs_models.crowbar.main.normalize(content.modality.remainder)
    }
}

