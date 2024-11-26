package org.abs_models.crowbar.trace
import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.tree.*

// should this implement Anything?
interface TraceElement

/*      ***************** EVENTS *****************      */
interface Event : TraceElement

//val call: CallStmt/CallingExpr
//data class CallEvent (val func: String, val param: List<(String, String)>, val Int callID = 0) : Event
data class SyncCallEvent (val callEx : SyncCallingExpr) : Event {
    override fun toString(): String = "Sync call: " + callEx.prettyPrint()
}
data class CallEvent (val callEx : CallingExpr) : Event {
    override fun toString(): String = "Call: " + callEx.prettyPrint()
}
data class AbstractSyncCallEvent (val callEx : SyncCallExprAbstractVar) : Event {
    override fun toString(): String = "Sync abstract call: " + callEx.prettyPrint()

}
data class AbstractCallEvent (val callEx : CallExprAbstractVar) : Event {
    override fun toString(): String = "Abstract call: " + callEx.prettyPrint()
}

data class ReturnEvent (val ret: ReturnStmt) : Event {
    override fun toString(): String = "return: " + ret.resExpr.prettyPrint()
}

//data class PrintEvent (val printed: String) : Event
/*      *************** EVENTS END ***************      */

data class TraceState (val state: SymbolicState) : TraceElement {
    override fun toString(): String = /* state.condition.prettyPrint() + "\n\t   | " + */  state.update.prettyPrint()
}

data class Trace (var traceSequence: List<TraceElement> = emptyList()) {
    fun pushTraceElement(e: TraceElement) {
        when (e) {
            //is EmptyTrace -> Unit
            else -> traceSequence = listOf(e) + traceSequence
        }
    }
    //fun lastEvent() : Event? = Unit
    //fun currentState() : TraceState? = Unit
    override fun toString(): String = traceSequence.fold("\nTrace:") {acc, elem -> acc + "\n\t-> " + elem.toString()}
}

fun concatTraces(vararg traces: Trace) : Trace = 
    traces.fold(Trace()) {acc, next -> Trace(acc.traceSequence + next.traceSequence)}

// Recieves an executed (check for this?) symbolic tree, and recursively builds the traces.
// TODO: refactor this please it's really bad, but just accept it for now, it runs.
fun constructTraces (node: SymbolicTree) : List<Trace> = when (node) {
    is SymbolicNode -> constructTraces(node, SkipStmt).map {concatTraces(Trace(listOf(TraceState(node.content))), it)}
    else -> listOf(Trace())
}

// Since SESs record the state after a statement has been executed,
// we pass the statement and the symbolic node which follows.
// As the proof tree and the SET is one and the same, we have to 
// filter out logicNodes when doing recursion.
fun constructTraces (node: SymbolicNode, prevStmt:Stmt) : List<Trace> {
    val symbolicChildren: List<SymbolicNode> = node.children.filterIsInstance<SymbolicNode>()
    val currentStatement : Stmt = node.content.modality.remainder
    return if (symbolicChildren.isEmpty()) { 
        when (currentStatement) {
            is ReturnStmt -> listOf(concatTraces(symbolicNodeToTrace(node, prevStmt), Trace(listOf(ReturnEvent(currentStatement)))))
            is SkipStmt -> listOf(Trace(listOf(TraceState(node.content)))) // idk, i miss monads
            else -> listOf(Trace()) // shouldn't happen? 
        }
    } else {
        symbolicChildren.flatMap {
            constructTraces(it, currentStatement).map {
                concatTraces(symbolicNodeToTrace(node, prevStmt), it)
            }
        }
    }
}

// small-step?
fun symbolicNodeToTrace(node: SymbolicNode, prevStmt: ProgramElement) : Trace {
    // case on Stmt type
    return when (prevStmt) {
        is SeqStmt -> symbolicNodeToTrace(node, prevStmt.first)
        is AssignStmt, is AllocateStmt -> Trace(listOf(TraceState(node.content))) // difference??
        is ReturnStmt -> Trace(listOf(ReturnEvent(prevStmt)))
        // I guess in the trace semantics it says just call(...,id)*K(x = res_id), so its right as is?
        is CallStmt -> 
            concatTraces(Trace(listOf(CallEvent(prevStmt.resExpr))), Trace(listOf(TraceState(node.content))))
        is SyncCallStmt ->
            concatTraces(Trace(listOf(SyncCallEvent(prevStmt.resExpr))), Trace(listOf(TraceState(node.content))))
        //is CallExpr -> Trace(listOf(CallEvent(prevProgElm)))
        //is SyncCallExpr -> Trace(listOf(SyncCallEvent(prevProgElm)))
        //is SyncCallExprAbstractVar -> 
        //is CallExprAbstractVar -> Trace(listOf(CallEvent())
        else -> Trace()
    }
}

/* UNUSED:
// TODO: Scrap for something else?
object EmptyTrace : TraceElement {
    override fun toString(): String = "ε"
}

IDEAS: - represent traces as trees instead, to share prefixes? Isn't that just the symbolic tree? no, a little different.
         might be fine later down the line.
       - deupdatify the states?
*/