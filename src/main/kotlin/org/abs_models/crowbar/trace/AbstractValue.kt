/*
 TODO:
    - Change functions to work on abstract constants
    - simplifyUpdate somewhere
    - constructReverse() init?
    - I want T to be Type or something? Or the lattice to take in a Type? (from abs)
    - WHAT WILL I WORK ON? Traces has symbolic states, with updates and formulas. Hmmmmmmm, get the types right:
        I'm doing this during the SET building, so I have access to a SymNode. Then I encounter a While-statement.
        I do side computation: I generate a subtree, then generate a trace from it. I repeat, and join the traces. So
        what I want is the symbolic states and pathconditions for the states to join the traces. So what I send in to the 
        predicates is a symbolic state, which holds the path condition etc (which is in a trace state), and a Term on
        the righthand side of an Elementary Update. 
*/

package org.abs_models.crowbar.trace

import org.abs_models.crowbar.tree.*
import org.abs_models.crowbar.data.*

typealias AbstractConstant = Pair<AbstractValue, Int>

class AbstractValue(val symbol: String) {
    override fun toString(): String = "AbsVal: $symbol"
    override fun hashCode(): Int = symbol.hashCode()
    override fun equals(other: Any?): Boolean = if (other !is AbstractValue) false else symbol == other.symbol
}

/*
ASSUMPTIONS/PRECONDITIONS:
    - Correct input.
    - Structure is antitransitive.
    - Structure has no cycles (including reflexive).
    - For abstract elements x and y, and concrete element a, if pred_x(a) and pred_y(a), then pred_meet_xy(a).
*/
class AbstractLattice(
    val structure: Map<AbstractValue, List<AbstractValue>>,
    //val charFuncs: Map<AbstractValue, (Term, SymbolicState) -> LogicNode>, // assumptions from SET in ante, "predicate" in succ (like x > 1)
    val charFuncs: Map<AbstractValue, (Term) -> Formula>,
    val smallestElement: AbstractValue,
    val largestElement: AbstractValue) {

    val constId: MutableMap<AbstractValue, Int> = mutableMapOf<AbstractValue, Int>().withDefault {0}
    val reverseStructure: Map<AbstractValue, List<AbstractValue>> = constructReverse()
    fun constructReverse(): Map<AbstractValue, List<AbstractValue>> {
        val reversedMap = mutableMapOf<AbstractValue, MutableList<AbstractValue>>()
        reversedMap[smallestElement] = mutableListOf()
        for ((key, valueList) in structure) {
            for (value in valueList) {
                reversedMap.getOrPut(value) { mutableListOf() }.add(key)
            }
        }
        return reversedMap.mapValues { it.value.toList() }.toMap()
    }
    
    fun join(a1: AbstractValue, a2: AbstractValue): AbstractValue {
        var smallestSeen: AbstractValue = largestElement
        while (true) {
            val next: AbstractValue? = reverseStructure[smallestSeen]!!.firstOrNull {(parOrd(a1, it) ?: false) && (parOrd(a2, it) ?: false)}
            if (next == null) return smallestSeen
            smallestSeen = next
        }
    }

    fun meet(a1: AbstractValue, a2: AbstractValue): AbstractValue {
        var largestSeen: AbstractValue = smallestElement
        while (true) {
            val next: AbstractValue? = structure[largestSeen]!!.firstOrNull {(parOrd(it, a1) ?: false) && (parOrd(it, a2) ?: false)}
            if (next == null) return largestSeen
            largestSeen = next
        }
    }

    // Basically subset relation.
    // Two BFS after each other, first checking if there is a path from a1 to a2, then if a2 to a1.
    // If neither succeeds, a1 and a2 are not comparable
    fun parOrd(a1: AbstractValue, a2: AbstractValue): Boolean? {
        var queue: List<AbstractValue> = listOf(a1)
        var seen: MutableMap<String, Boolean> = mutableMapOf<String, Boolean>().withDefault {false} // just for early exiting

        // check a1 <= a2
        while (!queue.isEmpty()) {
            val current: AbstractValue = queue.first()
            if (current == a2) {return true} // why not work??
            seen[current.symbol] = true
            queue = queue.drop(1) + structure[current]!!
        }

        // check a2 < a1
        queue = listOf(a2)
        while (!queue.isEmpty()) {
            val current: AbstractValue = queue.first()
            if (current == a1) {return false}
            queue = queue.drop(1)
            if (!seen.getValue(current.symbol)) {queue = queue + structure[current]!!} // just short circuit
        }

        // a1 and a2 are not comparable
        return null 
    }

//    fun concreteToAbstractOld(concrete: Term): AbstractValue {
//        var smallestSeen: AbstractValue = largestElement
//        while (true) {
//            val next: AbstractValue? = reverseStructure[smallestSeen]!!.firstOrNull {charFuncs[it]!!(concrete)}
//            if (next == null) return smallestSeen
//            smallestSeen = next
//        }
//    }

    
    // We require a symbolic state to give constraints over Terms. 
    fun concreteToAbstract(concrete: Term, symState: SymbolicState): AbstractValue {
        var smallestSeen: AbstractValue = largestElement
        while (true) {
            //val next: AbstractValue? = reverseStructure[smallestSeen]!!.firstOrNull {getPredicate(it)(concrete, symState).evaluate()}
            val next: AbstractValue? = reverseStructure[smallestSeen]!!.firstOrNull {getPredicate(it)(concrete, symState).let{println(it); it.evaluate()}}
            if (next == null) return smallestSeen
            smallestSeen = next
        }
    }
    
    fun concreteToAbstractConstant(concrete: Term, symState: SymbolicState): AbstractConstant = 
        concreteToAbstract(concrete, symState).let {Pair(it, getId(it))}

    // Overflow?
    fun getId(absVal: AbstractValue): Int {
        val id = constId.getValue(absVal)
        constId[absVal] = constId.getValue(absVal) + 1
        return id
    }

    fun getPredicate(absVal: AbstractValue): (Term, SymbolicState) -> LogicNode = {t, s ->
        LogicNode(apply(s.update, s.condition) as Formula, apply(s.update, charFuncs[absVal]!!(t)) as Formula)
    }
}
