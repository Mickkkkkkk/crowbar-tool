package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function

fun renderFormula(f: Formula, m: Map<String, String>): String {
    return when (f) {
        is True         -> "true"
        is False        -> "false"
        is Not          -> "!${renderFormula(f.left, m)}"
        is Or           -> "(${renderFormula(f.left, m)}) \\/ (${renderFormula(f.right, m)})"
        is And          -> "(${renderFormula(f.left, m)}) /\\ (${renderFormula(f.right, m)})"
        is Impl         -> "(${renderFormula(f.left, m)}) -> (${renderFormula(f.right, m)})"
        is Predicate    -> renderPredicate(f, m)
        is FormulaAbstractVar -> f.name
        is UpdateOnFormula -> renderFormula(apply(f.update,f.target) as Formula,m)
        else            -> throw Exception("Cannot render formula: ${f.prettyPrint()}")
    }
}

fun renderTerm(t: Term, m: Map<String, String>): String {
    return when (t) {
        is Function         -> renderFunction(t, m)
        is Field            -> "this.${t.name.substring(0, t.name.length - 2)}" // Strip _f suffix
        is ProgVar          -> if (m.containsKey(t.name)) m[t.name]!! else t.name
        is DataTypeConst    -> if (t.params.isEmpty()) t.name else "${t.name}(${
            t.params.joinToString(", ") {
                renderTerm(
                    it,
                    m
                )
            }
        })"
        is Case             -> "case(${renderTerm(t.match, m)}){ ${t.branches.joinToString("; ") { renderTerm(it, m) }} }"
        is BranchTerm       -> "${renderTerm(t.matchTerm, m)} => ${renderTerm(t.branch, m)}"
        else                -> throw Exception("Cannot render term: ${t.prettyPrint()}")
    }
}

fun renderPredicate(p: Predicate, m: Map<String, String>): String {
    return when {
        p.params.isEmpty() -> p.name
        binaries.contains(p.name) && p.params.size == 2 -> "(" + renderTerm(p.params[0], m) + p.name + renderTerm(p.params[1], m) + ")"
        else -> p.name + "(" + p.params.joinToString(", ") { t -> renderTerm(t, m) } + ")"
    }
}

fun renderFunction(f: Function, m: Map<String, String>): String {
    return when {
        f.params.isEmpty() -> f.name
        binaries.contains(f.name) && f.params.size == 2 -> "(" + renderTerm(f.params[0], m) + f.name + renderTerm(f.params[1], m) + ")"
        f.name == "select" && f.params.size == 2 && f.params[1] is Field -> renderSelect(f.params[0], f.params[1] as Field, m)
        else -> f.name + "(" + f.params.joinToString(", ") { t -> renderTerm(t, m) } + ")"
    }
}

fun renderSelect(heapTerm: Term, field: Field, m: Map<String, String>): String {
    val simpleHeapTerm = filterStores(heapTerm, field)

    return when (simpleHeapTerm) {
        is Heap, is OldHeap, is LastHeap -> renderTerm(simpleHeapTerm, m) + "." + renderTerm(field, m).substring(5) // Pretty-printing select(heapconst, this.field) as heapconst.field
        else -> "select(${renderTerm(simpleHeapTerm, m)}, ${renderTerm(field, m)})" // We'll keep a top-level select to emphasize heap access
    }
}

// Remove any store functions not relevant to the selected field or return value of matching store function
fun filterStores(heapTerm: Term, field: Field): Term {
    return if (heapTerm is Function && heapTerm.name == "store") {
        val subHeap = heapTerm.params[0]
        val storeField = heapTerm.params[1]
        val value = heapTerm.params[2]

        if (field == storeField)
            Function("store", listOf(Heap, field, value)) // replace the sub-heap term with a plain heap constant as it is irrelevant to the value
        else
            filterStores(subHeap, field)
    } else
        heapTerm
}
