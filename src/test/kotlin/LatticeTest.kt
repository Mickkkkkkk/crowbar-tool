import io.kotlintest.shouldBe
import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.trace.*
import org.abs_models.crowbar.tree.*
import org.abs_models.crowbar.types.*
import org.abs_models.crowbar.main.*

class LatticeTest : CrowbarTest() {
    init {
        val intStrct: Map<AbstractValue, List<AbstractValue>> = mapOf(
            AbstractValue("⊥") to listOf(AbstractValue("pos"), AbstractValue("neg"), AbstractValue("zero"))
            , AbstractValue("zero") to listOf(AbstractValue(">="), AbstractValue("<="))
            , AbstractValue("pos") to listOf(AbstractValue(">="))
            , AbstractValue("neg") to listOf(AbstractValue("<="))
            , AbstractValue(">=") to listOf(AbstractValue("T"))
            , AbstractValue("<=") to listOf(AbstractValue("T"))
            , AbstractValue("T") to listOf()
        )
        val intPreds: Map<AbstractValue, (Term) -> Formula> = mapOf(
            AbstractValue("⊥") to { _ -> False}
            , AbstractValue("zero") to { term -> Predicate("=", listOf(term, Function("0"))) }
            , AbstractValue("pos") to { term -> Predicate(">", listOf(term, Function("0"))) }
            , AbstractValue("neg") to { term -> Predicate("<", listOf(term, Function("0"))) }
            , AbstractValue(">=") to { term -> Predicate(">=", listOf(term, Function("0"))) }
            , AbstractValue("<=") to { term -> Predicate("<=", listOf(term, Function("0"))) }
            , AbstractValue("T") to { _ -> True }
        )
        val intSmol: AbstractValue = AbstractValue("⊥")
        val intBeeg: AbstractValue = AbstractValue("T")
        val intLattis: AbstractLattice = AbstractLattice(intStrct, intPreds, intSmol, intBeeg)
        val exampleSymState = SymbolicState(True, ElementaryUpdate(ProgVar("x"), Function("1")), Modality(SkipStmt, LocalTypeTarget(LTSkip, True)), listOf())

        "partial order" {
            fun answer(a: AbstractValue, b: AbstractValue): Boolean? = when (a.symbol) {
                "⊥" -> true
                "zero" -> when (b.symbol) {
                    "⊥" -> false
                    "pos", "neg" -> null
                    else -> true
                }
                "pos" -> when (b.symbol) {
                    "⊥" -> false
                    ">=", "T", "pos" -> true
                    else -> null
                }
                "neg" -> when (b.symbol) {
                    "⊥" -> false
                    "<=", "T", "neg" -> true
                    else -> null
                }
                ">=" -> when (b.symbol) {
                    "T", ">=" -> true
                    "<=", "neg" -> null
                    else -> false
                }
                "<=" -> when (b.symbol) {
                    "T", "<=" -> true
                    ">=", "pos" -> null
                    else -> false
                }
                "T" -> b.symbol == "T"
                else -> null
            }

            for (a in intStrct.keys) {
                for (b in intStrct.keys) {
                    println("${a.symbol} <= ${b.symbol}: ${answer(a, b)}")
                    intLattis.parOrd(a, b) shouldBe answer(a, b)
                }
            }
        }

        "join" {
            fun answer(a: AbstractValue, b: AbstractValue): String = when (a.symbol) {
                "⊥" -> b.symbol
                "zero" -> when (b.symbol) {
                    "pos" -> ">="
                    "neg" -> "<="
                    "⊥", "zero" -> "zero"
                    else -> b.symbol
                }
                "pos" -> when (b.symbol) {
                    "pos", "⊥" -> "pos"
                    "neg", "<=" -> "T"
                    "zero" -> ">="
                    else -> b.symbol
                }
                "neg" -> when (b.symbol) {
                    "neg", "⊥" -> "neg"
                    "pos", ">=" -> "T"
                    "zero" -> "<="
                    else -> b.symbol
                }
                ">=" -> when (b.symbol) {
                    "neg", "<=", "T" -> "T"
                    else -> a.symbol
                }
                "<=" -> when (b.symbol) {
                    "pos", ">=", "T" -> "T"
                    else -> a.symbol
                }
                "T" -> "T"
                else -> "error lol"
            }

            for (a in intStrct.keys) {
                for (b in intStrct.keys) {
                    println("Join of ${a.symbol} and ${b.symbol}: ${answer(a, b)}")
                    intLattis.join(a, b).symbol shouldBe answer(a, b)
                }
            }
        }

        "meet" {
            fun answer(a: AbstractValue, b: AbstractValue): String = when (a.symbol) {
                "⊥" -> "⊥"
                "zero" -> when (b.symbol) {
                    "⊥", "pos", "neg" -> "⊥"
                    else -> a.symbol
                }
                "pos" -> when (b.symbol) {
                    "⊥", "neg", "zero", "<=" -> "⊥"
                    else -> a.symbol
                }
                "neg" -> when (b.symbol) {
                    "⊥", "pos", "zero", ">=" -> "⊥"
                    else -> a.symbol
                }
                ">=" -> when (b.symbol) {
                    "neg", "⊥" -> "⊥"
                    "<=", "zero" -> "zero"
                    "T" -> ">="
                    else -> b.symbol
                }
                "<=" -> when (b.symbol) {
                    "pos", "⊥" -> "⊥"
                    ">=", "zero" -> "zero"
                    "T" -> "<="
                    else -> b.symbol
                }
                "T" -> b.symbol
                else -> "error lol"
            }

            for (a in intStrct.keys) {
                for (b in intStrct.keys) {
                    println("Meet of ${a.symbol} and ${b.symbol}: ${answer(a, b)}")
                    intLattis.meet(a, b).symbol shouldBe answer(a, b)
                }
            }
        }

        for (smt in listOf(z3, cvc)){
            if (!backendAvailable(smt)) continue
            println("testing with $smt as backend")

            /*
            "concrete to abstract constant $smt" {
                smtPath = smt

                val ids: MutableMap<String, Int> = mutableMapOf(
                    "pos" to 0,
                    "neg" to 0,
                    "zero" to 0
                )
                var absVal: AbstractValue
                for (i in -5..5) {
                    if (i < 0) {
                        ids["neg"] = ids["neg"]!! + 1
                        absVal = AbstractValue("neg")
                    } else if (i == 0) {
                        ids["zero"] = ids["zero"]!! + 1
                        absVal = AbstractValue("zero")
                    } else {
                        ids["pos"] = ids["pos"]!! + 1
                        absVal = AbstractValue("pos")
                    }
                    intLattis.concreteToAbstractConstant(Function("0"), exampleSymState) == intLattis.concreteToAbstractConstant(Function("0"), exampleSymState)

                    //intLattis.concreteToAbstractConstant(Function("$i"), exampleSymState).let {
                    //    //println("$it shouldBe ${Pair(absVal, ids[absVal.symbol]!!)}")
                    //    //it.first.symbol shouldBe absVal.symbol 
                    //    //it.second shouldBe ids[absVal.symbol]!!
                    //    i shouldBe i
                    //}
                }
            }
            */
        
            "hmmm $smt" {
                smtPath = smt
                intLattis.concreteToAbstractConstant(Function("2"),  exampleSymState) == intLattis.concreteToAbstractConstant(Function("2"),  exampleSymState)
            }
        }

        /* 

        output("\n2 to abstract constant: ${lattis.concreteToAbstractConstant(Function("2"),  exampleSymState)}", Verbosity.SILENT)
        output("\n1 to abstract constant: ${lattis.concreteToAbstractConstant(Function("1"),  exampleSymState)}", Verbosity.SILENT)
        output("\n0 to abstract constant: ${lattis.concreteToAbstractConstant(Function("0"),  exampleSymState)}", Verbosity.SILENT)
        output("\n0 to abstract constant: ${lattis.concreteToAbstractConstant(Function("0"),  exampleSymState)}", Verbosity.SILENT)
        output("\n-1 to abstract constant: ${lattis.concreteToAbstractConstant(Function("-1"),  exampleSymState)}", Verbosity.SILENT)
        output("\n-2 to abstract constant: ${lattis.concreteToAbstractConstant(Function("-2"),  exampleSymState)}", Verbosity.SILENT)
        output("\nx = 1 to abstract constant: ${lattis.concreteToAbstractConstant(ProgVar("x"),  exampleSymState)}", Verbosity.SILENT)
        */


        /* 
        Old version
        val preds: Map<AbstractValue, (Term, SymbolicState) -> LogicNode> = mapOf(
            AbstractValue("bot") to { _,  state -> 
                LogicNode(apply(state.update, state.condition) as Formula, False) 
            }
            , AbstractValue("zero") to { term,  state -> 
                LogicNode(apply(state.update, state.condition) as Formula
                        , apply(state.update, Predicate("=", listOf(term, Function("0")))) as Formula)
            }
            , AbstractValue("pos") to { term,  state -> 
                LogicNode(apply(state.update, state.condition) as Formula
                        , apply(state.update, Predicate(">", listOf(term, Function("0")))) as Formula) 
            }
            , AbstractValue("neg") to { term,  state -> 
                LogicNode(apply(state.update, state.condition) as Formula
                        , apply(state.update, Predicate("<", listOf(term, Function("0")))) as Formula)
            }
            , AbstractValue(">=") to { term,  state -> 
                LogicNode(apply(state.update, state.condition) as Formula
                        , apply(state.update, Predicate(">=", listOf(term, Function("0")))) as Formula)
            }
            , AbstractValue("<=") to { term,  state -> 
                LogicNode(apply(state.update, state.condition) as Formula
                        , apply(state.update, Predicate("<=", listOf(term, Function("0")))) as Formula)
            }
            , AbstractValue("T") to { _,  state -> 
                LogicNode(apply(state.update, state.condition) as Formula, True) 
            }
        )
        */



    }
}