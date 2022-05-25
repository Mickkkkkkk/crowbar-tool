
import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.main.ADTRepos
import org.abs_models.crowbar.main.Repository
import org.abs_models.crowbar.main.load
import org.abs_models.crowbar.rule.FreshGenerator
import org.abs_models.crowbar.rule.MatchCondition
import org.abs_models.crowbar.rule.containsAbstractVar
import org.abs_models.crowbar.rule.match
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.tree.nextPITStrategy
import org.abs_models.crowbar.types.PostInvariantPair
import java.nio.file.Paths
import java.util.*

class BasicTest : StringSpec() {

    private fun addExpr(e1 : Expr, e2 : Expr): Expr = SExpr("+", listOf(e1,e2))

    init {

        val model = load(listOf(Paths.get("src/test/resources/empty.abs"))).first
        val int = model.intType


        val conc = addExpr(ProgVar("v",int), addExpr(Const("1"), ProgVar("v")))
        val pattern = addExpr(ExprAbstractVar("A"), addExpr(Const("1"), ExprAbstractVar("A")))
        val pattern2 = addExpr(ExprAbstractVar("A"), addExpr(ExprAbstractVar("A"), Const("1")))
        val pattern3 = addExpr(ExprAbstractVar("A"), Const("1"))

        ADTRepos.initBuiltIn()
        "collect"{
            val stmt = WhileStmt(SExpr(">=", listOf(Field("f",int), Const("0"))),
                                 SeqStmt(AssignStmt(Field("g",int), ProgVar("v")), SkipStmt),
                                 PPId(0))
            stmt.collectAll(Field::class).size shouldBe 2
            stmt.collectAll(AssignStmt::class).size shouldBe 1
            stmt.collectAll(Stmt::class).size shouldBe 4
            stmt.collectAll(Location::class).size shouldBe 3
        }

        /*"matchAndApply" {
            val cond = MatchCondition()
            match(conc, pattern, cond)
            assert(!cond.failure)
            val res = apply(pattern3,cond) as Anything
            res shouldBe AddExpr(ProgVar("v"), Const("1"))
            assert(!containsAbstractVar(res))
        }*/
//        "Z3Test"{
//            val prog = SeqStmt(
//                    IfStmt(SExpr(">=", listOf(ProgVar("v",int), Const("0"))),
//                            AssignStmt(Field("f",int), ProgVar("v",int)),
//                            AssignStmt(Field("f",int), SExpr("-", listOf(ProgVar("v",int))))
//                    ),
//                    ReturnStmt(Field("f",int))
//            )
//
//            val input3 = SymbolicState(
//                    True,
//                    EmptyUpdate,
//                    Modality(prog, PostInvariantPair(Predicate(">=", listOf(select(Field("f",int)), Function("0"))),
//                            True)), listOf()
//            )
//
//            val strategy = nextPITStrategy(Repository(null))
//            val node = SymbolicNode(input3, emptyList())
//            strategy.execute(node)
//            println(node.debugString(0))
//            println(node.finishedExecution())
//            for(l in node.collectLeaves()){
//                println(l.evaluate())
//            }
//        }
        "deupdatify" {/* { v := 0 }{ v := v+1 } ((v == { v := v+1 }(v+w)) /\ { v := v+1 }!(v == w))
                          ->
                         (0+1 == (0+1+1+w)) /\ !(0+1+1 == w) */
            val s = UpdateOnFormula(ChainUpdate(ElementaryUpdate(ProgVar("v",int), Function("0")), ElementaryUpdate(ProgVar("v",int), Function("+", listOf(ProgVar("v",int), Function("1"))))),
                    And(Predicate("=", listOf(
                            ProgVar("v",int),
                            UpdateOnTerm(ElementaryUpdate(ProgVar("v",int), Function("+", listOf(ProgVar("v",int), Function("1")))),
                                    Function("+", listOf(ProgVar("v",int), ProgVar("w",int))))
                    )), UpdateOnFormula(ElementaryUpdate(ProgVar("v",int), Function("+", listOf(ProgVar("v",int), Function("1")))),
                            Not(Predicate("=", listOf(ProgVar("v",int), ProgVar("w",int)))))))

            deupdatify(s).prettyPrint() shouldBe "(0+1=0+1+1+w:ABS.StdLib.Int) /\\ (!0+1+1=w:ABS.StdLib.Int)"
        }
        "apply" {
            apply(ElementaryUpdate(ProgVar("v",int), Function("0")),
                    Predicate("=", listOf(Function("+", listOf(ProgVar("v",int), ProgVar("v",int))), Function("0")))) shouldBe
                    Predicate("=", listOf(Function("+", listOf(Function("0"), Function("0"))), Function("0")))
        }
        "subst" {
            subst(ProgVar("v",int), ProgVar("v",int), Function("0")) shouldBe Function("0")
            subst(ProgVar("w",int), ProgVar("v",int), Function("0")) shouldBe ProgVar("w")
            subst(Predicate("=",
                    listOf(Function("+", listOf(ProgVar("v",int), ProgVar("v",int))),
                            Function("0"))), ProgVar("v",int), Function("0")) shouldBe
                    Predicate("=",
                            listOf(Function("+", listOf(Function("0"), Function("0"))),
                                    Function("0")))

            subst(Predicate("=",
                    listOf(Function("+", listOf(UpdateOnTerm(ElementaryUpdate(ProgVar("v",int), Function("1")), ProgVar("v",int)),
                            UpdateOnTerm(ElementaryUpdate(ProgVar("w",int), Function("1")), ProgVar("v")))),
                            Function("0"))), ProgVar("v",int), Function("0")) shouldBe
                    Predicate("=",
                            listOf(Function("+", listOf(UpdateOnTerm(ElementaryUpdate(ProgVar("v",int), Function("1")), ProgVar("v",int)),
                                    UpdateOnTerm(ElementaryUpdate(ProgVar("w",int), Function("1")), Function("0")))),
                                    Function("0")))

            subst(ElementaryUpdate(ProgVar("v",int), Function("+", listOf(ProgVar("v",int), Function("1")))),
                    ProgVar("v",int),
                    Function("0")) shouldBe
                    ElementaryUpdate(ProgVar("v",int), Function("+", listOf(Function("0"), Function("1"))))

        }
        "matchAndFail1" {
            val cond = MatchCondition()
            match(conc, pattern2, cond)
            assert(cond.failure)
            cond.failReason shouldBe "AbstractVar A failed unification with two terms: v:ABS.StdLib.Int and 1"
        }
        "matchAndFail2"{
            val cond = MatchCondition()
            match(pattern, conc, cond)
            assert(cond.failure)
            cond.failReason shouldBe "Concrete statement contains abstract variables: +(A,+(1,A))"
        }
        "matchAndFail3"{
            val cond = MatchCondition()
            match(Const("v"), StmtAbstractVar("A"), cond)
            assert(cond.failure)
            cond.failReason shouldBe "AbstractVar A failed unification because of a type error: v"
        }
        "matchSet"{
            val stmt = SyncStmt(ProgVar("v"),  ProgVar("w"), ConcreteStringSet(), FreshGenerator.getFreshPP())
            val schablone = SyncStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR"), AbstractStringSet("RESOLVES"), PPAbstractVar("PP"))
            val cond = MatchCondition()
            match(stmt, schablone, cond)
            println(cond.failReason)
            assert(cond.map[AbstractStringSet("RESOLVES")] != null)
            assert(cond.map[AbstractStringSet("RESOLVES")] is ConcreteStringSet)
            assert((cond.map[AbstractStringSet("RESOLVES")] as ConcreteStringSet).vals.isEmpty())
        }
        "containsAbstractVar"{
            assert(!containsAbstractVar(conc))
            assert(containsAbstractVar(pattern))
            assert(containsAbstractVar(pattern2))
            assert(containsAbstractVar(pattern3))
        }
    }

}