import io.kotlintest.shouldBe
import org.abs_models.crowbar.main.*
import java.nio.file.Paths

class CaseExprTest : CrowbarTest() {
    init {
        for (smt in listOf(z3, cvc)){
            if (!backendAvailable(smt)) continue
            println("testing with $smt as backend")

            "$smt caseExp"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/caseExpr.abs")))
                val classDecl = model.extractClassDecl("CaseExpr", "E")

                val fullIntSuccess = classDecl.extractMethodNode(postInv, "fullIntSuccess", repos)
                executeNode(fullIntSuccess, repos, postInv) shouldBe true

                val intParamTypeReturnSuccess = classDecl.extractMethodNode(postInv, "intParamTypeReturnSuccess", repos)
                executeNode(intParamTypeReturnSuccess, repos, postInv) shouldBe true

                val constMatchFullTypeSuccess = classDecl.extractMethodNode(postInv, "constMatchFullTypeSuccess", repos)
                executeNode(constMatchFullTypeSuccess, repos, postInv) shouldBe true

                val complexTypeMatchSuccess = classDecl.extractMethodNode(postInv, "complexTypeMatchSuccess", repos)
                executeNode(complexTypeMatchSuccess, repos, postInv) shouldBe true

                val functorUsageSuccess = classDecl.extractMethodNode(postInv, "functorUsageSuccess", repos)
                executeNode(functorUsageSuccess, repos, postInv) shouldBe true

                val assignmentCaseExprSuccess = classDecl.extractMethodNode(postInv, "assignmentCaseExprSuccess", repos)
                executeNode(assignmentCaseExprSuccess, repos, postInv) shouldBe true
            }

            "$smt patternMatching"{
                smtPath = smt
                val (model, repos) = load(listOf(Paths.get("src/test/resources/caseExpr.abs")))
                val classDecl = model.extractClassDecl("CaseExpr", "E")

                val patternMatchingIntTrivialType3Success =
                    classDecl.extractMethodNode(postInv, "patternMatchingIntTrivialType3Success", repos)
                executeNode(patternMatchingIntTrivialType3Success, repos, postInv) shouldBe true

                val patternMatchingFunctorSuccess =
                    classDecl.extractMethodNode(postInv, "patternMatchingFunctorSuccess", repos)
                executeNode(patternMatchingFunctorSuccess, repos, postInv) shouldBe true

                val patternMatchingTypeTrivialType3Success =
                    classDecl.extractMethodNode(postInv, "patternMatchingTypeTrivialType3Success", repos)
                executeNode(patternMatchingTypeTrivialType3Success, repos, postInv) shouldBe true

                val patternMatchingWrapTypeFirstBranchSuccess =
                    classDecl.extractMethodNode(postInv, "patternMatchingWrapTypeFirstBranchSuccess", repos)
                executeNode(patternMatchingWrapTypeFirstBranchSuccess, repos, postInv) shouldBe true

                val patternMatchingDoubleWrapTypeFirstBranchSuccess =
                    classDecl.extractMethodNode(postInv, "patternMatchingDoubleWrapTypeFirstBranchSuccess", repos)
                executeNode(patternMatchingDoubleWrapTypeFirstBranchSuccess, repos, postInv) shouldBe true

                val patternMatchingDoubleWrapTypeFirstBranchFail =
                    classDecl.extractMethodNode(postInv, "patternMatchingDoubleWrapTypeFirstBranchFail", repos)
                executeNode(patternMatchingDoubleWrapTypeFirstBranchFail, repos, postInv) shouldBe false

                val patternMatchingFuncMatchSuccess =
                    classDecl.extractMethodNode(postInv, "patternMatchingFuncMatchSuccess", repos)
                executeNode(patternMatchingFuncMatchSuccess, repos, postInv) shouldBe true

                val simpleInnerWildCardSuccess =
                    classDecl.extractMethodNode(postInv, "simpleInnerWildCardSuccess", repos)
                executeNode(simpleInnerWildCardSuccess, repos, postInv) shouldBe true

                val innerWildCardSuccess =
                    classDecl.extractMethodNode(postInv, "innerWildCardSuccess", repos)
                executeNode(innerWildCardSuccess, repos, postInv) shouldBe true

                val innerWildCardPairSuccess =
                    classDecl.extractMethodNode(postInv, "innerWildCardPairSuccess", repos)
                executeNode(innerWildCardPairSuccess, repos, postInv) shouldBe true

                val innerWildCardPairFail =
                    classDecl.extractMethodNode(postInv, "innerWildCardPairFail", repos)
                executeNode(innerWildCardPairFail, repos, postInv) shouldBe false
            }

            "$smt boolPatternMatching"{
                smtPath = smt
                val (model, repos) = load(listOf(Paths.get("src/test/resources/caseExpr.abs")))
                val caseBoolSimpleSuccessFuncDecl = model.extractFunctionDecl("CaseExpr", "caseBoolSimpleSuccessMethod").exctractFunctionNode(postInv)
                executeNode(caseBoolSimpleSuccessFuncDecl, repos, postInv) shouldBe true

            }
        }
    }
}