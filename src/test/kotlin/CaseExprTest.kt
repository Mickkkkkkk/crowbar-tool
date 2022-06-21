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

            }

            "$smt boolPatternMatching"{
                smtPath = smt
                val (model, repos) = load(listOf(Paths.get("src/test/resources/caseExpr.abs")))
                val caseBoolSimpleSuccessFuncDecl = model.extractFunctionDecl("CaseExpr", "caseBoolSimpleSuccessMethod").exctractFunctionNode(postInv)
                executeNode(caseBoolSimpleSuccessFuncDecl, repos, postInv) shouldBe true

            }


            "$smt nested"{
                smtPath = smt
                val (model, repos) = load(listOf(Paths.get("src/test/resources/caseExpr.abs")))
                val classDecl = model.extractClassDecl("CaseExpr", "E")
                val nestedCaseExprSuccess =  classDecl.extractMethodNode(postInv, "nestedCaseExprsSuccess", repos)
                executeNode(nestedCaseExprSuccess, repos, postInv) shouldBe true
                val nestedCaseExprFail =  classDecl.extractMethodNode(postInv, "nestedCaseExprsFail", repos)
                executeNode(nestedCaseExprFail, repos, postInv) shouldBe false

                val nestedIfCaseExprsSuccess =  classDecl.extractMethodNode(postInv, "nestedIfCaseExprsSuccess", repos)
                executeNode(nestedIfCaseExprsSuccess, repos, postInv) shouldBe true

            }


            "$smt generics"{
                smtPath = z3
                val (model, repos) = load(listOf(Paths.get("src/test/resources/caseExpr.abs")))
				val pairPartialMatchSimpleSuccess = model.extractFunctionDecl("CaseExpr", "pairPartialMatchSimpleSuccess").exctractFunctionNode(postInv)
				executeNode(pairPartialMatchSimpleSuccess, repos, postInv) shouldBe true

                val listMatchFuncSimpleSuccess = model.extractFunctionDecl("CaseExpr", "listMatchFuncSimpleSuccess").exctractFunctionNode(postInv)
                executeNode(listMatchFuncSimpleSuccess, repos, postInv) shouldBe true

                val maybeMatchFuncSimpleSuccess = model.extractFunctionDecl("CaseExpr", "maybeMatchFuncSimpleSuccess").exctractFunctionNode(postInv)
                executeNode(maybeMatchFuncSimpleSuccess, repos, postInv) shouldBe true

                val oneElemListMatchFuncSimpleSuccess = model.extractFunctionDecl("CaseExpr", "oneElemListMatchFuncSimpleSuccess").exctractFunctionNode(postInv)
                executeNode(oneElemListMatchFuncSimpleSuccess, repos, postInv) shouldBe true

                val wrappedMaybeMatchFuncSimpleSuccess = model.extractFunctionDecl("CaseExpr", "wrappedMaybeMatchFuncSimpleSuccess").exctractFunctionNode(postInv)
                executeNode(wrappedMaybeMatchFuncSimpleSuccess, repos, postInv) shouldBe true

                val pairPlaceholdersFuncSimpleSuccess = model.extractFunctionDecl("CaseExpr", "pairPlaceholdersFuncSimpleSuccess").exctractFunctionNode(postInv)
                executeNode(pairPlaceholdersFuncSimpleSuccess, repos, postInv) shouldBe true
                val pairPlaceholderFuncWildcardSimpleSuccess = model.extractFunctionDecl("CaseExpr", "pairPlaceholderFuncWildcardSimpleSuccess").exctractFunctionNode(postInv)
                executeNode(pairPlaceholderFuncWildcardSimpleSuccess, repos, postInv) shouldBe true

                val maybePlaceholdersFuncSimpleSuccess = model.extractFunctionDecl("CaseExpr", "maybePlaceholdersFuncSimpleSuccess").exctractFunctionNode(postInv)
                executeNode(maybePlaceholdersFuncSimpleSuccess, repos, postInv) shouldBe true

                val listPlaceholdersFuncSimpleSuccess = model.extractFunctionDecl("CaseExpr", "listPlaceholdersFuncSimpleSuccess").exctractFunctionNode(postInv)
                executeNode(listPlaceholdersFuncSimpleSuccess, repos, postInv) shouldBe true

                val classDecl = model.extractClassDecl("CaseExpr", "E")
                val callRecFunctionNoContractSuccess =  classDecl.extractMethodNode(postInv, "callRecFunctionNoContractSuccess", repos)
                executeNode(callRecFunctionNoContractSuccess, repos, postInv) shouldBe true

                val callFuncNestedGenericsParam =  classDecl.extractMethodNode(postInv, "callFuncNestedGenericsParam", repos)
                executeNode(callFuncNestedGenericsParam, repos, postInv) shouldBe true

            }
        }
        "z3 wildcards-no-precondition"{
            smtPath = z3
            val (model, repos) = load(listOf(Paths.get("src/test/resources/caseExpr.abs")))
            val pairWildcardsNoPreSimpleSuccess = model.extractFunctionDecl("CaseExpr", "pairWildcardsNoPreSimpleSuccess").exctractFunctionNode(postInv)
            executeNode(pairWildcardsNoPreSimpleSuccess, repos, postInv) shouldBe true
        }
    }
}