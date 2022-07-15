import io.kotlintest.shouldBe
import org.abs_models.crowbar.main.*
import java.nio.file.Paths

class GenericsTest : CrowbarTest() {
    init {
        for (smt in listOf(z3, cvc)){
            if (!backendAvailable(smt)) continue
            println("testing with $smt as backend")


            "$smt maybe"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/generics.abs")))
                val classDecl = model.extractClassDecl("Generics", "MaybeClass")

                val trivialSuccess = classDecl.extractMethodNode(postInv, "trivialSuccess", repos)
                executeNode(trivialSuccess, repos, postInv) shouldBe true

                val wrapExpressionSuccess = classDecl.extractMethodNode(postInv, "wrapExpressionSuccess", repos)
                executeNode(wrapExpressionSuccess, repos, postInv) shouldBe true

                val updateFieldTrivialSuccess = classDecl.extractMethodNode(postInv, "updateFieldTrivialSuccess", repos)
                executeNode(updateFieldTrivialSuccess, repos, postInv) shouldBe true

                val updateFieldWrapSuccess = classDecl.extractMethodNode(postInv, "updateFieldWrapSuccess", repos)
                executeNode(updateFieldWrapSuccess, repos, postInv) shouldBe true
                //caseSuccess
                val trivialFunctionSuccess = classDecl.extractMethodNode(postInv, "trivialFunctionSuccess", repos)
                executeNode(trivialFunctionSuccess, repos, postInv) shouldBe true

                val caseSuccess = classDecl.extractMethodNode(postInv, "caseSuccess", repos)
                executeNode(caseSuccess, repos, postInv) shouldBe true

                val wrappedOldSuccess = classDecl.extractMethodNode(postInv, "wrappedOldSuccess", repos)
                executeNode(wrappedOldSuccess, repos, postInv) shouldBe true

                val returnNothingSimpleSuccess = classDecl.extractMethodNode(postInv, "returnNothingSimpleSuccess", repos)
                executeNode(returnNothingSimpleSuccess, repos, postInv) shouldBe true


                val returnNothingWrapPostSimpleSuccess = classDecl.extractMethodNode(postInv, "returnNothingWrapPostSimpleSuccess", repos)
                executeNode(returnNothingWrapPostSimpleSuccess, repos, postInv) shouldBe true

                val returnNothingWrapWrapPostSimpleSuccess = classDecl.extractMethodNode(postInv, "returnNothingWrapWrapPostSimpleSuccess", repos)
                executeNode(returnNothingWrapWrapPostSimpleSuccess, repos, postInv) shouldBe true
            }

            "$smt pair"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/generics.abs")))
                val classDecl = model.extractClassDecl("Generics", "PairClass")

                val trivialSuccess = classDecl.extractMethodNode(postInv, "trivialSuccess", repos)
                executeNode(trivialSuccess, repos, postInv) shouldBe true

                val wrapExpressionSuccess = classDecl.extractMethodNode(postInv, "wrapExpressionSuccess", repos)
                executeNode(wrapExpressionSuccess, repos, postInv) shouldBe true

                val updateFieldTrivialSuccess = classDecl.extractMethodNode(postInv, "updateFieldTrivialSuccess", repos)
                executeNode(updateFieldTrivialSuccess, repos, postInv) shouldBe true

                val updateFieldWrapSuccess = classDecl.extractMethodNode(postInv, "updateFieldWrapSuccess", repos)
                executeNode(updateFieldWrapSuccess, repos, postInv) shouldBe true

                val wrappedOldSuccess = classDecl.extractMethodNode(postInv, "wrappedOldSuccess", repos)
                executeNode(wrappedOldSuccess, repos, postInv) shouldBe true

                val fstSimpleSuccess = classDecl.extractMethodNode(postInv, "fstSimpleSuccess", repos)
                executeNode(fstSimpleSuccess, repos, postInv) shouldBe true

                val fstParamSuccess = classDecl.extractMethodNode(postInv, "fstParamSuccess", repos)
                executeNode(fstParamSuccess, repos, postInv) shouldBe true

                val sndSimpleSuccess = classDecl.extractMethodNode(postInv, "sndSimpleSuccess", repos)
                executeNode(sndSimpleSuccess, repos, postInv) shouldBe true

                val sndParamSuccess = classDecl.extractMethodNode(postInv, "sndParamSuccess", repos)
                executeNode(sndParamSuccess, repos, postInv) shouldBe true


            }

            "$smt pairFunctions"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/generics.abs")))

                val pairFuncSimpleSuccess = model.extractFunctionDecl("Generics", "pairFuncSimpleSuccess").exctractFunctionNode(postInv)
                executeNode(pairFuncSimpleSuccess, repos, postInv) shouldBe true

                val pairFuncWrappedSimpleSuccess = model.extractFunctionDecl("Generics", "pairFuncWrappedSimpleSuccess").exctractFunctionNode(postInv)
                executeNode(pairFuncWrappedSimpleSuccess, repos, postInv) shouldBe true


            }


            "$smt list"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/generics.abs")))
                val classDecl = model.extractClassDecl("Generics", "ListClass")

                val trivialSuccess = classDecl.extractMethodNode(postInv, "trivialSuccess", repos)
                executeNode(trivialSuccess, repos, postInv) shouldBe true//trivialWrapResultSuccess
                val trivialWrapResultSuccess = classDecl.extractMethodNode(postInv, "trivialWrapResultSuccess", repos)
                executeNode(trivialWrapResultSuccess, repos, postInv) shouldBe true

                val wrapExpressionSuccess = classDecl.extractMethodNode(postInv, "wrapExpressionSuccess", repos)
                executeNode(wrapExpressionSuccess, repos, postInv) shouldBe true

                val updateFieldTrivialSuccess = classDecl.extractMethodNode(postInv, "updateFieldTrivialSuccess", repos)
                executeNode(updateFieldTrivialSuccess, repos, postInv) shouldBe true

                val updateFieldWrapSuccess = classDecl.extractMethodNode(postInv, "updateFieldWrapSuccess", repos)
                executeNode(updateFieldWrapSuccess, repos, postInv) shouldBe true

                val wrappedOldSuccess = classDecl.extractMethodNode(postInv, "wrappedOldSuccess", repos)
                executeNode(wrappedOldSuccess, repos, postInv) shouldBe true

                val headSimpleSuccess = classDecl.extractMethodNode(postInv, "headSimpleSuccess", repos)
                executeNode(headSimpleSuccess, repos, postInv) shouldBe true

                val tailSimpleSuccess = classDecl.extractMethodNode(postInv, "tailSimpleSuccess", repos)
                executeNode(tailSimpleSuccess, repos, postInv) shouldBe true

                val headTailSimpleSuccess = classDecl.extractMethodNode(postInv, "headTailSimpleSuccess", repos)
                executeNode(headTailSimpleSuccess, repos, postInv) shouldBe true


                val returnNilSuccess = classDecl.extractMethodNode(postInv, "returnNilSuccess", repos)
                executeNode(returnNilSuccess, repos, postInv) shouldBe true

                val callMyHeadFuncSuccess = classDecl.extractMethodNode(postInv, "callMyHeadFuncSuccess", repos)
                executeNode(callMyHeadFuncSuccess, repos, postInv) shouldBe true

                val callMyHeadFuncFail = classDecl.extractMethodNode(postInv, "callMyHeadFuncFail", repos)
                executeNode(callMyHeadFuncFail, repos, postInv) shouldBe false

                val callMyContainsSuccess = classDecl.extractMethodNode(postInv, "callMyContainsSuccess", repos)
                executeNode(callMyContainsSuccess, repos, postInv) shouldBe true

                val callMyContainsFail = classDecl.extractMethodNode(postInv, "callMyContainsFail", repos)
                executeNode(callMyContainsFail, repos, postInv) shouldBe false

                val lengthCallNonEmptyListSuccess = classDecl.extractMethodNode(postInv, "lengthCallNonEmptyListSuccess", repos)
                executeNode(lengthCallNonEmptyListSuccess, repos, postInv) shouldBe true

                val lengthCallNonEmptyListFail = classDecl.extractMethodNode(postInv, "lengthCallNonEmptyListFail", repos)
                executeNode(lengthCallNonEmptyListFail, repos, postInv) shouldBe false

                val lengthCallEmptyListSuccess = classDecl.extractMethodNode(postInv, "lengthCallEmptyListSuccess", repos)
                executeNode(lengthCallEmptyListSuccess, repos, postInv) shouldBe true

                val lengthCallEmptyListFail = classDecl.extractMethodNode(postInv, "lengthCallEmptyListFail", repos)
                executeNode(lengthCallEmptyListFail, repos, postInv) shouldBe false
            }

            "$smt triple"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/generics.abs")))
                val classDecl = model.extractClassDecl("Generics", "TripleClass")

                val trivialSuccess = classDecl.extractMethodNode(postInv, "trivialSuccess", repos)
                executeNode(trivialSuccess, repos, postInv) shouldBe true

                val trivialWrapResultSuccess = classDecl.extractMethodNode(postInv, "trivialWrapResultSuccess", repos)
                executeNode(trivialWrapResultSuccess, repos, postInv) shouldBe true

                val wrapExpressionSuccess = classDecl.extractMethodNode(postInv, "wrapExpressionSuccess", repos)
                executeNode(wrapExpressionSuccess, repos, postInv) shouldBe true

                val updateFieldTrivialSuccess = classDecl.extractMethodNode(postInv, "updateFieldTrivialSuccess", repos)
                executeNode(updateFieldTrivialSuccess, repos, postInv) shouldBe true

                val wrappedOldSuccess = classDecl.extractMethodNode(postInv, "wrappedOldSuccess", repos)
                executeNode(wrappedOldSuccess, repos, postInv) shouldBe true

                val fstTSimpleSuccess = classDecl.extractMethodNode(postInv, "fstTSimpleSuccess", repos)
                executeNode(fstTSimpleSuccess, repos, postInv) shouldBe true

                val fstTParamSuccess = classDecl.extractMethodNode(postInv, "fstTParamSuccess", repos)
                executeNode(fstTParamSuccess, repos, postInv) shouldBe true


                val sndTSimpleSuccess = classDecl.extractMethodNode(postInv, "sndTSimpleSuccess", repos)
                executeNode(sndTSimpleSuccess, repos, postInv) shouldBe true
                val sndTParamSuccess = classDecl.extractMethodNode(postInv, "sndTParamSuccess", repos)
                executeNode(sndTParamSuccess, repos, postInv) shouldBe true


                val trdTSimpleSuccess = classDecl.extractMethodNode(postInv, "trdTSimpleSuccess", repos)
                executeNode(trdTSimpleSuccess, repos, postInv) shouldBe true

                val trdTParamSuccess = classDecl.extractMethodNode(postInv, "trdTParamSuccess", repos)
                executeNode(trdTParamSuccess, repos, postInv) shouldBe true

            }//

            "$smt set"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/generics.abs")))
                val classDecl = model.extractClassDecl("Generics", "SetClass")

                val callCustomContainsCallingLibContainsSuccess = classDecl.extractMethodNode(postInv, "callCustomContainsCallingLibContainsSuccess", repos)
                executeNode(callCustomContainsCallingLibContainsSuccess, repos, postInv) shouldBe true

                val callCustomContainsCallingLibContainsFail = classDecl.extractMethodNode(postInv, "callCustomContainsCallingLibContainsFail", repos)
                executeNode(callCustomContainsCallingLibContainsFail, repos, postInv) shouldBe false

            }

            "$smt map"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/generics.abs")))
                val classDecl = model.extractClassDecl("Generics", "MapClass")

                val callEmptyMapOnEmptyMapSuccess = classDecl.extractMethodNode(postInv, "callEmptyMapOnEmptyMapSuccess", repos)
                executeNode(callEmptyMapOnEmptyMapSuccess, repos, postInv) shouldBe true

                val callEmptyMapOnEmptyMapFail = classDecl.extractMethodNode(postInv, "callEmptyMapOnEmptyMapFail", repos)
                executeNode(callEmptyMapOnEmptyMapFail, repos, postInv) shouldBe false

                val callEmptyMapOnNonEmptyMapSuccess = classDecl.extractMethodNode(postInv, "callEmptyMapOnNonEmptyMapSuccess", repos)
                executeNode(callEmptyMapOnNonEmptyMapSuccess, repos, postInv) shouldBe true

                val callEmptyMapOnNonEmptyMapFail = classDecl.extractMethodNode(postInv, "callEmptyMapOnNonEmptyMapFail", repos)
                executeNode(callEmptyMapOnNonEmptyMapFail, repos, postInv) shouldBe false

                val callLookupOnEmptyMapSuccess = classDecl.extractMethodNode(postInv, "callLookupOnEmptyMapSuccess", repos)
                executeNode(callLookupOnEmptyMapSuccess, repos, postInv) shouldBe true

                val callLookupOnEmptyMapFail = classDecl.extractMethodNode(postInv, "callLookupOnEmptyMapFail", repos)
                executeNode(callLookupOnEmptyMapFail, repos, postInv) shouldBe false

                val callLookupOnNonEmptyMapWithoutElemSuccess = classDecl.extractMethodNode(postInv, "callLookupOnNonEmptyMapWithoutElemSuccess", repos)
                executeNode(callLookupOnNonEmptyMapWithoutElemSuccess, repos, postInv) shouldBe true
                val callLookupOnNonEmptyMapWithoutElemFail = classDecl.extractMethodNode(postInv, "callLookupOnNonEmptyMapWithoutElemFail", repos)
                executeNode(callLookupOnNonEmptyMapWithoutElemFail, repos, postInv) shouldBe false
                val callLookupOnNonEmptyMapWithElemSuccess = classDecl.extractMethodNode(postInv, "callLookupOnNonEmptyMapWithElemSuccess", repos)
                executeNode(callLookupOnNonEmptyMapWithElemSuccess, repos, postInv) shouldBe true
                val callLookupOnNonEmptyMapWithElemFail = classDecl.extractMethodNode(postInv, "callLookupOnNonEmptyMapWithElemFail", repos)
                executeNode(callLookupOnNonEmptyMapWithElemFail, repos, postInv) shouldBe false
                }
        }
    }
}