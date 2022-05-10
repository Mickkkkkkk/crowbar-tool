import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.types.PostInvType
import java.nio.file.Paths
import kotlin.system.exitProcess

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

            }

            "$smt triple"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/generics.abs")))
                val classDecl = model.extractClassDecl("Generics", "TripleClass")

                val trivialSuccess = classDecl.extractMethodNode(postInv, "trivialSuccess", repos)
                executeNode(trivialSuccess, repos, postInv) shouldBe true//trivialWrapResultSuccess

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


            }
        }
    }
}