import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.types.PostInvType
import java.nio.file.Paths

class OldTest : CrowbarTest() {
    init {
        for (smt in listOf(z3, cvc)){
            if (!backendAvailable(smt)) continue
            println("testing with $smt as backend")

            "$smt trivialOld"{
                smtPath = smt
                val (model, repos) = load(listOf(Paths.get("src/test/resources/old.abs")))
                val classDecl = model.extractClassDecl("Old", "OldC")

                val trivialSuccess = classDecl.extractMethodNode(postInv, "trivialSuccess", repos)
                executeNode(trivialSuccess, repos, postInv) shouldBe true

                val incrSuccess = classDecl.extractMethodNode(postInv, "incrSuccess", repos)
                executeNode(incrSuccess, repos, postInv) shouldBe true

                val trivialFail = classDecl.extractMethodNode(postInv, "trivialFail", repos)
                executeNode(trivialFail, repos, postInv) shouldBe false
            }
//
            "$smt simpleOld"{
                smtPath = smt
                val (model, repos) = load(listOf(Paths.get("src/test/resources/old.abs")))
                val classDecl = model.extractClassDecl("Old", "OldC")

                val simpleSuccess = classDecl.extractMethodNode(postInv, "simpleSuccess", repos)
                executeNode(simpleSuccess, repos, postInv) shouldBe true

                val simpleFail = classDecl.extractMethodNode(postInv, "simpleFail", repos)
                executeNode(simpleFail, repos, postInv) shouldBe false

            }

            "$smt booleanOld"{
                smtPath = smt
                val (model, repos) = load(listOf(Paths.get("src/test/resources/old.abs")))
                val classDecl = model.extractClassDecl("Old", "OldC")

                val booleanValSuccess = classDecl.extractMethodNode(postInv, "booleanValSuccess", repos)
                executeNode(booleanValSuccess, repos, postInv) shouldBe true

                val booleanValFail = classDecl.extractMethodNode(postInv, "booleanValFail", repos)
                executeNode(booleanValFail, repos, postInv) shouldBe false
            }

            "$smt predicateOld"{
                smtPath = smt
                val (model, repos) = load(listOf(Paths.get("src/test/resources/old.abs")))
                val classDecl = model.extractClassDecl("Old", "OldC")

                val predicateSimpleSuccess = classDecl.extractMethodNode(postInv, "predicateSimpleSuccess", repos)
                executeNode(predicateSimpleSuccess, repos, postInv) shouldBe true

                val predicateSimpleFail = classDecl.extractMethodNode(postInv, "predicateSimpleFail", repos)
                executeNode(predicateSimpleFail, repos, postInv) shouldBe false


                val predicateImplSuccess = classDecl.extractMethodNode(postInv, "predicateImplSuccess", repos)
                executeNode(predicateImplSuccess, repos, postInv) shouldBe true

                val predicateImplFail = classDecl.extractMethodNode(postInv, "predicateImplFail", repos)
                executeNode(predicateImplFail, repos, postInv) shouldBe false

                val predicateComplexSuccess = classDecl.extractMethodNode(postInv, "predicateComplexSuccess", repos)
                executeNode(predicateComplexSuccess, repos, postInv) shouldBe true
            }

            "$smt ifOld"{
                smtPath = smt
                val (model, repos) = load(listOf(Paths.get("src/test/resources/old.abs")))
                val classDecl = model.extractClassDecl("Old", "OldC")

                val oldIfSuccess = classDecl.extractMethodNode(postInv, "oldIfSuccess", repos)
                executeNode(oldIfSuccess, repos, postInv) shouldBe true

            }

            "$smt awaitOld"{
                smtPath = smt
                val (model, repos) = load(listOf(Paths.get("src/test/resources/old.abs")))
                val classDecl = model.extractClassDecl("Old", "OldC")

                val awaitSuccess = classDecl.extractMethodNode(postInv, "awaitSuccess", repos)
                executeNode(awaitSuccess, repos, postInv) shouldBe true

                val awaitFail = classDecl.extractMethodNode(postInv, "awaitFail", repos)
                executeNode(awaitFail, repos, postInv) shouldBe false

            }

            "$smt whileOld"{
                smtPath = smt
                val (model, repos) = load(listOf(Paths.get("src/test/resources/old.abs")))
                val classDecl = model.extractClassDecl("Old", "OldC")

                val predicateWhileSuccess = classDecl.extractMethodNode(postInv, "predicateWhileSuccess", repos)
                executeNode(predicateWhileSuccess, repos, postInv) shouldBe true

            }

            "$smt propOld"{
                smtPath = smt
                val (model, repos) = load(listOf(Paths.get("src/test/resources/oldprop.abs")))
                val classDecl = model.extractClassDecl("M", "C")

                var ss = classDecl.extractMethodNode(postInv, "m", repos)
                executeNode(ss, repos, postInv) shouldBe true
                ss = classDecl.extractMethodNode(postInv, "m2", repos)
                executeNode(ss, repos, postInv) shouldBe true
                ss = classDecl.extractMethodNode(postInv, "m3", repos)
                executeNode(ss, repos, postInv) shouldBe true
                ss = classDecl.extractMethodNode(postInv, "n1", repos)
                executeNode(ss, repos, postInv) shouldBe true
                ss = classDecl.extractMethodNode(postInv, "n2", repos)
                executeNode(ss, repos, postInv) shouldBe true
                ss = classDecl.extractMethodNode(postInv, "modify", repos)
                executeNode(ss, repos, postInv) shouldBe true
                ss = classDecl.extractMethodNode(postInv, "modifyFail", repos)
                executeNode(ss, repos, postInv) shouldBe false
                ss = classDecl.extractMethodNode(postInv, "doNothing", repos)
                executeNode(ss, repos, postInv) shouldBe true
            }
        }
    }
}