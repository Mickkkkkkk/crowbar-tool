import io.kotlintest.shouldBe
import org.abs_models.crowbar.main.*
import java.nio.file.Paths

class CaseTest : CrowbarTest() {
	init {

		for (smt in listOf(z3, cvc)) {
			if (!backendAvailable(smt)) continue
			println("testing with $smt as backend")


			"$smt case"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/case.abs")))
				val classDecl = model.extractClassDecl("M", "C")

				var res = classDecl.extractMethodNode(postInv, "m1", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "m2", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "m3", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "m4", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "m5", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "m6", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "caseBoolSimpleSuccessMethod", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "localBoolVarSimpleSuccess", repos)
				executeNode(res, repos, postInv) shouldBe true
			}

			"$smt wildcards"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/case.abs")))
				val classDecl = model.extractClassDecl("M", "C")
				val simpleInnerWildCardSuccess =
					classDecl.extractMethodNode(postInv, "simpleInnerWildCardSuccess", repos)
				executeNode(simpleInnerWildCardSuccess, repos, postInv) shouldBe true

				val innerWildCardSuccess =
					classDecl.extractMethodNode(postInv, "innerWildCardSuccess", repos)
				executeNode(innerWildCardSuccess, repos, postInv) shouldBe true


			}

			"$smt datatype"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/case.abs")))
				val classDecl = model.extractClassDecl("M", "C")
				val fullConcrDTypeSuccess =
					classDecl.extractMethodNode(postInv, "fullConcrDTypeSuccess", repos)
				executeNode(fullConcrDTypeSuccess, repos, postInv) shouldBe true

				val fullConcrDTypeSuccessPre =
					classDecl.extractMethodNode(postInv, "fullConcrDTypeSuccessPre", repos)
				executeNode(fullConcrDTypeSuccessPre, repos, postInv) shouldBe true
			}

			"$smt generics"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/case.abs")))
				val classDecl = model.extractClassDecl("M", "C")
				val innerWildCardPairSuccess =
					classDecl.extractMethodNode(postInv, "innerWildCardPairSuccess", repos)
				executeNode(innerWildCardPairSuccess, repos, postInv) shouldBe true

				val innerWildCardPairFail =
					classDecl.extractMethodNode(postInv, "innerWildCardPairFail", repos)
				executeNode(innerWildCardPairFail, repos, postInv) shouldBe false

				val doubleWildCardPairSuccess =
					classDecl.extractMethodNode(postInv, "doubleWildCardPairSuccess", repos)
				executeNode(doubleWildCardPairSuccess, repos, postInv) shouldBe true

				val doubleWildCardPairSuccessPre =
					classDecl.extractMethodNode(postInv, "doubleWildCardPairSuccessPre", repos)
				executeNode(doubleWildCardPairSuccessPre, repos, postInv) shouldBe true
				val maybeMatchSimpleSuccess =
					classDecl.extractMethodNode(postInv, "maybeMatchSimpleSuccess", repos)
				executeNode(maybeMatchSimpleSuccess, repos, postInv) shouldBe true
				val listMatchSimpleSuccess =
					classDecl.extractMethodNode(postInv, "listMatchSimpleSuccess", repos)
				executeNode(listMatchSimpleSuccess, repos, postInv) shouldBe true

				val listPlaceholderSimpleSuccess =
					classDecl.extractMethodNode(postInv, "listPlaceholderSimpleSuccess", repos)
				executeNode(listPlaceholderSimpleSuccess, repos, postInv) shouldBe true
				val listPlaceholderSimpleFail =
					classDecl.extractMethodNode(postInv, "listPlaceholderSimpleFail", repos)
				executeNode(listPlaceholderSimpleFail, repos, postInv) shouldBe false

				val maybePlaceholderSimpleSuccess =
					classDecl.extractMethodNode(postInv, "maybePlaceholderSimpleSuccess", repos)
				executeNode(maybePlaceholderSimpleSuccess, repos, postInv) shouldBe true
				val maybePlaceholderSimpleFail =
					classDecl.extractMethodNode(postInv, "maybePlaceholderSimpleFail", repos)
				executeNode(maybePlaceholderSimpleFail, repos, postInv) shouldBe false

				val listPlaceholdersSameNameMoreTypesSuccess =
					classDecl.extractMethodNode(postInv, "listPlaceholdersSameNameMoreTypesSuccess", repos)
				executeNode(listPlaceholdersSameNameMoreTypesSuccess, repos, postInv) shouldBe true


				val nestedPlaceholderPairSuccess =
					classDecl.extractMethodNode(postInv, "nestedPlaceholderPairSuccess", repos)
				executeNode(nestedPlaceholderPairSuccess, repos, postInv) shouldBe true

			}
		}
	}
}