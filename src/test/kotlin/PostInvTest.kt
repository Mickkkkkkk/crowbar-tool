import io.kotlintest.shouldBe
import io.kotlintest.shouldThrow
import org.abs_models.crowbar.main.*
import java.nio.file.Paths

class PostInvTest : CrowbarTest() {
	init {
		"typeerror"{
			shouldThrow<Exception> {
				load(listOf(Paths.get("src/test/resources/exception.abs")))
			}
		}
		for (smt in listOf(z3, cvc)){
			if (!backendAvailable(smt)) continue
			println("testing with $smt as backend")

			"$smt float"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/float.abs")))
				val classDecl = model.extractClassDecl("M", "C")

				var res = classDecl.extractMethodNode(postInv, "success", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "fail", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "ticket271", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "ticket272", repos)
				executeNode(res, repos, postInv) shouldBe true
			}

			"$smt string"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/string.abs")))
				val classDecl = model.extractClassDecl("Strings", "C")
				var res = classDecl.extractMethodNode(postInv, "success", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "successFieldFloat", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "fail", repos)
				executeNode(res, repos, postInv) shouldBe false
			}

			"$smt random"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/random.abs")))
				val classDecl = model.extractClassDecl("Random", "C")

				var res = classDecl.extractMethodNode(postInv, "success", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "fail", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "failEq", repos)
				executeNode(res, repos, postInv) shouldBe false
			}

			"$smt account"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("examples/account.abs")))
				val classDecl = model.extractClassDecl("Account", "AccountImpl")

				var res = classDecl.extractMethodNode(postInv, "withdraw", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "deposit", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = model.exctractMainNode(postInv)
				executeNode(res, repos, postInv) shouldBe true

			}

			"$smt resolves"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/resolves.abs")))
				val classDecl = model.extractClassDecl("Resolve", "C")

				var res = classDecl.extractMethodNode(postInv, "success1", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "fail1", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "fail2", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "fail3", repos)
				executeNode(res, repos, postInv) shouldBe false
			}
			"$smt success"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/success.abs")))
				val classDecl = model.extractClassDecl("Success", "C")
				classDecl.executeAll(repos, postInv) shouldBe true
			}
			"$smt types"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/types.abs")))
				val classDecl = model.extractClassDecl("Types", "C")

				val iNode = classDecl.extractInitialNode(postInv)
				executeNode(iNode, repos, postInv) shouldBe true

				val sNode = classDecl.extractMethodNode(postInv, "m", repos)
				executeNode(sNode, repos, postInv) shouldBe true

				val fNode = classDecl.extractMethodNode(postInv, "m2", repos)
				executeNode(fNode, repos, postInv) shouldBe false
			}

			"$smt ints"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/ints.abs")))
				val classDecl = model.extractClassDecl("Ints", "C")
				classDecl.executeAll(repos, postInv) shouldBe true

				val mNode = model.exctractMainNode(postInv)
				executeNode(mNode, repos, postInv) shouldBe true
			}

			"$smt guards"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/guards.abs")))
				val classDecl = model.extractClassDecl("Guard", "C")

				val m1Node = classDecl.extractMethodNode(postInv, "msucc", repos)
				executeNode(m1Node, repos, postInv) shouldBe true

				val m2Node = classDecl.extractMethodNode(postInv, "mfail", repos)
				executeNode(m2Node, repos, postInv) shouldBe false
			}

			"$smt fails"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/fail.abs")))
				val classDecl = model.extractClassDecl("Fail", "C")

				val iNode = classDecl.extractInitialNode(postInv)
				executeNode(iNode, repos, postInv) shouldBe false

				for (m in classDecl.methods) {
					val node = classDecl.extractMethodNode(postInv, m.methodSig.name, repos)
					executeNode(node, repos, postInv) shouldBe false
				}
				val classDecl2 = model.extractClassDecl("Fail", "D")
				val node2 = classDecl2.extractMethodNode(postInv, "failure", repos)
				executeNode(node2, repos, postInv) shouldBe false
			}

			"$smt create"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/create.abs")))
				val classDecl = model.extractClassDecl("Create", "C")

				val iNode = classDecl.extractInitialNode(postInv)
				executeNode(iNode, repos, postInv) shouldBe true

				val sNode = classDecl.extractMethodNode(postInv, "success", repos)
				executeNode(sNode, repos, postInv) shouldBe true

				val fNode = classDecl.extractMethodNode(postInv, "fail", repos)
				executeNode(fNode, repos, postInv) shouldBe false

				val mNode = model.exctractMainNode(postInv)
				executeNode(mNode, repos, postInv) shouldBe true
			}

			"$smt reference"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/reference.abs")))
				val classDecl = model.extractClassDecl("Reference", "C")

				val iNode = classDecl.extractInitialNode(postInv)
				executeNode(iNode, repos, postInv) shouldBe true

				val m1Node = classDecl.extractMethodNode(postInv, "m1", repos)
				executeNode(m1Node, repos, postInv) shouldBe false

				val m2Node = classDecl.extractMethodNode(postInv, "m2", repos)
				executeNode(m2Node, repos, postInv) shouldBe false //see comment in file

				val m3Node = classDecl.extractMethodNode(postInv, "m3", repos)
				executeNode(m3Node, repos, postInv) shouldBe true

				val m4Node = classDecl.extractMethodNode(postInv, "m4", repos)
				executeNode(m4Node, repos, postInv) shouldBe true

				val mNode = model.exctractMainNode(postInv)
				executeNode(mNode, repos, postInv) shouldBe false
			}

			"$smt multi"{
				smtPath = smt
				val (model, repos) = load(
					listOf(
						Paths.get("src/test/resources/multi1.abs"),
						Paths.get("src/test/resources/multi2.abs")
					)
				)
				val classDecl = model.extractClassDecl("Multi1", "C")
				classDecl.executeAll(repos, postInv) shouldBe true

				val mNode = model.exctractMainNode(postInv)
				executeNode(mNode, repos, postInv) shouldBe true
			}

			"$smt callsuccess"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/callsimplesuccess.abs")))
				val classDeclC = model.extractClassDecl("CallS", "C")
				classDeclC.executeAll(repos, postInv) shouldBe true
				val classDeclD = model.extractClassDecl("CallS", "D")
				classDeclD.executeAll(repos, postInv) shouldBe true
				val classDeclE = model.extractClassDecl("CallS", "E")
				classDeclE.executeAll(repos, postInv) shouldBe true
				val mNode = model.exctractMainNode(postInv)
				executeNode(mNode, repos, postInv) shouldBe true
			}

			"$smt callfail"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/callsimplefail.abs")))
				val classDeclC = model.extractClassDecl("CallF", "C")
				val m0Node = classDeclC.extractMethodNode(postInv, "m", repos)
				executeNode(m0Node, repos, postInv) shouldBe false
				val classDeclD = model.extractClassDecl("CallF", "D")
				val m1Node = classDeclD.extractMethodNode(postInv, "m", repos)
				executeNode(m1Node, repos, postInv) shouldBe false
				val classDeclE = model.extractClassDecl("CallF", "E")
				val m2Node = classDeclE.extractMethodNode(postInv, "m", repos)
				executeNode(m2Node, repos, postInv) shouldBe false
				val mNode = model.exctractMainNode(postInv)
				executeNode(mNode, repos, postInv) shouldBe false
			}

			"$smt failinher"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/callfailinherited.abs")))
				val classDeclC = model.extractClassDecl("Call", "C")
				val m0Node = classDeclC.extractMethodNode(postInv, "fail", repos)
				executeNode(m0Node, repos, postInv) shouldBe false
			}

			"$smt selfcall"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/selfcall.abs")))
				val classDecl = model.extractClassDecl("Self", "C")
				val m0Node = classDecl.extractMethodNode(postInv, "n", repos)
				executeNode(m0Node, repos, postInv) shouldBe true
				val m1Node = classDecl.extractMethodNode(postInv, "m", repos)
				executeNode(m1Node, repos, postInv) shouldBe true
				val m2Node = classDecl.extractMethodNode(postInv, "m2", repos)
				executeNode(m2Node, repos, postInv) shouldBe false
				val mNode = model.exctractMainNode(postInv)
				executeNode(mNode, repos, postInv) shouldBe true
			}

			"$smt valueof"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/valueof.abs")))
				val classDecl = model.extractClassDecl("Values", "C")

				val iNode = classDecl.extractInitialNode(postInv)
				executeNode(iNode, repos, postInv) shouldBe true

				var sNode = classDecl.extractMethodNode(postInv, "success", repos)
				executeNode(sNode, repos, postInv) shouldBe true

				sNode = classDecl.extractMethodNode(postInv, "readToField", repos)
				executeNode(sNode, repos, postInv) shouldBe true

				sNode = classDecl.extractMethodNode(postInv, "internal", repos)
				executeNode(sNode, repos, postInv) shouldBe true

				sNode = classDecl.extractMethodNode(postInv, "fail", repos)
				executeNode(sNode, repos, postInv) shouldBe false

				sNode = classDecl.extractMethodNode(postInv, "valueOfBoolFutSuccess", repos)
				executeNode(sNode, repos, postInv) shouldBe true
			}

			"$smt ensures-this"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/ensures.abs")))
				val classDecl = model.extractClassDecl("ThisCalls", "C")

				val iNode = classDecl.extractInitialNode(postInv)
				executeNode(iNode, repos, postInv) shouldBe true

				var sNode = classDecl.extractMethodNode(postInv, "one", repos)
				executeNode(sNode, repos, postInv) shouldBe true

				sNode = classDecl.extractMethodNode(postInv, "pos", repos)
				executeNode(sNode, repos, postInv) shouldBe true

				sNode = classDecl.extractMethodNode(postInv, "callOneOnThis", repos)
				executeNode(sNode, repos, postInv) shouldBe true

				sNode = classDecl.extractMethodNode(postInv, "callOneIndirectlyOnThis", repos)
				executeNode(sNode, repos, postInv) shouldBe true

				sNode = classDecl.extractMethodNode(postInv, "callOneOnOther", repos)
				executeNode(sNode, repos, postInv) shouldBe true

				sNode = classDecl.extractMethodNode(postInv, "failOneOnThis", repos)
				executeNode(sNode, repos, postInv) shouldBe false
			}

			"$smt paramensures"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/params.abs")))
				var classDecl = model.extractClassDecl("ParamCalls", "C")

				var sNode = classDecl.extractMethodNode(postInv, "firstArg", repos)
				executeNode(sNode, repos, postInv) shouldBe true

				sNode = classDecl.extractMethodNode(postInv, "fail", repos)
				executeNode(sNode, repos, postInv) shouldBe false


				classDecl = model.extractClassDecl("ParamCalls", "D")

				sNode = classDecl.extractMethodNode(postInv, "succ", repos)
				executeNode(sNode, repos, postInv) shouldBe true

				sNode = classDecl.extractMethodNode(postInv, "succZero", repos)
				executeNode(sNode, repos, postInv) shouldBe true
			}

			"$smt fieldvarclash"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/fieldvarclash.abs")))
				val classDecl = model.extractClassDecl("FieldVarClash", "C")
				classDecl.executeAll(repos, postInv) shouldBe true

				val mNode = model.exctractMainNode(postInv)
				executeNode(mNode, repos, postInv) shouldBe true
			}

			"$smt recidentity"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/identity.abs")))
				val classDecl = model.extractClassDecl("Iden", "C")

				var sNode = classDecl.extractMethodNode(postInv, "id", repos)
				executeNode(sNode, repos, postInv) shouldBe true

				sNode = classDecl.extractMethodNode(postInv, "nid", repos)
				executeNode(sNode, repos, postInv) shouldBe false

				sNode = classDecl.extractMethodNode(postInv, "nnid", repos)
				executeNode(sNode, repos, postInv) shouldBe false
			}

			"$smt examples"{
				smtPath = smt
				var (model, repos) = load(listOf(Paths.get("examples/c2abs.abs")))
				var classDecl = model.extractClassDecl("TestModule", "C_main")
				classDecl.executeAll(repos, postInv) shouldBe true

				classDecl = model.extractClassDecl("TestModule", "Global")
				classDecl.executeAll(repos, postInv) shouldBe true

				classDecl = model.extractClassDecl("TestModule", "C_set_x")
				classDecl.executeAll(repos, postInv) shouldBe true

				var mNode = model.exctractMainNode(postInv)
				executeNode(mNode, repos, postInv) shouldBe true

				var any = load(listOf(Paths.get("examples/gcd.abs")))
				model = any.first
				repos = any.second
				classDecl = model.extractClassDecl("CallS", "GcdC")
				classDecl.executeAll(repos, postInv) shouldBe true

				classDecl = model.extractClassDecl("CallS", "LogC")
				classDecl.executeAll(repos, postInv) shouldBe true

				mNode = model.exctractMainNode(postInv)
				executeNode(mNode, repos, postInv) shouldBe true

				any = load(listOf(Paths.get("examples/gcdfield.abs")))
				model = any.first
				repos = any.second
				classDecl = model.extractClassDecl("CallSField", "GcdC")
				classDecl.executeAll(repos, postInv) shouldBe true

				mNode = model.exctractMainNode(postInv)
				executeNode(mNode, repos, postInv) shouldBe true

				any = load(listOf(Paths.get("examples/one_to_fib_n.abs")))
				model = any.first
				repos = any.second

				classDecl = model.extractClassDecl("TestModule", "Global")
				classDecl.executeAll(repos, postInv) shouldBe true

				classDecl = model.extractClassDecl("TestModule", "C_set_x")
				classDecl.executeAll(repos, postInv) shouldBe true

				classDecl = model.extractClassDecl("TestModule", "C_two_unspec")
				classDecl.executeAll(repos, postInv) shouldBe true

				classDecl = model.extractClassDecl("TestModule", "C_add_zero")
				classDecl.executeAll(repos, postInv) shouldBe true

				classDecl = model.extractClassDecl("TestModule", "C_one_to_fib_n")
				classDecl.executeAll(repos, postInv) shouldBe true

				mNode = model.exctractMainNode(postInv)
				executeNode(mNode, repos, postInv) shouldBe true
			}

			"$smt functional"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/func.abs")))
				val classDecl = model.extractClassDecl("Func", "C")

				var sNode = classDecl.extractMethodNode(postInv, "m", repos)
				executeNode(sNode, repos, postInv) shouldBe true

				sNode = classDecl.extractMethodNode(postInv, "n", repos)
				executeNode(sNode, repos, postInv) shouldBe false
			}

			"$smt synccall"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/synccall.abs")))
				val classDecl = model.extractClassDecl("SyncCall", "SyncCallC")

				//empty contract for sync call
				val emptyContractSyncCallSuccessNode =
					classDecl.extractMethodNode(postInv, "emptyContractSuccess", repos)
				executeNode(emptyContractSyncCallSuccessNode, repos, postInv) shouldBe true
				//simple fail for sync call
				val simpleSyncCallFail = classDecl.extractMethodNode(postInv, "simpleSyncCallFail", repos)
				executeNode(simpleSyncCallFail, repos, postInv) shouldBe false
				//simple success for sync call
				val simpleSyncCallSuccess = classDecl.extractMethodNode(postInv, "simpleSyncCallSuccess", repos)
				executeNode(simpleSyncCallSuccess, repos, postInv) shouldBe true

				val simpleDirectReturnSyncCallSuccess = classDecl.extractMethodNode(postInv, "simpleDirectReturnSyncCallSuccess", repos)
				executeNode(simpleDirectReturnSyncCallSuccess, repos, postInv) shouldBe true

				//simple success for sync call with inherited contracts
				val syncCallInheritedSuccess = classDecl.extractMethodNode(postInv, "syncCallInheritedSuccess", repos)
				executeNode(syncCallInheritedSuccess, repos, postInv) shouldBe true

				//simple success for sync call with complex inherited contracts
				val syncCallComplexInheritedSuccess =
					classDecl.extractMethodNode(postInv, "syncCallComplexInheritedSuccess", repos)
				executeNode(syncCallComplexInheritedSuccess, repos, postInv) shouldBe true

				//simple success for sync call with complex inherited contracts
				val updateFieldSuccess = classDecl.extractMethodNode(postInv, "updateFieldSuccess", repos)
				executeNode(updateFieldSuccess, repos, postInv) shouldBe true
			}

			"$smt unexposedcontract"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/unexposedcontract.abs")))
				val classDecl = model.extractClassDecl("UnexposedContract", "UnexposedContractC")

				val unexposedContractFail = classDecl.extractMethodNode(postInv, "unexposedContractFail", repos)
				executeNode(unexposedContractFail, repos, postInv) shouldBe false

				val unexposedContractSuccess = classDecl.extractMethodNode(postInv, "unexposedContractSuccess", repos)
				executeNode(unexposedContractSuccess, repos, postInv) shouldBe true
			}

			"$smt syncField"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/syncField.abs")))
				val classDecl = model.extractClassDecl("TargetField", "C")

				val unexposedContractFail = classDecl.extractMethodNode(postInv, "m", repos)
				executeNode(unexposedContractFail, repos, postInv) shouldBe true
			}

			"$smt suspend"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/suspend.abs")))
				val classDecl = model.extractClassDecl("Susp", "C")

				var res = classDecl.extractMethodNode(postInv, "m1", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "m2", repos)
				executeNode(res, repos, postInv) shouldBe false
			}

			/*"$smt nullable"{
			smtPath = smt
			val (model, repos) = load(listOf(Paths.get("src/test/resources/nullable.abs")))
			val classDecl = model.extractClassDecl("Nullable", "K")

			val res = classDecl.extractMethodNode(postInv,"m", repos)
			executeNode(res, repos, postInv) shouldBe true
		}*/ //TODO: disabled until Daniel's version is merged

			"$smt assert"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/assert.abs")))
				val classDecl = model.extractClassDecl("Assert", "C")

				var res = classDecl.extractMethodNode(postInv, "fail1", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "fail2", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "fail3", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "success1", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "success2", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "success3", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "success4", repos)
				executeNode(res, repos, postInv) shouldBe true
			}
			"$smt divByZero"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/divByZero.abs")))
				val classDecl = model.extractClassDecl("DivByZero", "C")

				var res = classDecl.extractMethodNode(postInv, "fail1", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "fail2", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "fail3", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "fail4", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "success1", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "success2", repos)
				executeNode(res, repos, postInv) shouldBe true
			}
			"$smt let"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/let.abs")))
				val classDecl = model.extractClassDecl("Let", "C")

				var res = classDecl.extractMethodNode(postInv, "fail1", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "fail2", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "fail3", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "fail4", repos)
				executeNode(res, repos, postInv) shouldBe false
				res = classDecl.extractMethodNode(postInv, "success1", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "success2", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "success3", repos)
				executeNode(res, repos, postInv) shouldBe true
				res = classDecl.extractMethodNode(postInv, "success4", repos)
				executeNode(res, repos, postInv) shouldBe true
			}
		}
	}
}