import io.kotlintest.shouldBe
import org.abs_models.crowbar.main.*
import java.nio.file.Paths

class MathTest : CrowbarTest() {
    init {
        for (smt in listOf(z3, cvc)){
            if (!backendAvailable(smt)) continue
            println("testing with $smt as backend")

            "$smt absFunc"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/math.abs")))
                val classDecl = model.extractClassDecl("M", "C")

                val absEqSuccess = classDecl.extractMethodNode(postInv, "absEqSuccess", repos)
                executeNode(absEqSuccess, repos, postInv) shouldBe true
                //absPropSuccess
                val absFuncSuccess = classDecl.extractMethodNode(postInv, "absFuncSuccess", repos)
                executeNode(absFuncSuccess, repos, postInv) shouldBe true
                val absPropSuccess = classDecl.extractMethodNode(postInv, "absPropSuccess", repos)
                executeNode(absPropSuccess, repos, postInv) shouldBe true

            }

        }
    }
}