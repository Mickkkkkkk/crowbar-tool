@file:Suppress("KotlinDeprecation")

package org.abs_models.crowbar.main

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.groups.mutuallyExclusiveOptions
import com.github.ajalt.clikt.parameters.groups.required
import com.github.ajalt.clikt.parameters.groups.single
import com.github.ajalt.clikt.parameters.options.*
import com.github.ajalt.clikt.parameters.types.choice
import com.github.ajalt.clikt.parameters.types.int
import com.github.ajalt.clikt.parameters.types.path
import com.github.ajalt.clikt.parameters.types.restrictTo
import org.abs_models.crowbar.interfaces.filterAtomic
import org.abs_models.crowbar.types.LocalTypeType
import org.abs_models.crowbar.types.PostInvType
import org.abs_models.frontend.ast.*
import java.io.File
import java.nio.file.Files
import java.nio.file.Paths
import kotlin.system.exitProcess

enum class Verbosity { SILENT, NORMAL, V, VV, VVV }

var tmpPath = "/tmp/"
var smtPath  = "z3"
//var timeoutS  = 100
var verbosity = Verbosity.NORMAL
var investigate = false
var conciseProofs = false
var reportPath = "/tmp/report.csv"
var reporting = false

sealed class CrowOption{
    data class MethodOption(val path : String) : CrowOption()
    data class InitOption(val path : String) : CrowOption()
    data class AllClassOption(val path : String) : CrowOption()
    data class FunctionOption(val path : String) : CrowOption()
    object AllFunctionOption : CrowOption()
    object MainBlockOption : CrowOption()
    object FullOption : CrowOption()
}

class Main : CliktCommand() {
    private val filePath by argument(help="path to ABS file").path().multiple()

    //the casts in convert and validate are added to make the type checker happy
    private val target : CrowOption by mutuallyExclusiveOptions<CrowOption>(
        option("--method","-m",help="Verifies a single method <module>.<class>.<method>")
                .convert { CrowOption.MethodOption(it) as CrowOption }
                .validate { require((it as CrowOption.MethodOption).path.split(".").size == 3,
                    lazyMessage = {"invalid fully qualified method name $it"}) },
        option("--init","-i",help="Verifies the initial block of <module>.<class>")
                .convert {  CrowOption.InitOption(it) as CrowOption  }
                .validate { require((it as CrowOption.InitOption).path.split(".").size == 2,
                    lazyMessage = {"invalid fully qualified class name $it"}) },
        option("--class","-c",help="Verifies the initial block and all methods of <module>.<class>")
            .convert {  CrowOption.AllClassOption(it) as CrowOption }
            .validate { require((it as CrowOption.AllClassOption).path.split(".").size == 2,
                lazyMessage = {"invalid fully qualified class name $it"}) },
        option("--function","-f",help="Verifies the function <module>.<function> (experimental)")
            .convert {  CrowOption.FunctionOption(it) as CrowOption }
            .validate { require((it as CrowOption.FunctionOption).path.split(".").size == 2,
                lazyMessage = {"invalid fully qualified function name $it"}) },
        option(help="Verifies the main block of the model").switch("--main" to CrowOption.MainBlockOption),
        option(help="Verifies the full model").switch("--full" to CrowOption.FullOption)
    ).single().required()

    private val tmp        by   option("--tmp", "-t", help="Path to a directory used to store .smt and counterexample files").path().default(Paths.get(tmpPath))
    private val smtCmd     by   option("--smt", "-s", help="Command to start SMT solver").default(smtPath)
    private val verbose    by   option("--verbose", "-v", help="Verbosity output level").int().restrictTo(Verbosity.values().indices).default(Verbosity.NORMAL.ordinal)
    private val deductType by   option("--deduct", "-d", help="Used deductive system").choice("PostInv","LocalType").convert { when(it){"PostInv" -> PostInvType::class; "LocalType" -> LocalTypeType::class; else -> throw Exception(); } }.default(PostInvType::class)
    private val freedom    by   option("--freedom", "-fr", help="Performs a simple check for potentially deadlocking methods").flag()
    private val invFlag    by   option("--investigate", "-inv", help="Generate counterexamples for uncloseable branches").flag()
    private val conciseProofsFlag    by  option("--concise_proofs", "-cp", help="Generate concise proofs omitting unused declarations").flag()
    private val report        by   option("--report-path", "-rp", help="Path to a file used to store report of verification").path().default(Paths.get(reportPath))
    val reportFlag        by   option("--report", "-r", help="Path to a file used to store report of verification").flag()

    override fun run() {

        val start = System.currentTimeMillis()
        tmpPath = "$tmp/"
        smtPath = smtCmd
        verbosity = Verbosity.values()[verbose]
        investigate = invFlag
        conciseProofs = conciseProofsFlag
        reportPath = "$report"
        reporting = reportFlag

        if(!Files.exists(report) && reporting)
            File(reportPath).writeText("")

        if(investigate && deductType != PostInvType::class)
            output("Crowbar  : Counterexamples for types other than PostInv are not supported and may produce unexpected output", Verbosity.SILENT)

        val (model, repos) = load(filePath)
        //todo: check all VarDecls and Field Decls here
        //      no 'result', no 'heap', no '_f' suffix

        if(freedom) {
            val freedom = runFreeAnalysis(model)
            output("Crowbar  : Result of freedom analysis: $freedom", Verbosity.SILENT)
        }

        when(target){
            is  CrowOption.AllFunctionOption -> {
                System.err.println("option non implemented yet")
                exitProcess(-1)
            }
            is  CrowOption.FunctionOption -> {
                output("Crowbar  : This is an experimental feature and under development", Verbosity.SILENT)
                val tt = target as  CrowOption.FunctionOption
                val targetPath = tt.path.split(".")
                val funcDecl: FunctionDecl = model.extractFunctionDecl(targetPath[0], targetPath[1])
                val functionNode = funcDecl.exctractFunctionNode(deductType)
                val closed = executeNode(functionNode, repos, deductType)
                output("Crowbar  : Verification result: $closed", Verbosity.SILENT)
            }
            is  CrowOption.FullOption -> {
                var finalClose = true
                for( classDecl in model.extractAllClasses() ) {

                    val totalClosed =
                        if(!reportFlag) classDecl.executeAll(repos, deductType)
                        else classDecl.executeAllREPORT(repos, deductType)
                    output("Crowbar  : Verification result ${classDecl.qualifiedName}: $totalClosed\n", Verbosity.SILENT)
                    finalClose = finalClose && totalClosed
                }
                for( sNode in FunctionRepos.extractAll(deductType)){
                    val closed = executeNode(sNode.second, repos, deductType)
                    output("Crowbar  : Verification result ${sNode.first}: $closed\n", Verbosity.SILENT)
                    finalClose = finalClose && closed
                }
                val node = model.exctractMainNode(deductType)
                val closed = executeNode(node, repos, deductType)
                finalClose = finalClose && closed
                output("Crowbar  : Verification of main: $closed\n", Verbosity.SILENT)
                output("Crowbar  : Final verification result: $finalClose", Verbosity.SILENT)
                if(FunctionRepos.hasContracts()){
                    output("Crowbar  : Verification relies on functional contracts. This feature is experimental. To remove this warning, remove all specifications of function definitions.", Verbosity.SILENT)
                }
            }
            is  CrowOption.MainBlockOption -> {
                val node = model.exctractMainNode(deductType)
                val closed = executeNode(node, repos, deductType)
                output("Crowbar  : Verification result: $closed", Verbosity.SILENT)
            }
            is  CrowOption.AllClassOption -> {
                val tt = target as  CrowOption.AllClassOption
                val targetPath = tt.path.split(".")
                val classDecl = model.extractClassDecl(targetPath[0], targetPath[1])
                val totalClosed = classDecl.executeAll(repos, deductType)
                output("Crowbar  : Final verification result: $totalClosed", Verbosity.SILENT)
            }
            is  CrowOption.MethodOption -> {
                val tt = target as  CrowOption.MethodOption
                val targetPath = tt.path.split(".")
                val classDecl = model.extractClassDecl(targetPath[0], targetPath[1])
                val node = classDecl.extractMethodNode(deductType, targetPath[2],repos)
                val closed = executeNode(node, repos, deductType)
                output("Crowbar  : Verification result: $closed", Verbosity.SILENT)
            }
            is  CrowOption.InitOption -> {
                val tt = target as  CrowOption.InitOption
                val targetPath = tt.path.split(".")
                val classDecl = model.extractClassDecl(targetPath[0], targetPath[1])
                val node = classDecl.extractInitialNode(deductType)
                val closed = executeNode(node, repos, deductType)
                output("Crowbar  : Verification result: $closed", Verbosity.SILENT)
            }
        }
        val end = System.currentTimeMillis()
        output("Crowbar  : Verification time: ${end-start}ms", Verbosity.SILENT)
        output("Crowbar  : Total number of branches: $count", Verbosity.SILENT)
    }

    private fun runFreeAnalysis(model: Model) : Boolean{
        val mets = mutableListOf<MethodImpl>()
        val safemets = mutableListOf<MethodImpl>()
        val sigs = mutableListOf<MethodSig>()
        val safe = mutableListOf<MethodSig>()
        for(decl in model.moduleDecls){
            for(cDecl in decl.decls.filterIsInstance<ClassDecl>().map{it}){
                for(mImpl in cDecl.methods) {
                    if (decl.name.startsWith("ABS.")) {
                        safe.add(mImpl.methodSig)
                        safemets.add(mImpl)
                    } else {
                        mets.add(mImpl)
                        sigs.add(mImpl.methodSig)
                    }
                }
            }
        }
        safe.addAll(mets.filter { triviallyFree(it) }.map { it.methodSig })
        mets.removeAll(mets.filter { triviallyFree(it) }.toSet())
        sigs.removeAll (mets.filter { triviallyFree(it) }.map { it.methodSig }.toSet())
        output("Crowbar  : Potentially deadlocking methods: \n\t${mets.joinToString("\n\t") { it.contextDecl.name + "." + it.methodSig }}")
        return sigs.isEmpty()
    }

    private fun triviallyFree(methodImpl: MethodImpl) : Boolean{
        return filterAtomic(methodImpl.block) { (it is GetExp) || (it is AwaitStmt) }.isEmpty()
    }


}

fun main(args:Array<String>) = Main().main(args)