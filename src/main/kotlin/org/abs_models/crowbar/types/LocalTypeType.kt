package org.abs_models.crowbar.types

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.AssignStmt
import org.abs_models.crowbar.data.AwaitStmt
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.data.IfStmt
import org.abs_models.crowbar.data.ReturnStmt
import org.abs_models.crowbar.data.SkipStmt
import org.abs_models.crowbar.data.Stmt
import org.abs_models.crowbar.data.WhileStmt
import org.abs_models.crowbar.interfaces.LocalTypeParser
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.rule.FreshGenerator
import org.abs_models.crowbar.rule.MatchCondition
import org.abs_models.crowbar.rule.Rule
import org.abs_models.crowbar.tree.*
import org.abs_models.frontend.ast.*
import org.abs_models.frontend.typechecker.Type
import org.abs_models.frontend.typechecker.UnknownType
import kotlin.system.exitProcess

// Declaration
interface LocalTypeType : DeductType {
    companion object : LocalTypeType

    fun emptySymNode(): SymbolicNode {
        val emptySymState = SymbolicState(True, EmptyUpdate, Modality(SkipStmt, LocalTypeTarget(LTSkip, True)), listOf())
        return SymbolicNode(emptySymState, listOf())
    }

    override fun extractMethodNode(classDecl: ClassDecl, name: String, repos: Repository): SymbolicNode {
        val mDecl = classDecl.methods.firstOrNull { it.methodSig.name == name }
        if (mDecl == null) {
            if(reporting) throw Exception("method not found: ${classDecl.qualifiedName}.$name")
            System.err.println("method not found: ${classDecl.qualifiedName}.$name")
            exitProcess(-1)
        }

        output("Crowbar  : loading specification....")
        val symb: SymbolicState?
        val objInv: Formula?
        val ltexp: LocalType?
        val metpre: Formula?
        val roles: Formula?
        val body: Stmt?

        val context = getParseContext(mDecl, classDecl)

        try {
            objInv = extractSpec(classDecl, "ObjInv", UnknownType.INSTANCE)
            ltexp = extractLocalTypeSpec(mDecl, context)
            metpre = extractInheritedSpec(mDecl.methodSig, "Requires")
            body = getNormalizedStatement(mDecl.block)
            roles = extractRoleSpec(classDecl)
        } catch (e: Exception) {
            if(reporting) reportException("error during translation, aborting:", e)
            e.printStackTrace()
            System.err.println("error during translation, aborting")
            exitProcess(-1)
        }
        output("Crowbar-v: method local type expression: ${ltexp?.prettyPrint() ?: "null"}", Verbosity.V)

        // We have nothing to show if the method has no LocalType annotation
        if (ltexp == null)
            return emptySymNode()

        val updateOldHeap = ChainUpdate(ElementaryUpdate(LastHeap, Heap), ElementaryUpdate(OldHeap, Heap))
        symb = SymbolicState(And(And(objInv, metpre), roles), updateOldHeap, Modality(body, LocalTypeTarget(ltexp, roles, objInv)), listOf())

        val usedSpec = StaticNode("Using specification of ${classDecl.qualifiedName}.$name:\nObject Invariant: ${objInv.prettyPrint()}\nRequires: ${metpre.prettyPrint()}")

        return if (objInv != True || metpre != True)
                SymbolicNode(symb, listOf(usedSpec, SymbolicNode(symb, emptyList())))
            else
                SymbolicNode(symb, listOf())
    }

    fun getParseContext(mDecl: MethodImpl, cDecl: ClassDecl): Pair<Type, Map<String, Type>> {
        val returnType = mDecl.type
        val fields = cDecl.fields.map {
            Pair(it.name, it.type)
        }
        val params = cDecl.params.map {
            Pair(it.name, it.type)
        }
        val mapping = (fields + params).associate { it }
        return Pair(returnType, mapping)
    }

    fun extractLocalTypeSpec(mDecl: MethodImpl, context: Pair<Type, Map<String, Type>>?): LocalType? {
        val annotations = mDecl.methodSig.nodeAnnotations.filter {
            it.type.toString().endsWith(".Spec") && it.value is DataConstructorExp && (it.value as DataConstructorExp).constructor == "Local"
        }.map { it.value as DataConstructorExp }

        return when (annotations.size) {
            0 -> null
            1 -> LocalTypeParser.parse((annotations[0].getParam(0) as StringLiteral).content, context)
            else -> throw Exception("Cannot have more than one Local annotation per method (at method ${mDecl.methodSig.name})")
        }
    }

    override fun extractInitialNode(classDecl: ClassDecl): SymbolicNode {
        // Collect all local type annotations
        val methods = classDecl.methods.joinToString("\n") {
            val lte = extractLocalTypeSpec(it, null)
            "${classDecl.name}.${it.methodSig.name}: ${lte?.prettyPrint() ?: "no local type annotation"}"
        }

        val emptySymState = SymbolicState(True, EmptyUpdate, Modality(SkipStmt, LocalTypeTarget(LTSkip, True)), listOf())

        return SymbolicNode(emptySymState, listOf(StaticNode("Expected projection result:\n$methods")))
    }

    override fun exctractMainNode(model: Model) = emptySymNode()

    override fun exctractFunctionNode(fDecl: FunctionDecl) = emptySymNode()
}

data class LocalTypeTarget(val lte: LocalType, val roleInv: Formula, val invariant: Formula = True, val showInvariant: Boolean = false) : LocalTypeType {
    override fun prettyPrint() = lte.prettyPrint()

    fun updateLTE(newLte: LocalType) = LocalTypeTarget(newLte, roleInv, invariant, showInvariant)
}

data class LocalTypeAbstractTarget(val name: String) : LocalTypeType, AbstractVar {
    override fun prettyPrint(): String {
        return name
    }
}

abstract class LTTAssign(protected val repos: Repository, conclusion: Modality) : Rule(conclusion) {

    protected fun assignFor(loc: Location, rhs: Term): ElementaryUpdate {
        return if (loc is Field)
            ElementaryUpdate(Heap, store(loc, rhs))
        else
            ElementaryUpdate(loc as ProgVar, rhs)
    }

    protected fun symbolicNext(loc: Location, rhs: Term, remainder: Stmt, target: DeductType, iForm: Formula, iUp: UpdateElement, infoObj: NodeInfo): SymbolicNode {
        return SymbolicNode(SymbolicState(
            iForm,
            ChainUpdate(iUp, assignFor(loc, rhs)),
            Modality(remainder, target)
            , listOf()), info = infoObj)
    }
}

// Type system
class LTTLocAssign(repos: Repository) : LTTAssign(repos, Modality(
    SeqStmt(AssignStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR")), StmtAbstractVar("CONT")),
    LocalTypeAbstractTarget("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val rhsExpr = cond.map[ExprAbstractVar("EXPR")] as Expr
        val rhs = exprToTerm(rhsExpr)
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[LocalTypeAbstractTarget("TYPE")] as DeductType
        val info = InfoLocAssign(lhs, rhsExpr)
        return listOf(symbolicNext(lhs, rhs, remainder, target, input.condition, input.update, info))
    }
}

class LTTSyncAssign(repos: Repository) : LTTAssign(repos, Modality(
    SeqStmt(SyncStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR"), AbstractStringSet("RESOLVE"), PPAbstractVar("PP")),
        StmtAbstractVar("CONT")),
    LocalTypeAbstractTarget("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val rhsExpr = cond.map[ExprAbstractVar("EXPR")] as SExpr
        val rhs = exprToTerm(rhsExpr)
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[LocalTypeAbstractTarget("TYPE")] as LocalTypeTarget
        val ltexp = target.lte

        // We're executing a get statement here which has to match the local type specification
        if (!ltexp.matches(LTPatternGet)) {
            output("Crowbar  : bailing out, could not match .get to $ltexp")
            return listOf()
        }

        // Side condition: Show that the term we sync on is equivalent to the specified one (handled in readTransform)
        val context = LTGetContext(input.condition, input.update, rhsExpr.e[0]) // rhsExpr is valueOf(<get term>)
        val newTarget = target.updateLTE(ltexp.readTransform(LTPatternGet, context))

        // Generate SMT representation of the future expression to get its model value later
        val futureSMTExpr = apply(input.update, rhs) as Term
        val info = InfoGetAssign(lhs, rhsExpr, futureSMTExpr)

        return listOf(symbolicNext(lhs, rhs, remainder, newTarget, input.condition, input.update, info))
    }
}

class LTTAllocAssign(repos: Repository) : LTTAssign(repos, Modality(
    SeqStmt(AllocateStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR")),
        StmtAbstractVar("CONT")),
    LocalTypeAbstractTarget("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val rhsExpr = cond.map[ExprAbstractVar("EXPR")] as Expr
        val rhs = exprToTerm(rhsExpr) as Function
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[LocalTypeAbstractTarget("TYPE")] as DeductType

        val nextRhs = Function(rhs.name, rhs.params.subList(1, rhs.params.size))

        // Generate SMT representation of the NEW expression to get its model value later
        val constructorSMTExpr = apply(input.update, nextRhs).toSMT()

        val next = symbolicNext(lhs,
                                nextRhs,
                                remainder,
                                target,
                                And(input.condition, UpdateOnFormula(input.update, Not(Predicate("=", listOf(nextRhs, Function("0")))))),
                                ChainUpdate(input.update, assignFor(lhs, nextRhs)),
                                InfoObjAlloc(lhs, rhsExpr, constructorSMTExpr))

        return listOf(next)
    }
}

class LTTCallAssign(repos: Repository) : LTTAssign(repos, Modality(
    SeqStmt(CallStmt(LocationAbstractVar("LHS"), ExprAbstractVar("CALLEE"), CallExprAbstractVar("CALL")),
        StmtAbstractVar("CONT")),
    LocalTypeAbstractTarget("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val calleeExpr = cond.map[ExprAbstractVar("CALLEE")] as Expr
        val callee = exprToTerm(calleeExpr)
        val call = cond.map[CallExprAbstractVar("CALL")] as CallExpr
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[LocalTypeAbstractTarget("TYPE")] as LocalTypeTarget

        // Check that receiving object is non-null
        val isNonNull = false //calleeExpr.absExp?.nonNull() ?: false // call might already be non-null asserted by typechecker
        val notNullCondition = Not(Predicate("=", listOf(callee, Function("0", emptyList()))))
        val nonenull = LogicNode(
            input.condition,
            UpdateOnFormula(input.update, notNullCondition),
            info = InfoNullCheck(notNullCondition)
        )

        // We're executing a call here which has to match the local type specification
        val ltexp = target.lte
        val callPattern = LTPatternCall(call.met.split(".").last())
        if (!ltexp.matches(callPattern)) {
            output("Crowbar  : bailing out, could not match call $callPattern to $ltexp")
            return listOf()
        }

        // Collect mapping from parameter names to instantiated expressions
        val targetDecl = repos.methodReqs.getValue(call.met).second
        val substMap = mutableMapOf<LogicElement, LogicElement>()
        for (i in 0 until targetDecl.numParam) {
            val pName = ProgVar(
                targetDecl.getParam(i).name,
                targetDecl.getParam(i).type
            )
            val pValue = exprToTerm(call.e[i])
            substMap[pName] = pValue
        }

        // Side conditions handled in readTransform:
        // - Show that role of callee matches specified role
        // - Show that specified call precondition is met
        val context = LTCallContext(input.condition, input.update, calleeExpr, substMap)
        val newTarget = target.updateLTE(ltexp.readTransform(callPattern, context))

        val freshFut = FreshGenerator.getFreshFuture(targetDecl.type)
        val read = repos.methodEnss[call.met]
        val postCond = read?.first ?: True

        val targetPostDecl = read!!.second
        val substPostMap = mutableMapOf<LogicElement, LogicElement>()
        for (i in 0 until targetDecl.numParam) {
            val pName = ProgVar(targetPostDecl.getParam(i).name, targetPostDecl.getParam(i).type)
            val pValue = exprToTerm(call.e[i])
            substPostMap[pName] = pValue
        }
        val substPostCond = subst(postCond, substPostMap) as Formula
        val updateNew = ElementaryUpdate(ReturnVar(targetDecl.type), valueOfFunc(freshFut))

        val next = symbolicNext(lhs,
                                freshFut,
                                remainder,
                                newTarget,
                                And(input.condition, UpdateOnFormula(input.update, UpdateOnFormula(updateNew, substPostCond))),
                                input.update,
                                InfoCallAssign(lhs, calleeExpr, call, freshFut.name))

        val children = mutableListOf<SymbolicTree>(next)

        if (!isNonNull)
            children.add(nonenull)

        // Create static node if we used a non-trivial postcondition
        if (postCond != True)
            children.add(StaticNode("Using postcondition of method ${call.met}: ${postCond.prettyPrint()}"))

        return children
    }
}

object LTTSkip : Rule(Modality(SkipStmt, LocalTypeAbstractTarget("TARGET"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val target = cond.map[LocalTypeAbstractTarget("TARGET")] as LocalTypeTarget

        // There's nothing left to execute.
        // If the remaining local type expression does not require any further actions,
        // the proof was successful. If not, it failed.
        if (!target.lte.couldSkip) {
            output("Crowbar  : bailing out, program execution completed but expected actions remain: ${target.lte}")
            return listOf()
        }

        val sideconditions = target.lte.sideConditions.toMutableList()

        // We may have to show an invariant here (e.g. for loop invariant preservation)
        if (target.showInvariant)
            sideconditions.add(LogicNode(input.condition, apply(input.update, target.invariant) as Formula))

        // Show that roles are preserved
        sideconditions.add(LogicNode(input.condition, UpdateOnFormula(input.update, target.roleInv)))

        return sideconditions
    }
}

object LTTSkipSkip : Rule(Modality(
        SeqStmt(SkipStmt, StmtAbstractVar("CONT")),
        LocalTypeAbstractTarget("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[LocalTypeAbstractTarget("TYPE")] as DeductType
        val res = SymbolicNode(SymbolicState(input.condition, input.update, Modality(cont, target), listOf()), info = InfoSkip())
        return listOf(res)
    }
}

object LTTScopeSkip : Rule(Modality(
        SeqStmt(ScopeMarker, StmtAbstractVar("CONT")),
        LocalTypeAbstractTarget("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[LocalTypeAbstractTarget("TYPE")] as DeductType
        val res = SymbolicNode(SymbolicState(input.condition, input.update, Modality(cont, target), listOf()), info = InfoScopeClose())
        return listOf(res)
    }
}

object LTTReturn : Rule(Modality(
        ReturnStmt(ExprAbstractVar("RET")),
        LocalTypeAbstractTarget("TARGET"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val target = cond.map[LocalTypeAbstractTarget("TARGET")] as LocalTypeTarget
        val retExpr = cond.map[ExprAbstractVar("RET")] as Expr
        val ret = exprToTerm(retExpr)
        val typeReturn = getReturnType(ret)

        // We're executing a return statement here which has to match the local type specification
        val ltexp = target.lte
        if (!ltexp.matches(LTPatternPut)) {
            output("Crowbar  : bailing out, could not match return to $ltexp")
            return listOf()
        }

        // Sidecondition handled in readTransform: specified postcondition must hold
        val newUpdate = ChainUpdate(input.update, ElementaryUpdate(ReturnVar(typeReturn), ret))
        val context = LTCommonContext(input.condition, newUpdate)
        val newTargetExp = ltexp.readTransform(LTPatternPut, context)

        // We can't have un-matched parts of the local type expression remaining when finishing execution
        if (!newTargetExp.couldSkip) {
            output("Crowbar  : bailing out, finished execution but pattern is not skippable: $newTargetExp")
            return listOf()
        }

        // Collect all used sideconditions
        val sideconditions = newTargetExp.sideConditions.toMutableList()

        // Show the target invariant as well if requested
        // I don't think this is ever used for return statements, but we might as well support it
        if (target.showInvariant)
            sideconditions.add(LogicNode(input.condition, UpdateOnFormula(newUpdate, target.invariant)))

        // Show that roles are preserved
        sideconditions.add(LogicNode(input.condition, UpdateOnFormula(newUpdate, target.roleInv)))

        return sideconditions
    }
}

object LTTIf : Rule(Modality(
        SeqStmt(IfStmt(ExprAbstractVar("LHS"), StmtAbstractVar("THEN"), StmtAbstractVar("ELSE")),
                StmtAbstractVar("CONT")),
        LocalTypeAbstractTarget("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {

        val contBody = SeqStmt(ScopeMarker, cond.map[StmtAbstractVar("CONT")] as Stmt) // Add a ScopeMarker statement to detect scope closure
        val guardExpr = cond.map[ExprAbstractVar("LHS")] as Expr

        // then
        val guardYes = exprToForm(guardExpr)
        val bodyYes = SeqStmt(cond.map[StmtAbstractVar("THEN")] as Stmt, contBody)
        val updateYes = input.update
        val typeYes = cond.map[LocalTypeAbstractTarget("TYPE")] as DeductType
        val resThen = SymbolicState(And(input.condition, UpdateOnFormula(updateYes, guardYes)), updateYes, Modality(bodyYes, typeYes), listOf())

        // else
        val guardNo = Not(exprToForm(guardExpr))
        val bodyNo = SeqStmt(cond.map[StmtAbstractVar("ELSE")] as Stmt, contBody)
        val updateNo = input.update
        val typeNo = cond.map[LocalTypeAbstractTarget("TYPE")] as DeductType
        val resElse = SymbolicState(And(input.condition, UpdateOnFormula(updateNo, guardNo)), updateNo, Modality(bodyNo, typeNo), listOf())
        return listOf(SymbolicNode(resThen, info = InfoIfThen(guardExpr)), SymbolicNode(resElse, info = InfoIfElse(guardExpr)))
    }
}

object LTTAwait : Rule(Modality(
        SeqStmt(AwaitStmt(ExprAbstractVar("GUARD"), PPAbstractVar("PP")), StmtAbstractVar("CONT")),
        LocalTypeAbstractTarget("TARGET"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val guardExpr = cond.map[ExprAbstractVar("GUARD")] as Expr
        val guard = exprToForm(guardExpr)
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[LocalTypeAbstractTarget("TARGET")] as LocalTypeTarget

        // Generate SMT representation of the anonymized heap for future heap reconstruction
        val anonHeapExpr = apply(ChainUpdate(input.update, ElementaryUpdate(Heap, anon(Heap))), Heap) as Term

        val objInvariant = target.invariant
        val updateLastHeap = ElementaryUpdate(LastHeap, Heap)
        val newUpdate = ChainUpdate(input.update, ChainUpdate(ElementaryUpdate(Heap, anon(Heap)), updateLastHeap))
        val newInputCondition = And(
                        input.condition,
                        UpdateOnFormula(
                            newUpdate,
                            And(objInvariant, And(guard, target.roleInv))
                        )
                    )

        // We're executing an await statement here which has to match the local type specification
        val ltexp = target.lte
        if (!ltexp.matches(LTPatternSusp)) {
            output("Crowbar  : bailing out, could not match suspend to $ltexp")
            return listOf()
        }

        // Sidecondition handled in readTransform: specified precondition has to hold
        val context = LTCommonContext(input.condition, input.update)
        val newTarget = target.updateLTE(ltexp.readTransform(LTPatternSusp, context))

        val sState = SymbolicState(newInputCondition, newUpdate, Modality(cont, newTarget), listOf())

        return listOf(SymbolicNode(sState, info = InfoAwaitUse(guardExpr, anonHeapExpr)))
    }
}

// warning: this is the throwaway variant of loop invariants
object LTTWhile : Rule(Modality(
        SeqStmt(
            WhileStmt(
                ExprAbstractVar("GUARD"),
                StmtAbstractVar("BODY"),
                PPAbstractVar("PP"),
                FormulaAbstractVar("INV")
            ),
            StmtAbstractVar("CONT")
        ),
        LocalTypeAbstractTarget("TARGET"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val guardExpr = cond.map[ExprAbstractVar("GUARD")] as Expr
        val guard = exprToForm(guardExpr)
        val body = cond.map[StmtAbstractVar("BODY")] as Stmt
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val invariant = cond.map[FormulaAbstractVar("INV")] as Formula
        val target = cond.map[LocalTypeAbstractTarget("TARGET")] as LocalTypeTarget

        // We're executing a loop here which has to match the local type specification
        val ltexp = target.lte
        val useTarget: LocalTypeTarget
        val preservesTarget: LocalTypeTarget

        // Side condition: Show that the specified invariant holds
        if (ltexp.matches(LTPatternRep)) {
            val matches = ltexp.getMatches(LTPatternRep)
            if (matches.size > 1)
                output("Crowbar  : could not determine which repetition to match at '$ltexp', arbitrarily choosing first match")

            val matchedRep = matches[0] as LTRep
            preservesTarget = LocalTypeTarget(matchedRep.inner, target.roleInv, invariant, true)
            useTarget = target.updateLTE(ltexp.readTransform(LTPatternRep, greedy = true))
        }
        // If no repetition could be matched, the proof might still succeed if the loop does nothing
        else {
            useTarget = LocalTypeTarget(ltexp, target.roleInv, target.invariant, target.showInvariant)
            preservesTarget = LocalTypeTarget(LTSkip, target.roleInv, True, true)
        }

        // Initial Case
        val initial = LogicNode(
            input.condition,
            UpdateOnFormula(input.update, And(invariant, target.roleInv)), info = InfoLoopInitial(guardExpr, And(invariant, target.roleInv))
        )

        // Preserves Case
        val preservesInfo = InfoLoopPreserves(guardExpr, invariant)
        val preserves = SymbolicState(
            And(invariant, And(guard, target.roleInv)),
            EmptyUpdate,
            Modality(appendStmt(body, SeqStmt(ScopeMarker, SkipStmt)), preservesTarget)
            , listOf())

        // Use Case
        val useInfo = InfoLoopUse(guardExpr, invariant)
        val use = SymbolicState(
            And(invariant, And(Not(guard), target.roleInv)),
            EmptyUpdate,
            Modality(cont, useTarget)
            , listOf())

        return listOf(
            initial,
            SymbolicNode(preserves, info = preservesInfo),
            SymbolicNode(use, info = useInfo)
        )
    }
}

object LTTBranch : Rule(Modality(
    SeqStmt(BranchStmt(ExprAbstractVar("LHS"),
        BranchAbstractListVar("BRANCHES")), StmtAbstractVar("CONT")),
    LocalTypeAbstractTarget("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val matchExpr = cond.map[ExprAbstractVar("LHS")] as Expr
        val match = exprToTerm(matchExpr)
        val type = cond.map[LocalTypeAbstractTarget("TYPE")] as DeductType
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val branches = cond.map[BranchAbstractListVar("BRANCHES")] as BranchList
        val update = input.update
        var ress = listOf<SymbolicNode>()
        var no: Formula = True
        for (br in branches.content) {
            val preCond = Predicate("=", listOf(match, exprToTerm(br.matchTerm)))
            // Add two scope close markers for counterexample generation (one for branch, one for switch)
            val contBody = SeqStmt(br.branch, SeqStmt(ScopeMarker, SeqStmt(ScopeMarker, cont)))
            val ss = SymbolicState(And(no, And(input.condition, UpdateOnFormula(update, preCond))), update, Modality(contBody, type), listOf())
            ress = ress + SymbolicNode(ss, info = InfoBranch(matchExpr, br.matchTerm, no))
            no = And(no, Not(preCond))
        }
        return ress
    }
}
