package org.abs_models.crowbar.types

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.AssertStmt
import org.abs_models.crowbar.data.AssignStmt
import org.abs_models.crowbar.data.AwaitStmt
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.data.IfStmt
import org.abs_models.crowbar.data.ReturnStmt
import org.abs_models.crowbar.data.SkipStmt
import org.abs_models.crowbar.data.Stmt
import org.abs_models.crowbar.data.ThrowStmt
import org.abs_models.crowbar.data.WhileStmt
import org.abs_models.crowbar.interfaces.appendDesugaredCaseExprs
import org.abs_models.crowbar.interfaces.translateExpression
import org.abs_models.crowbar.interfaces.translateStatement
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.rule.FreshGenerator
import org.abs_models.crowbar.rule.MatchCondition
import org.abs_models.crowbar.rule.Rule
import org.abs_models.crowbar.tree.*
import org.abs_models.frontend.ast.*
import org.abs_models.frontend.typechecker.DataTypeType
import org.abs_models.frontend.typechecker.Type
import org.abs_models.frontend.typechecker.UnknownType
import java.io.PrintWriter
import java.io.StringWriter
import kotlin.system.exitProcess


val arithFunction = setOf("+","-","*","/")
val booleanFunction = setOf(">=","<=","<",">","=","!=",">=","<=","<",">","&&","||", "true", "false")

/**
 * Behavioral type for (cooperative) method contracts, object invariants and assertions.
 */
interface PostInvType : DeductType{
    companion object : PostInvType

    /**
     * Extracts the proof obligation for a single method classDecl.name
     */
    override fun extractMethodNode(classDecl: ClassDecl, name : String, repos: Repository) : SymbolicNode {
        val mDecl = classDecl.methods.firstOrNull { it.methodSig.name == name }
        if (mDecl == null) {
            if(reporting) throw Exception("method not found: ${classDecl.qualifiedName}.${name}")
            System.err.println("method not found: ${classDecl.qualifiedName}.${name}")
            exitProcess(-1)
        }

        //Translating input. Specification is *not* checked by the ABS compiler so this may fail.
        output("Crowbar  : loading specification....")
        val symb: SymbolicState?
        val objInv: Formula?
        val metpost: Formula?
        val metpre: Formula?
        val roles: Formula?
        val body: Stmt?
        var overlapsSet : String? = null
        var succeedsSet : String? = null
        val hasPre = hasHeapPre(mDecl)
        try {
            objInv = extractSpec(classDecl, "ObjInv", UnknownType.INSTANCE)
            metpost = extractSpec(mDecl, "Ensures", mDecl.type)
            metpre = extractInheritedSpec(mDecl.methodSig, "Requires")
            body = getNormalizedStatement(mDecl.block)
            roles = extractRoleSpec(classDecl)
            if(hasPre) {
                overlapsSet = extractContextSet(mDecl, "Overlaps")
                succeedsSet = extractContextSet(mDecl, "Succeeds")
            }
        } catch (e: Exception) {
            if(reporting) reportException("error during translation, aborting", e)
            System.err.println("error during translation, aborting")
            throw e
        }
        output("Crowbar-v: method post-condition: ${metpost.prettyPrint()}", Verbosity.V)
        output("Crowbar-v: object invariant: ${objInv.prettyPrint()}",Verbosity.V)

        //Save last and old heap
        val updateOldHeap = ChainUpdate(ElementaryUpdate(LastHeap,Heap), ElementaryUpdate(OldHeap, Heap))
        symb = SymbolicState(And(And(objInv,metpre),roles), updateOldHeap, Modality(body, PostInvariantPair(metpost, objInv)), listOf())

        //Default values for missing contract parts
        if(hasPre && (overlapsSet == null || succeedsSet == null)){
            output("Crowbar: Method ${mDecl.methodSig.name} has a heap precondition but does not fully specify its context.")
            val full = classDecl.allMethodSigs.joinToString(",") { it.name }
            if(overlapsSet == null) overlapsSet = full
            if(succeedsSet == null) succeedsSet = full
        }
        return SymbolicNode(symb, if (hasPre) listOf(SymbolicNode(symb, emptyList()),
                                                     StaticNode("Overlaps ${classDecl.moduleName()}.${classDecl.name}.${mDecl.methodSig.name} {$overlapsSet}"),
                                                     StaticNode("Succeeds ${classDecl.moduleName()}.${classDecl.name}.${mDecl.methodSig.name} {$succeedsSet}"))
                                  else emptyList())
    }

    /**
     * Checks whether a heap precondition is present
     */
    fun hasHeapPre(mDecl: MethodImpl) : Boolean{
        for (annotation in mDecl.methodSig.nodeAnnotations) {
            if (!annotation.type.toString().endsWith(".Spec") || annotation.value !is DataConstructorExp) continue
            val annotated = annotation.value as DataConstructorExp
            if (annotated.constructor == "Requires") return true
        }
        return false
    }

    /**
     * Returns the context set `expectedSpec` as a string, or null if it is not specified
     */
    fun extractContextSet(mDecl: MethodImpl, expectedSpec: String): String? {

        for (annotation in mDecl.nodeAnnotations) {
            if (!annotation.type.toString().endsWith(".Spec")) continue
            if (annotation.value !is DataConstructorExp) {
                throw Exception("Could not extract any specification from $mDecl because of the expected value")
            }
            val annotated = annotation.value as DataConstructorExp
            if (annotated.constructor != expectedSpec) continue
            val content = annotated.getParam(0) as Exp
            if(content !is FnApp ||
               content.name != "list" ||
               content.getParam(0) !is ListLiteral ||
               (content.getParam(0) as ListLiteral).pureExpList.any { it !is StringLiteral })
                throw Exception("Could not extract context set $expectedSpec from ${mDecl.methodSig.name}: set must be declared using list[\"str\",...]")
            return (content.getParam(0) as ListLiteral).pureExpList.joinToString(",") { (it as StringLiteral).content }
        }
        return null
    }

    /**
     * Creates the proof obligation for the class initializer: first field initializers are executed, then the initializing block
     */
    override fun extractInitialNode(classDecl: ClassDecl) : SymbolicNode {

        var body = getNormalizedStatement(classDecl.initBlock)
        for (fieldDecl in classDecl.fields){
            if(fieldDecl.hasInitExp()){
                val nextBody = AssignStmt(Field(fieldDecl.name+"_f", fieldDecl.type),
                        translateExpression(fieldDecl.initExp, UnknownType.INSTANCE, emptyMap(), true).first) //todo: check!
                body = SeqStmt(nextBody,body)
            }
        }

        output("Crowbar  : loading specification....")
        val objInv: Formula?
        val objPre: Formula?
        try {
            objInv = extractSpec(classDecl, "ObjInv", UnknownType.INSTANCE)
            objPre = extractSpec(classDecl, "Requires",UnknownType.INSTANCE)
        } catch (e: Exception) {
            if(reporting) reportException("error during translation, aborting", e)
            e.printStackTrace()
            System.err.println("error during translation, aborting")
            exitProcess(-1)
        }
        if (verbosity >= Verbosity.V) {
            output("Crowbar-v: object precondition: ${objPre.prettyPrint()}")
            output("Crowbar-v: object invariant: ${objInv.prettyPrint()}")
        }
        val symb = SymbolicState(objPre, EmptyUpdate, Modality(body, PostInvariantPair(True, objInv)), listOf())
        return SymbolicNode(symb, emptyList())
    }

    /**
     *  Generates the proof obligation for the main block.
     *  The main block is the one selected by the ABS compiler, all other main blocks are ignored.
     */
    override fun exctractMainNode(model: Model) : SymbolicNode {

        if(!model.hasMainBlock()){
            if(reporting) throw Exception("model has no main block!")
            System.err.println("model has no main block!")
            exitProcess(-1)
        }

        val v = appendStmt(translateStatement(model.mainBlock, emptyMap()), SkipStmt)
        return SymbolicNode(SymbolicState(True, EmptyUpdate, Modality(v, PostInvariantPair(True, True)), listOf()), emptyList())
    }

    /**
     *  Generates the proof obligation a function f(x) by generating a dummy method with the method body s; return f'(x).
     *  Statement s and f' are generated by pulling out case expressions in front to simplify the program structure for symbolic execution.
     */
    override fun exctractFunctionNode(fDecl: FunctionDecl): SymbolicNode {
        val symb: SymbolicState?
        val funpost: Formula?
        val funpre: Formula?
        var body: Stmt? = null
        try {
            funpre = extractSpec(fDecl, "Requires", fDecl.type)
            funpost = extractSpec(fDecl, "Ensures", fDecl.type)
            val fDef = fDecl.functionDef
            if(fDef is BuiltinFunctionDef){
                throw Exception("error during translation, cannot handle builtin yet")
            }else if(fDef is ExpFunctionDef){

                val expr = translateExpression(fDef.rhs, fDecl.type, emptyMap(),false)
                body = appendDesugaredCaseExprs(expr.second, ReturnStmt(expr.first))

            }
        }catch (e: Exception) {
            e.printStackTrace()
            System.err.println("error during translation, aborting")
            throw e
        }
        if(body != null) {
            symb = SymbolicState(funpre, EmptyUpdate, Modality(body, PostInvariantPair(funpost, True)), listOf())
            return SymbolicNode(symb, emptyList())
        }else{
            throw Exception("error during translation of function contract")
        }
    }
}

data class PostInvAbstractVar(val name : String) : PostInvType, AbstractVar{
    override fun prettyPrint(): String {
        return name
    }
}

data class PostInvariantPair(val post : Formula, val objInvariant : Formula) : PostInvType {
    override fun prettyPrint(): String {
        return post.prettyPrint()+", "+objInvariant.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + post.iterate (f) + objInvariant.iterate (f)
}

/**
 * Class for all statements that assign to something.
 */
abstract class PITAssign(protected val repos: Repository,
                         conclusion : Modality) : Rule(conclusion){

    protected fun assignFor(loc : Location, rhs : Term) : ElementaryUpdate{
        return if(loc is Field)   ElementaryUpdate(Heap, store(loc, rhs)) else ElementaryUpdate(loc as ProgVar, rhs)
    }

    protected fun symbolicNext(loc : Location,
                     rhs : Term,
                     remainder : Stmt,
                     target : DeductType,
                     iForm : Formula,
                     iUp : UpdateElement,
                     infoObj: NodeInfo,
                     scopes: List<ConcreteExceptionScope>) : SymbolicNode{
        return SymbolicNode(SymbolicState(
            iForm,
            ChainUpdate(iUp, assignFor(loc,rhs)),
            Modality(remainder, target),
            scopes
        ), info = infoObj)
    }
}

//Type system itself




/**
 * Class for assignment of pure expressions
 */
class PITLocAssign(repos: Repository) : PITAssign(repos,Modality(
    SeqStmt(AssignStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR")), StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val rhsExpr = cond.map[ExprAbstractVar("EXPR")] as Expr
        val rhs = exprToTerm(rhsExpr)
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        // for the CEG
        val info = InfoLocAssign(lhs, rhsExpr)

        //ABS pure expression may still throw implicit exceptions, which are handled by ZeroNodes
        val zeros  = divByZeroNodes(listOf(rhsExpr), remainder, input, repos)

        //consume statement and add ZeroNodes
        return listOf(symbolicNext(lhs, rhs, remainder, target, input.condition, input.update, info, input.exceptionScopes)) + zeros
    }
}

/**
 * Class for assignment with a .get top level expressions
 */
class PITSyncAssign(repos: Repository) : PITAssign(repos, Modality(
    SeqStmt(SyncStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR"), AbstractStringSet("RESOLVES"), PPAbstractVar("PP")),
        StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val rhsExpr = cond.map[ExprAbstractVar("EXPR")] as Expr
        val rhs = exprToTerm(rhsExpr)
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val resolves = cond.map[AbstractStringSet("RESOLVES")] as ConcreteStringSet
        val pp = cond.map[PPAbstractVar("PP")] as PP


        // Generate SMT representation of the future expression to get its model value later
        val futureSMTExpr = apply(input.update, rhs) as Term
        val info = InfoGetAssign(lhs, rhsExpr, futureSMTExpr)
        var cond = input.condition
        var zeros : List<SymbolicTree>  = divByZeroNodes(listOf(rhsExpr), remainder, input, repos)


        //future contracts are external to Crowbar
        if(resolves.vals.isNotEmpty()){
            val ground =  StaticNode("Must resolve: $pp contract $resolves")
            var got = resolves.vals.mapNotNull { repos.methodEnss[it] }
                .foldRight<Pair<Formula, MethodSig>, Formula>(True) { nx, acc -> And(acc, nx.first) }
            val myType =  getReturnType(exprToTerm(lhs))

            //we do not know the caller, so we throw away the contract if any input variable is used.
            //this can be made a bit more precise using the usual projection
            if(got.iterate { it is ProgVar && it.name != "result"}.isNotEmpty())
                got = True
            else
                got = subst(got, mapOf(Pair(ReturnVar(myType.qualifiedName, myType), rhs))) as Formula
            cond = And(cond, apply(input.update, got) as Formula)
            zeros = zeros + ground
        }
        return listOf(symbolicNext(lhs, rhs, remainder, target, cond, input.update, info, input.exceptionScopes)) + zeros
    }

}

/**
 *  Rule for statements that create a new instance
 */
class PITAllocAssign(repos: Repository) : PITAssign(repos, Modality(
    SeqStmt(AllocateStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR")),
        StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val rhsExpr = cond.map[ExprAbstractVar("EXPR")] as Expr
        val rhs = exprToTerm(rhsExpr) as Function
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[PostInvAbstractVar("TYPE")] as DeductType

        val classNameExpr = rhs.params[0] as Function
        val nextRhs = Function(rhs.name,rhs.params.subList(1,rhs.params.size))

        //construct precondition check of the class creation
        val precond = repos.classReqs.getValue(classNameExpr.name).first
        val targetDecl = repos.classReqs[classNameExpr.name]!!.second
        val substMap = mutableMapOf<LogicElement,LogicElement>()
        for(i in 0 until targetDecl.numParam){
            val pName = select(Field(targetDecl.getParam(i).name+"_f", targetDecl.getParam(i).type))
            val pValue = nextRhs.params[i]
            substMap[pName] = pValue
        }
        val precondSubst = subst(precond, substMap) as Formula

        val pre = LogicNode(
            input.condition,
            UpdateOnFormula(input.update, precondSubst),
            info = InfoClassPrecondition(precondSubst)
        )

        // Generate SMT representation of the NEW expression to get its model value later
        val constructorSMTExpr = apply(input.update, nextRhs).toSMT()

        val next = symbolicNext(lhs,
                                            nextRhs,
                                            remainder,
                                            target,
                                            And(input.condition, UpdateOnFormula(input.update, Not(Predicate("=", listOf(nextRhs, Function("0")))))),
                                            ChainUpdate(input.update, assignFor(lhs, nextRhs)),
                                            InfoObjAlloc(lhs, rhsExpr, constructorSMTExpr), input.exceptionScopes)

        val zeros  = divByZeroNodes(listOf(rhsExpr), remainder, input, repos)
        return listOf(pre, next) + zeros
    }
}

/**
 * Rule for asynchronous method calls
 */
class PITCallAssign(repos: Repository) : PITAssign(repos, Modality(
    SeqStmt(CallStmt(LocationAbstractVar("LHS"), ExprAbstractVar("CALLEE"), CallExprAbstractVar("CALL")),
        StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val calleeExpr = cond.map[ExprAbstractVar("CALLEE")] as Expr
        val callee = exprToTerm(calleeExpr)
        val call = cond.map[CallExprAbstractVar("CALL")] as CallExpr
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[PostInvAbstractVar("TYPE")] as DeductType

        val notNullCondition = Predicate("=", listOf(callee,Function("0", emptyList())))

        //NonNull check here
        val absExp = calleeExpr.absExp
        val isNonNull = false //absExp?.nonNull() ?: false
        val nonNull =
        SymbolicNode(SymbolicState(And(input.condition, UpdateOnFormula(input.update, notNullCondition)), input.update, Modality(
            appendStmt(ThrowStmt(DataTypeExpr("ABS.StdLib.Exceptions.NullPointerException","ABS.StdLib.Exception", repos.model?.exceptionType, listOf())),
                remainder), input.modality.target), input.exceptionScopes),
            info = InfoNullCheck(notNullCondition))

        //construct precondition check of the call
        val precond = repos.methodReqs.getValue(call.met).first
        val targetDecl = repos.methodReqs.getValue(call.met).second
        val substMap = mutableMapOf<LogicElement,LogicElement>()
        for(i in 0 until targetDecl.numParam){
            val pName = ProgVar(
                targetDecl.getParam(i).name,
                targetDecl.getParam(i).type
            )
            val pValue = exprToTerm(call.e[i])
            substMap[pName] = pValue
        }
        val precondSubst = subst(precond, substMap) as Formula
        val pre = LogicNode(
            input.condition,
            UpdateOnFormula(input.update, precondSubst),
            info = InfoMethodPrecondition(precondSubst)
        )

        val freshFut = FreshGenerator.getFreshFuture(targetDecl.type)
        val read = repos.methodEnss[call.met]
        val postCond = read?.first ?: True

        val targetPostDecl = read!!.second
        val substPostMap = mutableMapOf<LogicElement,LogicElement>()
        for(i in 0 until targetDecl.numParam){
            val pName = ProgVar(
                targetPostDecl.getParam(i).name,
                targetPostDecl.getParam(i).type
            )
            val pValue = exprToTerm(call.e[i])
            substPostMap[pName] = pValue
        }

        val updateNew = ElementaryUpdate(ReturnVar(targetDecl.type.qualifiedName, targetDecl.type),valueOfFunc(freshFut))

        val next = symbolicNext(lhs,
                                            freshFut,
                                            remainder,
                                            target,
                                            And(input.condition, UpdateOnFormula(input.update,UpdateOnFormula(updateNew,subst(postCond, substPostMap) as Formula))),
                                            input.update,
                                            InfoCallAssign(lhs, calleeExpr, call, freshFut.name), input.exceptionScopes)
        if (isNonNull) return listOf(pre, next)
        val zeros  = divByZeroNodes(call.e, remainder, input, repos)
        return listOf(nonNull,pre,next) + zeros
    }
}


/**
 * Rule for synchronous method calls
 */
class PITSyncCallAssign(repos: Repository) : PITAssign(repos, Modality(
        SeqStmt(SyncCallStmt(LocationAbstractVar("LHS"), ExprAbstractVar("CALLEE"), SyncCallExprAbstractVar("CALL")),
                StmtAbstractVar("CONT")),
        PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val call = cond.map[SyncCallExprAbstractVar("CALL")] as SyncCallExpr
        val calleeExpr = cond.map[ExprAbstractVar("CALLEE")] as Expr
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[PostInvAbstractVar("TYPE")] as PostInvariantPair


        var precond = repos.syncMethodReqs.getValue(call.met).first
        precond = And(precond, target.objInvariant)
        val targetPreDecl = repos.syncMethodReqs.getValue(call.met).second

        val freshVar = FreshGenerator.getFreshProgVar(targetPreDecl.type)//ASK<<

        val updateNew = ElementaryUpdate(ReturnVar(targetPreDecl.type.qualifiedName, targetPreDecl.type), freshVar)

        val substPreMap = mapSubstPar(call, targetPreDecl)
        val precondSubst = subst(precond, substPreMap) as Formula

        //preconditions
        val first = LogicNode(
                input.condition,
                UpdateOnFormula(input.update, precondSubst),
                info = InfoMethodPrecondition(precondSubst)
        )

        var postCond = repos.syncMethodEnss[call.met]?.first ?: True
        postCond = And(postCond, target.objInvariant)
        val targetPostDecl = repos.syncMethodEnss[call.met]!!.second
        val substPostMap = mapSubstPar(call, targetPostDecl)

        val anon = ElementaryUpdate(Heap, anon(Heap))

        val heapUpdate = ChainUpdate(ElementaryUpdate(OldHeap,Heap), ElementaryUpdate(LastHeap,anon(Heap)))

        val updateLeftNext = ChainUpdate(input.update, ChainUpdate(heapUpdate, ChainUpdate(anon, updateNew)))
        val updateRightNext = ChainUpdate(input.update, anon)
        val updateOnFormula =  UpdateOnFormula(updateLeftNext, subst(postCond, substPostMap) as Formula)

        // Generate SMT representation of the anonymized heap for future heap reconstruction
        val anonHeapExpr = apply(updateRightNext, Heap) as Term
        // Generate SMT expression of method return value for model evaluation
        val returnValExpr = apply(updateRightNext, freshVar) as Term

        val next = symbolicNext(lhs,
                freshVar,
                remainder,
                target,
                And(input.condition, updateOnFormula),
                updateRightNext,
                InfoSyncCallAssign(lhs, calleeExpr, call, anonHeapExpr, returnValExpr), input.exceptionScopes)

        val zeros  = divByZeroNodes(call.e, remainder, input, repos)
        return listOf(first,next) + zeros
    }
}


/**
 *  Rule for skip without following statement. SE demands that every branch ends in a return
 *  or skip because these are the only rules that operates on a SymbolicNode and generates no further SymbolicNode.
 */
object PITSkip : Rule(Modality(
        SkipStmt,
        PostInvariantPair(FormulaAbstractVar("POST"), FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val target = cond.map[FormulaAbstractVar("POST")] as Formula
        val res = LogicNode(
                    input.condition,
                    UpdateOnFormula(input.update, target),
                    info = InfoSkipEnd(target)
        )
        return listOf(res)
    }
}

/**
 *  Rule for Skip with a following statement
 */
object PITSkipSkip : Rule(Modality(
        SeqStmt(SkipStmt, StmtAbstractVar("CONT")),
        PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val pitype = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val res = SymbolicNode(SymbolicState(input.condition, input.update, Modality(cont, pitype), input.exceptionScopes), info = InfoSkip())
        return listOf(res)
    }
}

/**
 *  Scopes are ignored and only there to add structure to the SE for the CEG.
 */
object PITScopeSkip : Rule(Modality(
        SeqStmt(ScopeMarker, StmtAbstractVar("CONT")),
        PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val pitype = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val res = SymbolicNode(SymbolicState(input.condition, input.update, Modality(cont, pitype), input.exceptionScopes), info = InfoScopeClose())
        return listOf(res)
    }
 }

/**
 *  Rule for return. The IR can handle returns anywhere, but SE demands that every branch ends in a return
 *  or skip because these are the only rules that operates on a SymbolicNode and generates no further SymbolicNode.
 */
class PITReturn(val repos: Repository) : Rule(Modality(
        ReturnStmt(ExprAbstractVar("RET")),
        PostInvariantPair(FormulaAbstractVar("POST"), FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val target = cond.map[FormulaAbstractVar("OBJ")] as Formula
        val targetPost = cond.map[FormulaAbstractVar("POST")] as Formula
        val retExpr = cond.map[ExprAbstractVar("RET")] as Expr
        val ret = exprToTerm(retExpr)
        val retTypeFromPost = retrieveReturnTypeFromPost(targetPost)
        var typeReturn = getReturnType(ret)
        if(isGeneric(typeReturn) && !isBoundGeneric(typeReturn))
            typeReturn = retTypeFromPost ?: throw Exception("Unbound return type for retExpr: $retExpr")

        val res = LogicNode(
            input.condition,
            And(
                    UpdateOnFormula(ChainUpdate(input.update, ElementaryUpdate(ReturnVar(typeReturn.qualifiedName,typeReturn), ret)), targetPost),
                    UpdateOnFormula(input.update, target)
            ),
            info = InfoReturn(retExpr, targetPost, target, input.update)
        )
        val zeros  = divByZeroNodes(listOf(retExpr), SkipStmt, input, repos)
        return listOf(res) + zeros
    }
}

/**
 * Rule for standard binary branching
 */
class PITIf(val repos: Repository) : Rule(Modality(
        SeqStmt(IfStmt(ExprAbstractVar("LHS"), StmtAbstractVar("THEN"), StmtAbstractVar("ELSE")),
                StmtAbstractVar("CONT")),
        PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {

        val contBody = SeqStmt(ScopeMarker, cond.map[StmtAbstractVar("CONT")] as Stmt) // Add a ScopeMarker statement to detect scope closure
        val guardExpr = cond.map[ExprAbstractVar("LHS")] as Expr

        //then
        val guardYes = exprToForm(guardExpr)
        val bodyYes = SeqStmt(cond.map[StmtAbstractVar("THEN")] as Stmt, contBody)
        val updateYes = input.update
        val typeYes = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val resThen = SymbolicState(And(input.condition, UpdateOnFormula(updateYes, guardYes)), updateYes, Modality(bodyYes, typeYes), input.exceptionScopes)

        val shortThen = LogicNode(And(input.condition, UpdateOnFormula(updateYes, guardYes)), False).evaluate()

        //else
        val guardNo = Not(exprToForm(guardExpr))
        val bodyNo = SeqStmt(cond.map[StmtAbstractVar("ELSE")] as Stmt, contBody)
        val updateNo = input.update
        val typeNo = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val resElse = SymbolicState(And(input.condition, UpdateOnFormula(updateNo, guardNo)), updateNo, Modality(bodyNo, typeNo), input.exceptionScopes)

        val shortElse = LogicNode(And(input.condition, UpdateOnFormula(updateYes, guardNo)), False).evaluate()
        val zeros  = divByZeroNodes(listOf(guardExpr), contBody, input, repos)
        var next = zeros
        if(shortThen && !shortElse) next = next + listOf(SymbolicNode(resElse, info = InfoIfThen(guardExpr)))
        else if(shortElse && !shortThen) next = next +listOf(SymbolicNode(resElse, info = InfoIfElse(guardExpr)))
        else next = next+ listOf(SymbolicNode(resThen, info = InfoIfThen(guardExpr)), SymbolicNode(resElse, info = InfoIfElse(guardExpr)))
        return next
    }
}

/**
 *  Rule for assertion
 */
class PITAssert(val repos: Repository) : Rule(Modality(
    SeqStmt(AssertStmt(ExprAbstractVar("GUARD")), StmtAbstractVar("CONT")),
    PostInvariantPair(FormulaAbstractVar("POST"), FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val guardExpr = cond.map[ExprAbstractVar("GUARD")] as Expr
        val guard = exprToForm(guardExpr)
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[FormulaAbstractVar("OBJ")] as Formula
        val targetPost = cond.map[FormulaAbstractVar("POST")] as Formula


        val lNode =
        SymbolicNode(SymbolicState(And(input.condition, UpdateOnFormula(input.update, Not(guard))), input.update, Modality(
            appendStmt(ThrowStmt(DataTypeExpr("ABS.StdLib.Exceptions.AssertionFailException","ABS.StdLib.Exception", repos.model?.exceptionType, listOf())),
                cont), input.modality.target), input.exceptionScopes))

        val sStat = SymbolicState(And(input.condition, UpdateOnFormula(input.update, guard)), input.update, Modality(cont, PostInvariantPair(targetPost,target)), input.exceptionScopes)

        val zeros  = divByZeroNodes(listOf(guardExpr), cont, input, repos)
        return listOf<SymbolicTree>(lNode,SymbolicNode(sStat, info = NoInfo())) + zeros
    }
}

/**
 *  Rule for expressions without target. Essentially a skip, but with ZeroNodes for exceptions thrown by the expressions
 */
class PITExpr(val repos: Repository) : Rule(Modality(
    SeqStmt(ExprStmt(ExprAbstractVar("EXPR")), StmtAbstractVar("CONT")),
    PostInvariantPair(FormulaAbstractVar("POST"), FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val guardExpr = cond.map[ExprAbstractVar("EXPR")] as Expr
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[FormulaAbstractVar("OBJ")] as Formula
        val targetPost = cond.map[FormulaAbstractVar("POST")] as Formula

        val sStat = SymbolicState(input.condition, input.update, Modality(cont, PostInvariantPair(targetPost,target)), input.exceptionScopes)

        val zeros  = divByZeroNodes(listOf(guardExpr), cont, input, repos)
        return listOf<SymbolicTree>(SymbolicNode(sStat, info = NoInfo())) + zeros
    }
}


/**
 *  Rule for suspension
 */
class PITAwait(val repos: Repository) : Rule(Modality(
        SeqStmt(AwaitStmt(ExprAbstractVar("GUARD"),PPAbstractVar("PP")), StmtAbstractVar("CONT")),
        PostInvariantPair(FormulaAbstractVar("POST"), FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val guardExpr = cond.map[ExprAbstractVar("GUARD")] as Expr
        val guard = exprToForm(guardExpr)
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[FormulaAbstractVar("OBJ")] as Formula
        val targetPost = cond.map[FormulaAbstractVar("POST")] as Formula

        val updateLastHeap = ElementaryUpdate(LastHeap, Heap)

        // Generate SMT representation of the anonymized heap for future heap reconstruction
        val anonHeapExpr = apply(ChainUpdate(input.update, ElementaryUpdate(Heap,anon(Heap))), Heap) as Term

        val lNode = LogicNode(input.condition, UpdateOnFormula(input.update, target), info = InfoInvariant(target))

        val sStat = SymbolicState(
                And(
                        input.condition,
                        UpdateOnFormula(
                                ChainUpdate(input.update,ChainUpdate(ElementaryUpdate(Heap,anon(Heap)),updateLastHeap)),
                                And(target,guard)
                        )
                ),
                ChainUpdate(input.update, ChainUpdate(ElementaryUpdate(Heap,anon(Heap)),updateLastHeap)),
                Modality(cont, PostInvariantPair(targetPost,target)), input.exceptionScopes)
        val zeros  = divByZeroNodes(listOf(guardExpr), cont, input, repos)
        return listOf(lNode,SymbolicNode(sStat, info = InfoAwaitUse(guardExpr, anonHeapExpr))) + zeros
    }
}

/**
 *  Start of a try-catch-finally block. Adds an exception scope
 */
object PITTryPush: Rule(Modality(
    SeqStmt(TryPushStmt(ConcreteExceptionScope(BranchAbstractListVar("BRANCHES"), StmtAbstractVar("FINALLY"), PPAbstractVar("PP"))),StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val type = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val finally = cond.map[StmtAbstractVar("FINALLY")] as Stmt
        val branches = cond.map[BranchAbstractListVar("BRANCHES")] as BranchList
        val pp = cond.map[PPAbstractVar("PP")] as PP
        val res = SymbolicState(input.condition, input.update, Modality(cont, type), listOf(ConcreteExceptionScope(branches, finally, pp)) + input.exceptionScopes)
        return listOf<SymbolicTree>(SymbolicNode(res))
    }
}

/**
 *  End of a try-catch-finally block. Removes outermost exception scope
 */
object PITTryPop: Rule(Modality(
    SeqStmt(TryPopStmt(PPAbstractVar("PP")),StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val type = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val pp = cond.map[PPAbstractVar("PP")] as PP
        val scope = input.exceptionScopes.firstOrNull { it.id == pp }
        val res : SymbolicState = if(scope == null)
            SymbolicState(
                input.condition,
                input.update,
                Modality(cont, type),
                input.exceptionScopes
            )
        else {
            SymbolicState(
                input.condition,
                input.update,
                Modality(appendStmt(scope.finally, cont), type),
                input.exceptionScopes.filter { it.id != pp }
            )
        }
        return listOf<SymbolicTree>(SymbolicNode(res))
    }
}

/**
 * Rule for loops. This is the throwaway variant of loop invariants without anonymizing.
 */
object PITWhile : Rule(Modality(
        SeqStmt(WhileStmt(ExprAbstractVar("GUARD"),
                          StmtAbstractVar("BODY"),
                          PPAbstractVar("PP"),
                          FormulaAbstractVar("INV")),
                StmtAbstractVar("CONT")),
        PostInvariantPair(FormulaAbstractVar("POST"),
                          FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val guardExpr = cond.map[ExprAbstractVar("GUARD")] as Expr
        val guard = exprToForm(guardExpr)
        val body = cond.map[StmtAbstractVar("BODY")] as Stmt
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val targetInv = cond.map[FormulaAbstractVar("INV")] as Formula
        val target = cond.map[FormulaAbstractVar("OBJ")] as Formula
        val targetPost = cond.map[FormulaAbstractVar("POST")] as Formula

        val form = getDivisors(guardExpr).foldRight(True as Formula) { nx, acc -> And(acc, innerDivByZeroFormula(nx))}
        //Initial Case
        val initial = LogicNode(input.condition, UpdateOnFormula(input.update, And(form,targetInv)), info = InfoLoopInitial(guardExpr, targetInv))

        //Preserves Case
        val preservesInfo = InfoLoopPreserves(guardExpr, targetInv)
        val preserves = SymbolicState(And(And(targetInv, form), guard),
                                      EmptyUpdate,
                                      Modality(appendStmt(body,SeqStmt(ScopeMarker, SkipStmt)), PostInvariantPair(And(targetInv, form),target)), input.exceptionScopes)

        //Use Case
        val useInfo = InfoLoopUse(guardExpr, targetInv)
        val use = SymbolicState(And(And(targetInv, form),Not(guard)),
                                  EmptyUpdate,
                                  Modality(cont, PostInvariantPair(targetPost,target)), input.exceptionScopes)

        return listOf(
            initial,
            SymbolicNode(preserves, info = preservesInfo),
            SymbolicNode(use, info = useInfo)
        )

    }
}

/**
 *  Case statement
 */
class PITBranch(val repos: Repository) : Rule(Modality(
    SeqStmt(BranchStmt(ExprAbstractVar("LHS"),
        BranchAbstractListVar("BRANCHES")),StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val matchExpr = cond.map[ExprAbstractVar("LHS")] as Expr
        val match = exprToTerm(matchExpr)
        val type = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val branches = cond.map[BranchAbstractListVar("BRANCHES")] as BranchList
        val update = input.update
        var ress = listOf<SymbolicNode>()
        var no : Formula = True
        for(br in branches.content){
            val preCond = UpdateOnFormula(update, Predicate("=",listOf(match, exprToTerm(br.matchTerm))))
            // Add two scope close markers for counterexample generation (one for branch, one for switch)
            val contBody = SeqStmt(br.branch, SeqStmt(ScopeMarker, SeqStmt(ScopeMarker, cont)))
            val ss = SymbolicState(And(no,And(input.condition, preCond)), update, Modality(contBody, type), input.exceptionScopes)
            ress = ress + SymbolicNode(ss, info = InfoBranch(matchExpr, br.matchTerm, no))
            no = And(no, Not(preCond))
        }
        //if there is no default branch, add one by hand
        if(!branches.content.any { it.matchTerm is ProgVar }){
            val myBody = appendStmt(ThrowStmt(SExpr("ABS.StdLib.PatternMatchFailException", listOf())), cont)
            val newStmt = SymbolicState(no, update, Modality(myBody, type), input.exceptionScopes)
            ress = ress + SymbolicNode(newStmt, info = InfoBranch(matchExpr, SExpr("ABS.StdLib.PatternMatchFailException", listOf()), no))
        }
        println(no.prettyPrint())
        val zeros  = divByZeroNodes(listOf(matchExpr), cont, input, repos)
        return ress + zeros
    }
}

/**
 * Class for throw statements
 */
object PITThrow : Rule(Modality(
    SeqStmt(ThrowStmt(ExprAbstractVar("EXCEP")),StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val matchExpr = cond.map[ExprAbstractVar("EXCEP")] as Expr
        val type = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt

        //If there are no scopes, the proof fails because method terminates with an exception
        if(input.exceptionScopes.isEmpty()){
            return listOf<SymbolicTree>(LogicNode(input.condition, UpdateOnFormula(input.update, False)))
        }

        //transform outermost scope into a case statement against the thrown exception
        val transform = buildMatchForScope(matchExpr, input.exceptionScopes, cont)

        //drop outermost scope now
        val res = SymbolicState(input.condition, input.update, Modality(transform, type),  input.exceptionScopes.drop(1))
        return listOf<SymbolicTree>(SymbolicNode(res))
    }
}

fun getReturnType(term: Term) : Type {
    if(term is ProgVar){
        return term.concrType
    }
    else if(term is DataTypeConst){
        return term.concrType!!
    }
    else if (term is Function) {
        if(term.name in setOf( "contains","emptyMap"))
            return ADTRepos.model!!.boolType
        if(term.name in setOf("ABS.StdLib.Cons_0","ABS.StdLib.Insert_0", "fst","fstT","head", "appendright","concatenate"))
            return (getReturnType(term.params[0]) as DataTypeType).getTypeArg(0)
        if(term.name in setOf("snd","sndT","lookup"))
            return (getReturnType(term.params[0]) as DataTypeType).getTypeArg(1)
        if(term.name == "trdT")
            return (getReturnType(term.params[0]) as DataTypeType).getTypeArg(2)
        if(term.name in setOf("ABS.StdLib.Cons_1", "ABS.StdLib.Insert_1", "ABS.StdLib.InsertAssoc_1","tail"))
            return (getReturnType(term.params[0]) as DataTypeType)
        if (term.name in arithFunction ){
            val left = getReturnType(term.params[0])
            val right = getReturnType(term.params[1])
            if(left == ADTRepos.model!!.intType && right == ADTRepos.model!!.intType) return ADTRepos.model!!.intType
            return ADTRepos.model!!.floatType
        }
        if ( term.name.toIntOrNull() != null)
            return ADTRepos.model!!.intType
        if ( term.name.toFloatOrNull() != null)
            return ADTRepos.model!!.floatType
        if (term.name == "valueOf")
            return ((term.params[0] as ProgVar).concrType as DataTypeType).getTypeArg(0)
        if (term.name in booleanFunction)
            return ADTRepos.model!!.boolType
        return when (term.name) {
            "Unit" -> ADTRepos.model!!.unitType
            "ite" -> getReturnType(term.params[1])
            "select" -> (term.params[1] as Field).concrType
            else -> {
                val fName = term.name.replace("-",".")
                if(FunctionRepos.isKnown(fName))
                    return FunctionRepos.get(fName).type
                else
                    throw Exception("Function $fName not defined")
            }
        }
    }
    else if(term is Case){
        return term.expectedTypeConcr
    }
    else {
        throw java.lang.Exception("Term $term not allowed as return ")
    }
}

fun divByZeroNodes(exprs: List<Expr>, next : Stmt, input : SymbolicState, repos: Repository) : List<SymbolicTree> =
    exprs.flatMap { getDivisors(it) }.foldRight(emptyList()) { nx, acc -> acc + divByZeroSingleNode(nx, next, input, repos) }

fun getDivisors(expr : Expr) : List<Expr> =
     (expr.iterate { it is SExpr && it.op == "/" } as Set<SExpr>).map { it.e[1] }

fun divByZeroSingleNode(expr: Expr, next : Stmt, input : SymbolicState, repos: Repository) : SymbolicTree =
    SymbolicNode(SymbolicState(And(input.condition, UpdateOnFormula(input.update, innerDivByZeroFormula(expr))), input.update, Modality(
        appendStmt(ThrowStmt(DataTypeExpr("ABS.StdLib.Exceptions.DivisionByZeroException","ABS.StdLib.Exception", repos.model?.exceptionType, listOf())),
            next), input.modality.target), input.exceptionScopes))

fun innerDivByZeroFormula(expr: Expr) : Formula =
     Eq(exprToTerm(expr), Function("0"))



fun buildMatchForScope(thrown : Expr, active : List<ConcreteExceptionScope>, cont : Stmt) : Stmt {
    val first = active[0]
    return appendStmt(appendStmt(BranchStmt(thrown, first.scopes), first.finally), cont)
}

fun retrieveReturnTypeFromPost(post: Formula) : Type?{
    val resultSet = post.iterate { it is ProgVar && it.name == "result" }
    return  if(resultSet.isEmpty()) null else (resultSet.toList().first() as ProgVar).concrType
}


fun mapSubstPar(callExpr: SyncCallExpr, targetDecl: MethodSig): MutableMap<LogicElement, LogicElement> {

    val substMap = mutableMapOf<LogicElement, LogicElement>()

    for (i in 0 until targetDecl.numParam) {
        val pName = ProgVar(
            targetDecl.getParam(i).name,
            targetDecl.getParam(i).type
        )
        val pValue = exprToTerm(callExpr.e[i])
        substMap[pName] = pValue

    }
    return substMap
}