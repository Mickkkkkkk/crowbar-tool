package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Const
import org.abs_models.crowbar.data.SkipStmt
import org.abs_models.crowbar.main.ADTRepos
import org.abs_models.crowbar.main.FunctionRepos
import org.abs_models.crowbar.main.FunctionRepos.functionNameSMT
import org.abs_models.crowbar.main.applyBinding
import org.abs_models.crowbar.main.extractSpec
import org.abs_models.crowbar.rule.FreshGenerator
import org.abs_models.frontend.ast.*
import org.abs_models.frontend.ast.AssertStmt
import org.abs_models.frontend.ast.AssignStmt
import org.abs_models.frontend.ast.AwaitStmt
import org.abs_models.frontend.ast.IfStmt
import org.abs_models.frontend.ast.ReturnStmt
import org.abs_models.frontend.ast.Stmt
import org.abs_models.frontend.ast.ThrowStmt
import org.abs_models.frontend.ast.WhileStmt
import org.abs_models.frontend.typechecker.Type
import org.abs_models.frontend.typechecker.TypeParameter
import org.abs_models.frontend.typechecker.UnknownType

/**
 *   Translates the ABS AST into our IR
 */


fun translateStatement(input: Stmt?, subst: Map<String, Expr>) : org.abs_models.crowbar.data.Stmt {
    if(input == null) return SkipStmt
    val returnType =
        if(input.contextMethod != null) input.contextMethod.type
        else UnknownType.INSTANCE

    when(input){
        is org.abs_models.frontend.ast.SkipStmt -> return SkipStmt
        is ExpressionStmt ->{
            val loc = FreshGenerator.getFreshProgVar(input.type)
            val exp = input.exp
            val type = input.type
            return when(exp) {
                is GetExp       -> SyncStmt(loc, translateExpression(exp, returnType, subst,true).first, extractResolves(input), FreshGenerator.getFreshPP())
                is NewExp       -> AllocateStmt(loc, translateExpression(exp, returnType, subst,true).first)
                is AsyncCall    -> CallStmt(loc, translateExpression(exp.callee, returnType, subst,true).first, translateExpression(exp, returnType, subst,true).first as CallExpr)
                is SyncCall     -> desugar(loc, type, exp, returnType, subst)
                else            -> {

                    val expr = translateExpression(exp, returnType, subst, false)
                    appendDesugaredCaseExprs(expr.second, ExprStmt(expr.first))
                } // Cannot be SkipStmt, as an expression can throw an exception
            }
        }
        is VarDeclStmt -> {

            if(input.varDecl.name in specialKeywords) throw Exception("VarDecl cannot be named with special keywords: $input")
            val loc = ProgVar(input.varDecl.name, input.varDecl.type)
            return when(val exp = input.varDecl.initExp ?: NullExp()) {
                is GetExp       -> SyncStmt(loc, translateExpression(exp, returnType, subst,true).first, extractResolves(input), FreshGenerator.getFreshPP())
                is NewExp       -> AllocateStmt(loc, translateExpression(exp, returnType, subst, true).first)
                is AsyncCall    -> CallStmt(loc, translateExpression(exp.callee, returnType, subst, true).first, translateExpression(exp, returnType, subst,true).first as CallExpr)
                is SyncCall     -> desugar(loc, input.type, exp, returnType, subst)

                else -> {
                    val expr = translateExpression(exp, returnType, subst, false)
                    appendDesugaredCaseExprs(expr.second, org.abs_models.crowbar.data.AssignStmt(loc,expr.first))
                }
            }
        }
        is AssignStmt -> {
            val loc:Location = if(input.varNoTransform is FieldUse) Field(input.varNoTransform.name+"_f",input.varNoTransform.type)
            else ProgVar(
                input.varNoTransform.name,
                input.varNoTransform.type
            )
            return when(val exp = input.valueNoTransform) {
                is GetExp       -> SyncStmt(loc, translateExpression(exp, returnType, subst, true).first, extractResolves(input), FreshGenerator.getFreshPP())
                is NewExp       -> AllocateStmt(loc, translateExpression(exp, returnType, subst, true).first)
                is AsyncCall    -> CallStmt(loc, translateExpression(exp.callee, returnType, subst, true).first, translateExpression(exp, returnType, subst,true).first as CallExpr)
                is SyncCall     -> desugar(loc, input.type, exp, returnType, subst)

                else -> {
                    val expr = translateExpression(exp, returnType, subst, false)
                    appendDesugaredCaseExprs(expr.second, org.abs_models.crowbar.data.AssignStmt(loc,expr.first))
                }
            }
        }
        is Block -> {
            val subs = input.stmts.map {translateStatement(it, subst)  }
            if(subs.isEmpty())  return SkipStmt
            val last = subs.last()
            val tail = subs.dropLast(1)
            return tail.foldRight( last) { nx, acc -> appendStmt(nx, acc) }
        }
        is WhileStmt -> {
            val expr = translateExpression(input.conditionNoTransform, returnType, subst, false)
            return appendDesugaredCaseExprs(expr.second, org.abs_models.crowbar.data.WhileStmt(expr.first,
                translateStatement(input.bodyNoTransform, subst),
                FreshGenerator.getFreshPP(),
                extractSpec(input,"WhileInv", returnType)))
        }
        is AwaitStmt -> return org.abs_models.crowbar.data.AwaitStmt(translateGuard(input.guard, returnType, subst),FreshGenerator.getFreshPP())
        is SuspendStmt -> return org.abs_models.crowbar.data.AwaitStmt(Const("true", input.model.boolType),FreshGenerator.getFreshPP()) // We should be able to model a suspend; as an await True;
        is ReturnStmt -> {
            val expr = translateExpression(input.retExp, returnType, subst, false)
            return appendDesugaredCaseExprs(expr.second, org.abs_models.crowbar.data.ReturnStmt(expr.first))
        }
        is IfStmt -> {
            val expr = translateExpression(input.conditionNoTransform, returnType, subst, false)
            return appendDesugaredCaseExprs(expr.second, org.abs_models.crowbar.data.IfStmt(expr.first, translateStatement(input.then, subst), translateStatement(input.`else`, subst)))
        }
        is AssertStmt -> {
            val expr = translateExpression(input.condition, returnType, subst, false)
            return appendDesugaredCaseExprs(expr.second, org.abs_models.crowbar.data.AssertStmt(expr.first))
        }
        is CaseStmt -> {
            var list : List<Branch> = emptyList()

            for (br in input.branchList) {
                val wildCards = br.left.freePatternVars.map { Pair(it.`var`.name, FreshGenerator.createPlaceholder(it.`var`.type)) }
                val newSubst = subst.toMutableMap().plus(wildCards)
                val patt = translatePattern(br.left, input.expr.type, returnType, newSubst)
                val next = translateStatement(br.right, newSubst)
                list = list + Branch(patt, next)
            }
            val expr = translateExpression(input.expr, returnType, subst, false)
            return appendDesugaredCaseExprs(expr.second, BranchStmt(expr.first, BranchList(list)))
        }
        is DieStmt -> return org.abs_models.crowbar.data.AssertStmt(Const("False", input.model.boolType))
        is MoveCogToStmt -> throw Exception("Statements ${input::class} are not coreABS" )
        is DurationStmt -> throw Exception("Statements ${input::class} are not coreABS" )
        is ThrowStmt -> {
            val expr = translateExpression(input.reason, returnType, subst, false)
            return appendDesugaredCaseExprs(expr.second, org.abs_models.crowbar.data.ThrowStmt(expr.first))
        }
        is TryCatchFinallyStmt -> {
            val inner = translateStatement(input.body, subst)
            var list : List<Branch> = emptyList()
            for (br in input.catchList) {
                val patt = translatePattern(br.left, returnType, input.model.exceptionType, subst)
                val next = translateStatement(br.right, subst)
                list = list + Branch(patt, next)
            }
            val pp = FreshGenerator.getFreshPP()
            val finally = translateStatement(input.finally, subst)
            val sFirst = TryPushStmt(ConcreteExceptionScope(BranchList(list), finally, pp))
            return appendStmt(appendStmt(sFirst, inner), TryPopStmt(pp))
        }
        //this is the foreach statement only and should not occur
        else -> throw Exception("Translation of ${input::class} not supported, please flatten the model before passing it to Crowbar" )
    }
}

fun translateExpression(input: Exp, returnType: Type, subst : Map<String, Expr>, fullExpr:Boolean, map: Map<TypeParameter, Type> = mapOf()) : Pair<Expr, List<org.abs_models.crowbar.data.Stmt>> {
    val converted = when(input){
        is FieldUse -> {
            if(input.name in specialKeywords) throw Exception("Fields cannot be named with special keywords: $input")
            if(input.contextDecl is InterfaceDecl)
                throw Exception("fields cannot be referred to in the declaration of interfaces: " +
                        "field $input is referred to in the declaration of ${input.contextDecl.name}")
            val type = if (input.type.isUnknownType) {
                            if(input.contextDecl.locallookupVarOrFieldName(input.name, true) == null)
                                throw Exception("Field ${input.name} not defined")
                        applyBinding(input.contextDecl.locallookupVarOrFieldName(input.name, true).type ,map)
                        } else applyBinding(input.type, map)
            Pair(Field(input.name + "_f",type), listOf())
        }
        is LetExp          ->{
            val innerExpr = translateExpression(input.`val`, returnType, subst, fullExpr,map)
            val outerExpr =  translateExpression(input.exp, returnType, subst + Pair(input.`var`.name, innerExpr.first), fullExpr,map)
            Pair(outerExpr.first, innerExpr.second + outerExpr.second)
        }//this handles overwrite correctly
        is IntLiteral      -> Pair(Const(input.content, input.model.intType), listOf())
        is GetExp          -> {
            val expr = translateExpression(input.pureExp, returnType, subst, fullExpr,map)
            Pair(readFut(expr.first), expr.second)
        }

        is NewExp          ->{
            val exprs = input.paramList.map { translateExpression(it, returnType, subst, fullExpr) }
            val stmts = exprs.map{it.second}.flatten()
            Pair(FreshGenerator.getFreshObjectId(input.type.qualifiedName, exprs.map { it.first } ,applyBinding(input.type, map)),stmts)//todo:add "implements" information to Repos
        }
        is NullExp         -> Pair(Const("0", input.model.intType), listOf())
        is ThisExp         -> Pair(Const("1", input.model.intType), listOf())
        is VarUse -> {
            if(input.name in specialKeywords) throw Exception("VarUse cannot be named with special keywords: $input")
            if (input.name == "result") {
                if (returnType.isUnknownType)
                    throw Exception("result type cannot be <UNKNOWN>")
                Pair(ReturnVar(returnType.qualifiedName,returnType), listOf())
            } else {
                val type = applyBinding(input.type, map)
                if (input.type.isFutureType) {
                    Pair(ProgVar(input.name, type), listOf())
                }
                else if(subst.keys.contains(input.name)){
                    Pair(subst[input.name]!!, listOf())
                } else
                    Pair(ProgVar(input.name, type), listOf())
            }
        }
        is Binary -> {
            val op = when (input) {
                is GTEQExp -> ">="
                is LTEQExp -> "<="
                is GTExp -> ">"
                is LTExp -> "<"
                is EqExp -> "="
                is NotEqExp -> "!="
                is AddAddExp -> "+"
                is SubAddExp -> "-"
                is MultMultExp -> "*"
                is DivMultExp -> "/"
                is AndBoolExp -> "&&"
                is OrBoolExp -> "||"
                else -> throw Exception("Translation of data ${input::class} not supported, term is $input")
            }
            val exprLeft = translateExpression(input.left, returnType, subst, fullExpr,map)
            val exprRight = translateExpression(input.right, returnType, subst, fullExpr,map)
            Pair(SExpr(op, listOf(exprLeft.first, exprRight.first)), exprLeft.second + exprRight.second)
        }
        is Unary -> {
            val op = when(input){
                is MinusExp     -> "-"
                is NegExp       -> "!"
                else            -> throw Exception("Translation of data ${input::class} not supported, term is $input" )
            }
            val expr = translateExpression(input.operand, returnType, subst, fullExpr,map)
            Pair(SExpr(op, listOf(expr.first)), expr.second)
        }
        is DataConstructorExp -> {
            if(input.dataConstructor == null){
                throw Exception("Data constructor ${input.constructor} not defined")
            }
            if(input.type.isUnknownType)
                throw Exception("Wrong use of data constructor ${input.constructor} with parameters ${input.paramList} ")
            when (input.dataConstructor!!.name) {
                "Unit" -> Pair(unitExpr(), listOf())
                "True" -> Pair(Const("true", input.model.boolType), listOf())
                "False" -> Pair(Const("false", input.model.boolType), listOf())
                else -> {
                    val exprs = input.params.map { translateExpression(it, returnType, subst, fullExpr,map) }
                    val stmts = exprs.map{it.second}.flatten()
                    val newType = applyBinding(input.type, map)
                    Pair(DataTypeExpr(input.dataConstructor!!.qualifiedName, newType.qualifiedName, newType, exprs.map{it.first}), stmts)
                }
            }
        }
        is FnApp -> {
            if (input.name in specialKeywordNoHeap) {
                throw Exception("FnApp cannot be named with special keywords: ${input.name}")
            } else {
                if (input.name == "valueOf") {
                    val expr = translateExpression(input.params.getChild(0), returnType, subst, fullExpr,map)
                    Pair(readFut(expr.first), expr.second)
                } else if (input.name in FunctionRepos.builtInFunctionNames) {

                    val exprs = input.params.map { translateExpression(it, returnType, subst, fullExpr,map) }
                    val stmts = exprs.map { it.second }.flatten()

                    Pair(SExpr(input.name, exprs.map { it.first }), stmts)
                } else if (input.name == "hasRole") {
                    val roleConst =
                        Const("\"${(input.params.getChild(1) as StringLiteral).content}\"", input.model.stringType)
                    val field = translateExpression(input.params.getChild(0), returnType, subst, fullExpr,map)
                    Pair(SExpr("hasRole", listOf(field.first, roleConst)), field.second)
                } else if (input.decl is UnknownDecl) {
                    if (specialHeapKeywords.containsKey(input.name)) {

                        val exprs = input.params.map { translateExpression(it, returnType, subst, fullExpr,map) }
                        val stmts = exprs.map { it.second }.flatten()

                        Pair(SExpr(input.name, exprs.map { it.first }), stmts)
                    } else
                        throw Exception("Unknown declaration of function ${input.name}")
                } else if (FunctionRepos.isKnown(input.decl.qualifiedName) || functionNameSMT(input.decl as FunctionDecl) in FunctionRepos.parametricFunctions) {
                    val exprs = input.params.map { translateExpression(it, returnType, subst, fullExpr,map) }
                    val stmts = exprs.map { it.second }.flatten()
                    Pair(SExpr(functionNameSMT(input.decl as FunctionDecl), exprs.map { it.first }), stmts)
                } else if (input.decl.qualifiedName == "ABS.StdLib.random") {
                    Pair(
                        FreshGenerator.getFreshProgVar(input.model.intType),
                        listOf<org.abs_models.crowbar.data.Stmt>()
                    )
                } else throw Exception("Translation of FnApp is not fully supported, term is $input with function ${input.decl.qualifiedName}")
            }
        }
        is IfExp -> {
            val condExpr = translateExpression(input.condExp, returnType, subst, fullExpr,map)
            val thenExpr = translateExpression(input.thenExp, returnType, subst, fullExpr,map)
            val elseExpr = translateExpression(input.elseExp, returnType, subst, fullExpr,map)
            Pair((SExpr("ite", listOf(condExpr.first,thenExpr.first,elseExpr.first))), condExpr.second+thenExpr.second+elseExpr.second)
        }
        is Call -> {
            val met = input.methodSig.contextDecl.qualifiedName+"."+input.methodSig.name
            val params = input.params.map {  translateExpression(it, returnType, subst,true,map).first }

            if(input is AsyncCall || input.callee  !is ThisExp)
                Pair(CallExpr(met, params), listOf())
            else
                Pair(SyncCallExpr(met, params), listOf())
        }
        is CaseExp ->{
            if(!fullExpr) {
                val newVar = FreshGenerator.getFreshProgVar(returnType)
                val matchExpr = translateExpression(input.expr, returnType, subst, fullExpr,map)


                val branchExprs = input.branchList.map {br ->

                    val wildCards = br.left.freePatternVars.map { Pair(it.`var`.name, FreshGenerator.createPlaceholder(applyBinding(it.`var`.type, map))) }
                    val newSubst = subst.toMutableMap().plus(wildCards)
                    Pair(
                        translatePattern(br.left, applyBinding(br.patternExpType, map), returnType, newSubst,map),
                        translateExpression(br.right, returnType, newSubst, fullExpr,map)
                    )
                }

                val stmts = matchExpr.second + branchExprs.map { it.second.second }
                    .flatten() + org.abs_models.crowbar.data.AssignStmt(newVar, Const("0", input.model.intType))

                val list: MutableList<Branch> = branchExprs.map {
                    Branch(it.first, org.abs_models.crowbar.data.AssignStmt(newVar, it.second.first))
                }.toMutableList()
                if(list.last().matchTerm !is ConstructorPattern)
                    list.add(Branch(FreshGenerator.getFreshWildCard(applyBinding(input.expr.type, map)),org.abs_models.crowbar.data.AssignStmt(newVar, FreshGenerator.getFreshProgVar(returnType))))

                Pair(newVar, stmts + BranchStmt(matchExpr.first, BranchList(list)))
            }else {
                Pair(CaseExpr(translateExpression(input.expr, returnType, subst,true,map).first,
                    ADTRepos.libPrefix(applyBinding(input.type, map).qualifiedName),
                    input.branchList.map {br ->
                        val wildCards = br.left.freePatternVars.map { Pair(it.`var`.name, FreshGenerator.createPlaceholder(applyBinding((it.`var`.type), map))) }
                        val newSubst = subst.toMutableMap().plus(wildCards)
                        BranchExpr(
                            translatePattern(br.left, applyBinding(br.patternExpType, map), returnType, newSubst,map),
                            translateExpression(br.right, returnType, newSubst,true,map).first)}, input.freeVars, applyBinding(input.type, map)),
                    listOf()
                )
            }
        }
        is StringLiteral -> {
            Pair(Const("\"" + input.content +"\"", input.model.stringType), listOf<org.abs_models.crowbar.data.Stmt>())
        }
        is FloatLiteral -> {
            Pair(Const(input.content, input.model.floatType), listOf<org.abs_models.crowbar.data.Stmt>())
        }
        is AsExp -> {
            val inputExpr = translateExpression(input.exp,returnType, subst, fullExpr,map)
            val implements = ImplementsExpr(inputExpr.first,applyBinding(input.type, map))
            val res = SExpr("ite",
                listOf(
                    SExpr("and", listOf(SExpr("not", listOf(SExpr("=", listOf(inputExpr.first, Const("0", input.model.intType))))),
                    implements)),
                    inputExpr.first,
                    Const("0", input.model.intType)))
            Pair(res, inputExpr.second as List<org.abs_models.crowbar.data.Stmt>)
        }
        is ImplementsExp -> {
            val expr = translateExpression(input.exp, returnType, subst, fullExpr,map)
            Pair(ImplementsExpr(expr.first, applyBinding(input.interfaceTypeUse.type, map)), expr.second as List<org.abs_models.crowbar.data.Stmt>)
        }
        else -> throw Exception("Translation of ${input::class} not supported, term is $input" )
    }

    // Save reference to original expression
    converted.first.absExp = input
    return converted
}

fun translateGuard(input: Guard, returnType: Type, subst: Map<String, Expr>) : Expr =
    when(input){
        is ExpGuard -> translateExpression(input.pureExp, returnType, subst, false).first
        is AndGuard -> SExpr("&&",listOf(translateGuard(input.left, returnType, subst), translateGuard(input.right, returnType, subst)))
        is ClaimGuard -> {
            val placeholder = Const("true")
            placeholder.absExp = input.`var` // Save reference to original guard expression
            placeholder
        }
        else -> throw Exception("Guards ${input::class} are not coreABS" )
    }

fun translatePattern(pattern : Pattern, overrideType : Type, returnType:Type, subst: Map<String, Expr>,map : Map<TypeParameter, Type> = mapOf()) : Expr =
    when (pattern) {
        is PatternVarUse -> if (pattern.name in subst) subst[pattern.name]!! else ProgVar(pattern.name, applyBinding(pattern.type, map))
        is PatternVar -> if (pattern.`var`.name in subst) subst[pattern.`var`.name]!! else ProgVar(pattern.`var`.name, applyBinding(pattern.type, map))
        is LiteralPattern -> translateExpression(pattern.literal, returnType, subst,true,map).first
        is UnderscorePattern ->  FreshGenerator.getFreshWildCard(overrideType)
        is ConstructorPattern -> {
            val qualName = if(returnType == pattern.moduleDecl.model.exceptionType) "ABS.StdLib.Exceptions.${pattern.constructor}"
            else if(pattern.constructor == "True" || pattern.constructor == "False")
                pattern.constructor.toLowerCase()
            else if(pattern.type.qualifiedName.startsWith("ABS.StdLib.")) {
                "ABS.StdLib.${pattern.constructor}"
            }
            else typeWithModule(pattern.constructor, pattern.moduleDecl.name)
            DataTypeExpr(qualName,applyBinding(pattern.type, map).qualifiedName,applyBinding(pattern.type, map),pattern.params.map { translatePattern(it,applyBinding(it.inhType,map), returnType, subst,map) })
        }
        else -> throw Exception("Translation of complex constructors is not supported")
    }

fun typeWithModule(type : String, moduleName : String) :String {
    var constructor = type
    if(!constructor.startsWith("$moduleName."))
        constructor =  "$moduleName.$type"
    return constructor
}

fun filterAtomic(input: Stmt?, app : (Stmt) -> Boolean) : Set<Stmt> {
    if (input == null) return emptySet()
    return when (input) {
        is Block -> input.stmts.fold(emptySet()) { acc, nx -> acc + filterAtomic(nx, app) }
        is WhileStmt -> filterAtomic(input.body, app)
        is IfStmt -> filterAtomic(input.then, app) + filterAtomic(input.`else`, app)
        else -> if (app(input)) setOf(input) else emptySet()
    }
}

/* Extracts the resolves set for get statements */
fun extractResolves(stmt: Stmt): ConcreteStringSet{
    val spec = stmt.annotations.firstOrNull { it.type.toString()
        .endsWith(".Spec") && it.value is DataConstructorExp && (it.value as DataConstructorExp).constructor == "Resolves" }
        ?: return ConcreteStringSet()
    val inner = ((spec.value as DataConstructorExp).params.getChild(0) as StringLiteral).content.split(",").map { it.trim() }
    return ConcreteStringSet(inner.toSet())
}

/* We need to perform the rewritting on sync call ourselves as the version of the compiler we use still uses the old broken location types */
fun desugar(loc: Location, type: Type, syncCall: SyncCall, returnType :Type, subst: Map<String, Expr>) : org.abs_models.crowbar.data.Stmt{
    val calleeExpr = translateExpression(syncCall.callee, returnType, subst,true).first
    val callExpr = translateExpression(syncCall, returnType, subst,true).first

    if(syncCall.callee is ThisExp)
        return SyncCallStmt(loc, calleeExpr, callExpr as SyncCallExpr)

    val fut = FreshGenerator.getFreshProgVar(type)
    val callStmt = CallStmt(fut, calleeExpr, callExpr as CallExpr)
    val syncStmt = SyncStmt(loc, readFut(fut), ConcreteStringSet(setOf(syncCall.methodSig.name)), FreshGenerator.getFreshPP())
    return SeqStmt(callStmt, syncStmt)
}

fun appendDesugaredCaseExprs(desugaredCaseExprs:List<org.abs_models.crowbar.data.Stmt>, stmt: org.abs_models.crowbar.data.Stmt):org.abs_models.crowbar.data.Stmt{
    return appendStmt(appendListStmt(desugaredCaseExprs), stmt)
}

fun appendListStmt(stmtList:List<org.abs_models.crowbar.data.Stmt>):org.abs_models.crowbar.data.Stmt{
    return  stmtList.fold(SkipStmt as org.abs_models.crowbar.data.Stmt){ appended, it-> appendStmt(appended,it) }
}
