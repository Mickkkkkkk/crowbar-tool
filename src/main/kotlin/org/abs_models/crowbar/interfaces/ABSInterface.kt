package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Const
import org.abs_models.crowbar.data.SkipStmt
import org.abs_models.crowbar.main.ADTRepos
import org.abs_models.crowbar.main.FunctionRepos
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
                is GetExp       -> SyncStmt(loc, translateExpression(exp, returnType, subst), extractResolves(input), FreshGenerator.getFreshPP())
                is NewExp       -> AllocateStmt(loc, translateExpression(exp, returnType, subst))
                is AsyncCall    -> CallStmt(loc, translateExpression(exp.callee, returnType, subst), translateExpression(exp, returnType, subst) as CallExpr)
                is SyncCall     -> desugar(loc, type, exp, returnType, subst)
                else            -> ExprStmt(translateExpression(exp, returnType, subst)) // Cannot be SkipStmt, as an expression can throw an exception
            }
        }
        is VarDeclStmt -> {
            val loc = ProgVar(input.varDecl.name, input.varDecl.type)
            return when(val exp = input.varDecl.initExp ?: NullExp()) {
                is GetExp       -> SyncStmt(loc, translateExpression(exp, returnType, subst), extractResolves(input), FreshGenerator.getFreshPP())
                is NewExp       -> AllocateStmt(loc, translateExpression(exp, returnType, subst))
                is AsyncCall    -> CallStmt(loc, translateExpression(exp.callee, returnType, subst), translateExpression(exp, returnType, subst) as CallExpr)
                is SyncCall     -> desugar(loc, input.type, exp, returnType, subst)
                else -> org.abs_models.crowbar.data.AssignStmt(loc, translateExpression(exp, returnType, subst))
            }
        }
        is AssignStmt -> {
            val loc:Location = if(input.varNoTransform is FieldUse) Field(input.varNoTransform.name+"_f",input.varNoTransform.type)
            else ProgVar(
                input.varNoTransform.name,
                input.varNoTransform.type
            )
            return when(val exp = input.valueNoTransform) {
                is GetExp       -> SyncStmt(loc, translateExpression(exp, returnType, subst), extractResolves(input), FreshGenerator.getFreshPP())
                is NewExp       -> AllocateStmt(loc, translateExpression(exp, returnType, subst))
                is AsyncCall    -> CallStmt(loc, translateExpression(exp.callee, returnType, subst), translateExpression(exp, returnType, subst) as CallExpr)
                is SyncCall     -> desugar(loc, input.type, exp, returnType, subst)
                else -> org.abs_models.crowbar.data.AssignStmt(loc, translateExpression(exp, returnType, subst))
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
            return org.abs_models.crowbar.data.WhileStmt(translateExpression(input.conditionNoTransform, returnType, subst),
                translateStatement(input.bodyNoTransform, subst),
                FreshGenerator.getFreshPP(),
                extractSpec(input,"WhileInv", returnType))
        }
        is AwaitStmt -> return org.abs_models.crowbar.data.AwaitStmt(translateGuard(input.guard, returnType, subst),FreshGenerator.getFreshPP())
        is SuspendStmt -> return org.abs_models.crowbar.data.AwaitStmt(Const("true", input.model.boolType),FreshGenerator.getFreshPP()) // We should be able to model a suspend; as an await True;
        is ReturnStmt -> return org.abs_models.crowbar.data.ReturnStmt(translateExpression(input.retExp, returnType, subst))
        is IfStmt -> return org.abs_models.crowbar.data.IfStmt(translateExpression(input.conditionNoTransform, returnType, subst), translateStatement(input.then, subst), translateStatement(input.`else`, subst))
        is AssertStmt -> return org.abs_models.crowbar.data.AssertStmt(translateExpression(input.condition, returnType, subst))
        is CaseStmt -> {
            if(isGeneric(input.expr.type))
                throw Exception("Generics not supported as match term for CaseStmt: ${input.expr}:${input.expr.type}")
            var list : List<Branch> = emptyList()
            for (br in input.branchList) {
                val patt = translatePattern(br.left, input.expr.type, returnType, subst)
                val next = translateStatement(br.right, subst)
                list = list + Branch(patt, next)
            }
            return BranchStmt(translateExpression(input.expr, returnType, subst), BranchList(list))
        }
        is DieStmt -> return org.abs_models.crowbar.data.AssertStmt(Const("False", input.model.boolType))
        is MoveCogToStmt -> throw Exception("Statements ${input::class} are not coreABS" )
        is DurationStmt -> throw Exception("Statements ${input::class} are not coreABS" )
        is ThrowStmt -> return org.abs_models.crowbar.data.ThrowStmt(translateExpression(input.reason, returnType, subst))
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

fun translateExpression(input: Exp, returnType: Type, subst : Map<String, Expr>) : Expr {
    val converted = when(input){
        is FieldUse -> {
            if(input.contextDecl is InterfaceDecl)
                throw Exception("fields cannot be referred to in the declaration of interfaces: " +
                        "field $input is referred to in the declaration of ${input.contextDecl.name}")
            val type = if (input.type.isUnknownType) {
                            if(input.contextDecl.locallookupVarOrFieldName(input.name, true) == null)
                                throw Exception("Field ${input.name} not defined")
                            input.contextDecl.locallookupVarOrFieldName(input.name, true).type
                        } else input.type
            Field(input.name + "_f",type)
        }
        is LetExp          ->
            translateExpression(input.exp, returnType, subst + Pair(input.`var`.name, translateExpression(input.`val`, returnType, subst))) //this handles overwrite correctly
        is IntLiteral      -> Const(input.content, input.model.intType)
        is GetExp          -> readFut(translateExpression(input.pureExp, returnType, subst))
        is NewExp          -> FreshGenerator.getFreshObjectId(input.type.qualifiedName, input.paramList.map { translateExpression(it, returnType, subst) },input.type) //todo:add "implements" information to Repos
        is NullExp         -> Const("0", input.model.intType)
        is ThisExp         -> Const("1", input.model.intType)
        is VarUse -> {
            if (input.name == "result") {
                if (returnType.isUnknownType)
                    throw Exception("result type cannot be <UNKNOWN>")
                ReturnVar(returnType.qualifiedName,returnType)
            } else {
                if (input.type.isFutureType) {
                    ProgVar(input.name, input.type)
                }
                else if(subst.keys.contains(input.name)){
                    subst[input.name]
                } else
                    ProgVar(input.name, input.type)
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
            SExpr(op, listOf(translateExpression(input.left, returnType, subst), translateExpression(input.right, returnType, subst)))
        }
        is Unary -> {
            val op = when(input){
                is MinusExp     -> "-"
                is NegExp       -> "!"
                else            -> throw Exception("Translation of data ${input::class} not supported, term is $input" )
            }
            SExpr(op, listOf(translateExpression(input.operand, returnType, subst)))
        }
        is DataConstructorExp -> {
            if(input.dataConstructor == null){
                throw Exception("Data constructor ${input.constructor} not defined")
            }
            if(input.type.isUnknownType)
                throw Exception("Wrong use of data constructor ${input.constructor} with parameters ${input.paramList} ")
            when (input.dataConstructor!!.name) {
                "Unit" -> unitExpr()
                "True" -> Const("true", input.model.boolType)
                "False" -> Const("false", input.model.boolType)
                else -> DataTypeExpr(input.dataConstructor!!.qualifiedName, input.type.qualifiedName, input.type, input.params.map { translateExpression(it, returnType, subst) })
            }
        }
        is FnApp ->
            if (input.name == "valueOf")
                readFut(translateExpression(input.params.getChild(0), returnType, subst))
            else if(input.name in FunctionRepos.functionPairTriple) {
                SExpr(input.name, input.params.map { translateExpression(it, returnType, subst) })
            }
            else if(input.name == "abs")
                SExpr(input.name, input.params.map { translateExpression(it, returnType, subst) })
            else if (input.name == "hasRole") {
                val roleConst = Const("\"${(input.params.getChild(1) as StringLiteral).content}\"", input.model.stringType)
                val field = translateExpression(input.params.getChild(0), returnType, subst)
                SExpr("hasRole", listOf(field, roleConst))
            }
            else if (input.decl is UnknownDecl) {
                if (specialHeapKeywords.containsKey(input.name))
                    SExpr(input.name, input.params.map { translateExpression(it, returnType, subst) })
                else
                    throw Exception("Unknown declaration of function ${input.name}")
            } else if (FunctionRepos.isKnown(input.decl.qualifiedName)) {
                SExpr(input.decl.qualifiedName.replace(".", "-"), input.params.map { translateExpression(it, returnType, subst) })
            } else if(input.decl.qualifiedName == "ABS.StdLib.random"){
                FreshGenerator.getFreshProgVar(input.model.intType)
            } else throw Exception("Translation of FnApp is not fully supported, term is $input with function ${input.decl.qualifiedName}")
        is IfExp -> SExpr("ite", listOf(translateExpression(input.condExp, returnType, subst),translateExpression(input.thenExp, returnType, subst),translateExpression(input.elseExp, returnType, subst)))
        is Call -> {
            val met = input.methodSig.contextDecl.qualifiedName+"."+input.methodSig.name
            val params = input.params.map {  translateExpression(it, returnType, subst) }

            if(input is AsyncCall || input.callee  !is ThisExp)
                CallExpr(met, params)
            else
                SyncCallExpr(met, params)
        }
        is CaseExp ->{
            if(isGeneric(input.expr.type))
                throw Exception("Generics not supported as match term of CaseExpr, ${input.expr}:${input.expr.type}")
            CaseExpr(translateExpression(input.expr, returnType, subst),
                ADTRepos.libPrefix(input.type.qualifiedName),
                input.branchList.map {
                BranchExpr(
                    translatePattern(it.left, it.patternExpType, returnType, subst),
                    translateExpression(it.right, returnType, subst))}, input.freeVars,input.type)
        }
        is StringLiteral -> {
            Const("\"" + input.content +"\"", input.model.stringType)
        }
        is FloatLiteral -> {
            Const(input.content, input.model.floatType)
        }
        is AsExp -> {
            val inputExpr = translateExpression(input.exp,returnType, subst)
            val implements = ImplementsExpr(inputExpr,input.type)
            val res = SExpr("ite",
                listOf(
                    SExpr("and", listOf(SExpr("not", listOf(SExpr("=", listOf(inputExpr, Const("0", input.model.intType))))),
                    implements)),
                    inputExpr,
                    Const("0", input.model.intType)))
            res
        }
        is ImplementsExp -> {
            ImplementsExpr(translateExpression(input.exp, returnType, subst), input.interfaceTypeUse.type)
        }
        else -> throw Exception("Translation of ${input::class} not supported, term is $input" )
    }

    // Save reference to original expression
    converted!!.absExp = input
    return converted
}

fun translateGuard(input: Guard, returnType: Type, subst: Map<String, Expr>) : Expr =
    when(input){
        is ExpGuard -> translateExpression(input.pureExp, returnType, subst)
        is AndGuard -> SExpr("&&",listOf(translateGuard(input.left, returnType, subst), translateGuard(input.right, returnType, subst)))
        is ClaimGuard -> {
            val placeholder = Const("true")
            placeholder.absExp = input.`var` // Save reference to original guard expression
            placeholder
        }
        else -> throw Exception("Guards ${input::class} are not coreABS" )
    }

fun translatePattern(pattern : Pattern, overrideType : Type, returnType:Type, subst: Map<String, Expr>) : Expr =
    when (pattern) {
        is PatternVarUse -> ProgVar(pattern.name, pattern.type)
        is PatternVar -> ProgVar(pattern.`var`.name, pattern.type)
        is LiteralPattern -> translateExpression(pattern.literal, returnType, subst)
        is UnderscorePattern ->  FreshGenerator.getFreshProgVar(overrideType)
        is ConstructorPattern -> {
            val qualName = if(returnType == pattern.moduleDecl.model.exceptionType) "ABS.StdLib.Exceptions.${pattern.constructor}"
            else if(pattern.constructor == "True" || pattern.constructor == "False")
                pattern.constructor.toLowerCase()
            else if(pattern.type.qualifiedName.startsWith("ABS.StdLib."))
                pattern.type.qualifiedName
            else typeWithModule(pattern.constructor, pattern.moduleDecl.name)
            DataTypeExpr(qualName,pattern.type.qualifiedName,pattern.type,pattern.params.map { translatePattern(it,it.inhType, returnType, subst) })
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
    val calleeExpr = translateExpression(syncCall.callee, returnType, subst)
    val callExpr = translateExpression(syncCall, returnType, subst)

    if(syncCall.callee is ThisExp)
        return SyncCallStmt(loc, calleeExpr, callExpr as SyncCallExpr)

    val fut = FreshGenerator.getFreshProgVar(type)
    val callStmt = CallStmt(fut, calleeExpr, callExpr as CallExpr)
    val syncStmt = SyncStmt(loc, readFut(fut), ConcreteStringSet(setOf(syncCall.methodSig.name)), FreshGenerator.getFreshPP())
    return SeqStmt(callStmt, syncStmt)
}