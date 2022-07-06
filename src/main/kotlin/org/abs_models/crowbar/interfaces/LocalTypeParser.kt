package org.abs_models.crowbar.interfaces

import antlr.crowbar.gen.LocalSessionBaseVisitor
import antlr.crowbar.gen.LocalSessionLexer
import antlr.crowbar.gen.LocalSessionParser
import antlr.crowbar.gen.LocalSessionParser.And_type_formulaContext
import antlr.crowbar.gen.LocalSessionParser.Binary_type_termContext
import antlr.crowbar.gen.LocalSessionParser.Boolean_type_formulaContext
import antlr.crowbar.gen.LocalSessionParser.Call_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Constant_type_termContext
import antlr.crowbar.gen.LocalSessionParser.Field_type_termContext
import antlr.crowbar.gen.LocalSessionParser.Function_type_termContext
import antlr.crowbar.gen.LocalSessionParser.Get_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Nested_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Not_type_formulaContext
import antlr.crowbar.gen.LocalSessionParser.Or_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Or_type_formulaContext
import antlr.crowbar.gen.LocalSessionParser.Put_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Rep_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Seq_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Skip_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Susp_local_typeContext
import org.abs_models.crowbar.data.Const
import org.abs_models.crowbar.data.DataTypeExpr
import org.abs_models.crowbar.data.Expr
import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.LTCall
import org.abs_models.crowbar.data.LTGet
import org.abs_models.crowbar.data.LTNest
import org.abs_models.crowbar.data.LTOpt
import org.abs_models.crowbar.data.LTPut
import org.abs_models.crowbar.data.LTRep
import org.abs_models.crowbar.data.LTSeq
import org.abs_models.crowbar.data.LTSkip
import org.abs_models.crowbar.data.LTSusp
import org.abs_models.crowbar.data.LocalType
import org.abs_models.crowbar.data.ProgVar
import org.abs_models.crowbar.data.ReturnVar
import org.abs_models.crowbar.data.SExpr
import org.abs_models.crowbar.main.ADTRepos
import org.abs_models.frontend.typechecker.Type
import org.abs_models.frontend.typechecker.UnknownType
import org.antlr.v4.runtime.BaseErrorListener
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.RecognitionException
import org.antlr.v4.runtime.Recognizer

/**
 *   Parses a local session type and directly translates the AST into the internal data structure
 */

object LocalTypeParser : LocalSessionBaseVisitor<LocalType>() {

    private val noContext = Pair(UnknownType.INSTANCE, mapOf<String, Type>())
    private var formulaConverter: LocalTypeFormulaConverter = LocalTypeFormulaConverter(noContext)

    fun parse(localTypeExp: String, context: Pair<Type, Map<String, Type>>?): LocalType {
        formulaConverter = LocalTypeFormulaConverter(context ?: noContext)

        val stream = CharStreams.fromString(localTypeExp)

        val lexer = LocalSessionLexer(stream)
        lexer.removeErrorListeners()
        lexer.addErrorListener(ThrowingErrorListener)

        val tokens = CommonTokenStream(lexer)
        val parser = LocalSessionParser(tokens)
        parser.removeErrorListeners()
        parser.addErrorListener(ThrowingErrorListener)

        try {
            return parser.local().accept(this)
        } catch (e: LocalTypeParsingException) {
            throw Exception("Could not parse local type expression '$localTypeExp':\n${e.message}")
        }
    }

    override fun visitCall_local_type(ctx: Call_local_typeContext): LocalType {
        val role = ctx.role().STRING().text
        val method = ctx.STRING().text
        val formula = ctx.formula()?.accept(formulaConverter) ?: Const("true")

        return LTCall(role, method, formula)
    }

    override fun visitRep_local_type(ctx: Rep_local_typeContext): LocalType {
        val inner = ctx.local().accept(this)
        return LTRep(inner)
    }

    override fun visitPut_local_type(ctx: Put_local_typeContext): LocalType {
        val formula = ctx.formula()?.accept(formulaConverter) ?: Const("true")
        return LTPut(formula)
    }

    override fun visitSkip_local_type(ctx: Skip_local_typeContext): LocalType {
        return LTSkip
    }

    override fun visitNested_local_type(ctx: Nested_local_typeContext): LocalType {
        return LTNest(ctx.local().accept(this))
    }

    override fun visitOr_local_type(ctx: Or_local_typeContext): LocalType {
        val left = ctx.local(0).accept(this)
        val right = ctx.local(1).accept(this)
        return LTOpt(left, right)
    }

    override fun visitGet_local_type(ctx: Get_local_typeContext): LocalType {
        val term = ctx.term().accept(formulaConverter)!!
        return LTGet(term)
    }

    override fun visitSusp_local_type(ctx: Susp_local_typeContext): LocalType {
        val formula = ctx.formula()?.accept(formulaConverter) ?: Const("true")
        return LTSusp(formula)
    }

    override fun visitSeq_local_type(ctx: Seq_local_typeContext): LocalType {
        val first = ctx.local(0).accept(this)
        val second = ctx.local(1).accept(this)
        return LTSeq(first, second)
    }
}

// Sub-converter for terms and formulas in local type expressions
class LocalTypeFormulaConverter(context: Pair<Type, Map<String, Type>>) : LocalSessionBaseVisitor<Expr>() {
    private val methodReturnType = context.first
    private val fieldTypeMapping = context.second

    // Build a mapping from possible data type constructor names to their declarations
    // this is the only way we can distinguish a data type constructor from a function / a program variable
    private val dataTypeConstructors = ADTRepos.dTypesDecl.map {
        datatype -> datatype.dataConstructorList.map { constructor -> Pair(constructor.name, datatype) }
    }.flatten().associate { it }

    override fun visitOr_type_formula(ctx: Or_type_formulaContext): SExpr {
        val left = ctx.formula(0).accept(this) as Expr
        val right = ctx.formula(1).accept(this) as Expr
        return SExpr("||", listOf(left, right))
    }

    override fun visitBoolean_type_formula(ctx: Boolean_type_formulaContext): Expr {
        val term = ctx.term().accept(this) as Expr
        return SExpr("=", listOf(term, Const("true")))
    }

    override fun visitNot_type_formula(ctx: Not_type_formulaContext): Expr {
        return SExpr("!", listOf(ctx.formula().accept(this) as Expr))
    }

    override fun visitAnd_type_formula(ctx: And_type_formulaContext): Expr {
        val left = ctx.formula(0).accept(this) as Expr
        val right = ctx.formula(1).accept(this) as Expr
        return SExpr("&&", listOf(left, right))
    }

    override fun visitFunction_type_term(ctx: Function_type_termContext): Expr {
        val name = ctx.STRING().text
        val args = ctx.termlist().term().map { it.accept(this) as Expr }
        return if (dataTypeConstructors.containsKey(name))
                buildDataType(name, args)
            else
                SExpr(name, args)
    }

    override fun visitBinary_type_term(ctx: Binary_type_termContext): Expr {
        val op = ctx.binop().text
        val left = ctx.term(0).accept(this) as Expr
        val right = ctx.term(1).accept(this) as Expr
        return SExpr(if (op == "==") "=" else op, listOf(left, right))
    }

    override fun visitField_type_term(ctx: Field_type_termContext): Expr {
        val name = ctx.STRING().text
        val type = fieldTypeMapping[name] ?: UnknownType.INSTANCE
        return Field(name + "_f", type)
    }

    override fun visitConstant_type_term(ctx: Constant_type_termContext): Expr {
        val text = ctx.STRING().text
        return when {
            text == "null"   -> Const("0")
            text == "this"   -> Const("1")
            text == "true"   -> Const("true")
            text == "false"  -> Const("false")
            text == "True"   -> Const("true")
            text == "False"  -> Const("false")
            text == "result" -> ReturnVar(methodReturnType)
            text matches Regex("[0-9]+") -> Const(text)
            dataTypeConstructors.containsKey(text) -> buildDataType(text)
            else -> ProgVar(text, UnknownType.INSTANCE)
        }
    }

    private fun buildDataType(name: String, args: List<Expr> = emptyList()): Expr {
        val decl = dataTypeConstructors[name]!!
        val constructor = decl.dataConstructorList.first { it.name == name }
        return DataTypeExpr(constructor.qualifiedName, constructor.type.qualifiedName, constructor.type, args)
    }
}

class LocalTypeParsingException(msg: String) : Exception(msg)

object ThrowingErrorListener : BaseErrorListener() {
    override fun syntaxError(recognizer: Recognizer<*, *>, offendingSymbol: Any?, line: Int, charPositionInLine: Int, msg: String, e: RecognitionException?) {
        throw LocalTypeParsingException("Error at position $line:$charPositionInLine $msg")
    }
}
