package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.Location
import org.abs_models.crowbar.data.ProgVar
import org.abs_models.crowbar.tree.InfoAwaitUse
import org.abs_models.crowbar.tree.InfoCallAssign
import org.abs_models.crowbar.tree.InfoClassPrecondition
import org.abs_models.crowbar.tree.InfoGetAssign
import org.abs_models.crowbar.tree.InfoIfElse
import org.abs_models.crowbar.tree.InfoIfThen
import org.abs_models.crowbar.tree.InfoInvariant
import org.abs_models.crowbar.tree.InfoLocAssign
import org.abs_models.crowbar.tree.InfoLoopInitial
import org.abs_models.crowbar.tree.InfoLoopPreserves
import org.abs_models.crowbar.tree.InfoLoopUse
import org.abs_models.crowbar.tree.InfoNullCheck
import org.abs_models.crowbar.tree.InfoObjAlloc
import org.abs_models.crowbar.tree.InfoReturn
import org.abs_models.crowbar.tree.InfoScopeClose
import org.abs_models.crowbar.tree.InfoSkip
import org.abs_models.crowbar.tree.InfoSkipEnd
import org.abs_models.crowbar.tree.NoInfo
import org.abs_models.crowbar.tree.NodeInfoVisitor
import org.abs_models.frontend.ast.FieldUse

object NodeInfoRenderer : NodeInfoVisitor<String> {

    private var indentLevel = 0
    private var indentString = "\t"

    private var objectCounter = 0
    private val varDefs = mutableSetOf<String>()
    private var model = EmptyModel

    fun reset(newModel: Model) {
        model = newModel
        indentLevel = 0
        objectCounter = 0
        varDefs.clear()
    }

    fun initAssignments(): String {
        val initAssign = model.initState.map { renderModelAssignment(it.first, it.second) }.joinToString("\n")
        return indent("// Assume the following pre-state:\n$initAssign\n// End of setup\n\n")
    }

    override fun visit(info: InfoAwaitUse): String {
        val postHeap = model.heapMap[info.heapExpr]

        val assignmentBlock: String
        if (postHeap == null)
            assignmentBlock = "// No heap modification info available for this call"
        else {
            val assignments = postHeap.map { renderModelAssignment(it.first, it.second) }.joinToString("\n")
            assignmentBlock = "// Assume the following assignments during the async call:\n$assignments\n// End assignments"
        }

        val renderedGuard = if (info.guard.absExp is FieldUse) "${renderExpression(info.guard)}?" else renderExpression(info.guard)

        return indent("\n// await $renderedGuard;\n$assignmentBlock\n")
    }

    override fun visit(info: InfoClassPrecondition) = ""

    override fun visit(info: InfoNullCheck) = ""

    override fun visit(info: InfoIfElse): String {
        val res =  indent("if(${renderExpression(info.guard)}){}\nelse{")
        indentLevel += 1

        return res
    }

    override fun visit(info: InfoIfThen): String {
        val res = indent("if(${renderExpression(info.guard)}){")
        indentLevel += 1
        return res
    }

    override fun visit(info: InfoInvariant) = ""

    override fun visit(info: InfoLocAssign): String {
        val location = renderDeclLocation(info.lhs, fut2str = true)

        return indent("$location = ${renderExpression(info.expression)};")
    }

    override fun visit(info: InfoGetAssign): String {
        val location = renderDeclLocation(info.lhs, fut2str = false)

        val origGet = "// $location = ${renderExpression(info.expression)};"

        val futureValue = model.futMap[info.futureExpr]
        val getReplacement = if (futureValue != null) "${futureToString(location)} = $futureValue;" else "// No future evaluation info available"

        return indent("$origGet\n$getReplacement")
    }

    override fun visit(info: InfoCallAssign): String {
        val location = renderDeclLocation(info.lhs, fut2str = false)

        val origCall = "// $location = ${renderExpression(info.callee)}!${renderExpression(info.call)};"
        val callReplacement = "${futureToString(location)} = \"${info.futureName}\";"

        return indent("$origCall\n$callReplacement")
    }

    override fun visit(info: InfoLoopInitial) = indent("while(${renderExpression(info.guard)}) { }")

    override fun visit(info: InfoLoopPreserves): String {
        val text = "// Known true:\n" +
            "// Loop guard: ${renderExpression(info.guard)}\n" +
            "// Loop invariant: ${renderFormula(info.loopInv)}\n" +
            "while(${renderExpression(info.guard)}) {"
        val res = indent(text)

        indentLevel += 1

        return res
    }

    override fun visit(info: InfoLoopUse): String {
        val text = "while(${renderExpression(info.guard)}){} \n" +
            "// Known true:\n" +
            "// Negated loop guard: !(${renderExpression(info.guard)})\n" +
            "// Loop invariant: ${renderFormula(info.invariant)}"

        return indent(text)
    }

    override fun visit(info: InfoObjAlloc): String {
        val location = renderDeclLocation(info.lhs, fut2str = false)

        val original = "// $location = ${renderExpression(info.classInit)};"
        val replacement = "${futureToString(location)} = \"${getFreshObject()}\";"
        return indent("$original\n$replacement")
    }

    override fun visit(info: InfoReturn) = indent("return ${renderExpression(info.expression)};")

    override fun visit(info: InfoScopeClose): String {
        indentLevel -= 1
        return indent("}")
    }

    override fun visit(info: InfoSkip) = ""

    override fun visit(info: InfoSkipEnd) = ""

    override fun visit(info: NoInfo) = ""

    private fun getFreshObject(): String {
        objectCounter++
        return "object-$objectCounter"
    }

    private fun renderModelAssignment(loc: Location, value: Int): String {
        val location = renderDeclLocation(loc, fut2str = true)

        val type = when (loc) {
            is Field -> loc.dType
            is ProgVar -> loc.dType
            else -> throw Exception("Cannot render unknown location: ${loc.prettyPrint()}")
        }

        val renderedValue = when (type) {
            "Int" -> value.toString()
            "Fut" -> "\"${model.futNameById(value)}\""
            "Bool" -> if (value == 0) "False" else "True"
            else -> "$value??"
        }
        return "$location = $renderedValue;"
    }

    private fun renderDeclLocation(loc: Location, fut2str: Boolean): String {
        var location = renderLocation(loc)

        // Variables have to be declared on first use
        if (loc is ProgVar && !varDefs.contains(location)) {
            varDefs.add(location)
            location = "${loc.dType} $location"
        }

        // Futures are replaced by placeholder strings in executable code
        // but kept as futures in comments for context
        return if (fut2str) futureToString(location) else location
    }

    private fun renderLocation(loc: Location): String {
        return when (loc) {
            is ProgVar -> loc.name
            is Field -> "this.${loc.name.substring(0, loc.name.length - 2)}" // Remove _f suffix
            else -> loc.prettyPrint()
        }
    }

    private fun futureToString(location: String) = location.replace(Regex("^Fut\\b"), "String")

    private fun indent(text: String): String {
        val lines = text.split("\n")
        val spacer = indentString.repeat(indentLevel)

        return lines.map { "$spacer$it" }.joinToString("\n")
    }
}
