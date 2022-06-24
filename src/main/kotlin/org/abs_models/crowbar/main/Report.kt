package org.abs_models.crowbar.main

import java.io.PrintWriter
import java.io.StringWriter


fun reportException(message:String, e:Exception){
    if(reporting) {
        val sw = StringWriter()
        (if(e.cause != null)  e.cause else e)!!.printStackTrace(PrintWriter(sw))
        val cause = sw.toString()
        throw Exception("$message: ${cause.split("\n")[0]}")
    }
}

