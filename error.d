// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.error;

import std.string, std.range, std.array, std.uni, std.algorithm.searching;
import std.conv: to;

import ast.lexer, util;
import util.io;


enum ErrorType {
	error,
	run_error,
	warning,
	note,
	message,
}

private string prefix(ErrorType ty){
	final switch(ty) {
		case ErrorType.error: return "error: ";
		case ErrorType.run_error: return "error: ";
		case ErrorType.warning: return "warning: ";
		case ErrorType.note: return "note: ";
		case ErrorType.message: return "";
	}
}

abstract class ErrorHandler{
	//string source;
	//string code;
	int nerrors=0;
	private int tabsize=8;

	void report(ErrorType ty, lazy string msg, Location loc) {
		if(ty <= ErrorType.run_error) {
			nerrors++;
		}
	}

	final void error(lazy string msg, Location loc) {
		return report(ErrorType.error, msg, loc);
	}
	final void run_error(lazy string msg, Location loc) {
		return report(ErrorType.run_error, msg, loc);
	}
	final void warning(lazy string msg, Location loc) {
		return report(ErrorType.warning, msg, loc);
	}
	final void note(lazy string msg, Location loc) {
		return report(ErrorType.note, msg, loc);
	}
	final void message(lazy string msg, Location loc) {
		return report(ErrorType.message, msg, loc);
	}

	bool showsEffect(){ return true; }

	int getTabsize(){ return tabsize; }

	this(){
		tabsize=getTabSize();
	}
	void finalize(){}
}
class SimpleErrorHandler: ErrorHandler{
	override void report(ErrorType ty, lazy string err, Location loc){
		super.report(ty, err, loc);
		if(loc.line == 0){ // just here for robustness
			stderr.writef("(location missing): %s%s\n", ty.prefix(), err);
			return;
		}
		stderr.writef("%s(%d): %s%s\n", loc.source.name, loc.line, ty.prefix(), err);
	}
}

enum underlineArrow  = "^";
enum underlineStroke = "─";

import std.json;
class JSONErrorHandler: ErrorHandler{
	alias JSONValue JS;
	JS[] result=[];
	File output;
	bool close;

	this(){
		this.output = stderr;
		this.close = false;
	}
	this(File output, bool close){
		this.output = output;
		this.close = close;
	}

	override void report(ErrorType ty, lazy string error, Location loc){
		super.report(ty, error, loc);
		auto li = loc.info(getTabsize());
		auto sourceJS = JS(li.source.name);
		auto startJS = JS(["byte": li.startByte, "line": li.startLine, "column": li.startColumn]);
		auto endJS = JS(["byte": li.endByte, "line": li.endLine, "column": li.endColumn]);
		auto messageJS = JS(error);
		auto severityJS = JS(ty.to!string());
		auto diagnosticJS = JS(["source": sourceJS, "start": startJS, "end": endJS, "message": messageJS, "severity": severityJS]);
		if(ty != ErrorType.note){
			auto relatedInformationJS = JS((JS[]).init);
			diagnosticJS["relatedInformation"] = relatedInformationJS;
			result~=diagnosticJS;
		} else {
			result[$-1]["relatedInformation"]~=[diagnosticJS];
		}
	}
	override void finalize(){
		output.writeln(result);
		if(close) {
			output.close();
		}
	}
}


// TODO: remove code duplication

class VerboseErrorHandler: ErrorHandler{
	override void report(ErrorType ty, lazy string err, Location loc){
		super.report(ty, err, loc);
		if(loc.line == 0||!loc.rep.length){ // just here for robustness
			stderr.writef("(location missing): %s%s\n", ty.prefix(), err);
			return;
		}
		auto li = loc.info(getTabsize());
		auto line = li.source.getLineOf(loc.rep);
		write(ty, li.source.name, li.startLine, li.startColumn, err);
		if(line.length&&line[0]){
			display(line);
			auto ntabs = line.countUntil!(c => c != '\t');
			highlight(li.startColumn, cast(int)(ntabs < 0 ? line.length : ntabs), loc.rep);
		}
	}
protected:
	void write(ErrorType ty, string source, int line, int column, string error){
		stderr.writeln(source, ':', line, ':', column, ": ", ty.prefix(), error);
	}
	void display(string line){
		stderr.writeln(line);
	}
	void writeIndent(int column, int ntabs){
		foreach(i;0..ntabs) stderr.write("\t");
		foreach(i;0..column-ntabs*getTabsize()) stderr.write(" ");
	}
	void writeUnderline(string rep, int column){
		import std.utf:byChar;
		auto n = rep.byChar.countUntil('\n');
		if(n >= 0) {
			rep = rep[0..n];
		}
		stderr.write(underlineArrow);
		foreach(i; 0..displayWidth(rep, getTabsize(), column) - 1) {
			stderr.write(underlineStroke);
		}
		stderr.writeln();
	}
	void highlight(int column, int ntabs, string rep){
		writeIndent(column, ntabs);
		writeUnderline(rep, column);
	}
}

import util.terminal;
class FormattingErrorHandler: VerboseErrorHandler{
protected:
	override void write(ErrorType ty, string source, int line, int column, string error){
		string color = BLACK;
		if(ty <= ErrorType.run_error) color = RED;
		stderr.writeln(BOLD, source, ':', line, ':', column, ": ", color, ty.prefix(), RESET, BOLD, error, RESET);
	}

	override void highlight(int column, int ntabs, string rep){
		writeIndent(column, ntabs);
		stderr.write(BOLD, GREEN);
		writeUnderline(rep, column);
		stderr.writeln(RESET);
	}
}
