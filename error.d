// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.error;

import std.string, std.range, std.array, std.uni;

import ast.lexer, util, options;
import util.io;


abstract class ErrorHandler{
	//string source;
	//string code;
	int nerrors=0;
	private int tabsize=8;


	void error(lazy string err, Location loc)in{assert(loc.line>=1&&loc.rep);}do{nerrors++;}   // in{assert(loc.rep);}body
	void warning(lazy string err, Location loc)in{assert(loc.line>=1&&loc.rep);}do{}
	void note(lazy string note, Location loc)in{assert(loc.rep);}do{}
	void message(lazy string msg, Location loc)in{assert(loc.line>=1&&loc.rep);}do{}

	bool showsEffect(){ return true; }

	int getTabsize(){ return tabsize; }

	this(){
		tabsize=getTabSize();
	}
	void finalize(){}
}
class SimpleErrorHandler: ErrorHandler{
	override void error(lazy string err, Location loc){
		if(loc.line == 0){ // just here for robustness
			stderr.writeln("(location missing): error: "~err);
			return;
		}
		nerrors++;
		stderr.writeln(loc.source.name,'(',loc.line,"): error: ",err);
	}
	override void warning(lazy string err, Location loc){
		if(loc.line == 0){ // just here for robustness
			stderr.writeln("(location missing): warning: "~err);
			return;
		}
		nerrors++;
		stderr.writeln(loc.source.name,'(',loc.line,"): warning: ",err);
	}
	override void message(lazy string msg, Location loc){
		stderr.writeln(msg);
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

	private JS makeJS(string error, Location loc, string severity, bool addRelated){
		auto source=loc.source.name;
		auto start=getStart!wchar(loc,1);
		auto end=getEnd!wchar(loc,1);
		auto sourceJS=JS(source);
		auto startJS=JS(["line": JS(start.line), "column": JS(start.column)]);
		auto endJS=JS(["line": JS(end.line), "column": JS(end.column)]);
		auto messageJS=JS(error);
		auto severityJS=JS(severity);
		auto diagnosticJS=JS(["source": sourceJS, "start": startJS, "end": endJS, "message": messageJS, "severity": severityJS]);
		if(addRelated){
			auto relatedInformationJS=JS((JS[]).init);
			diagnosticJS["relatedInformation"]=relatedInformationJS;
		}
		return diagnosticJS;
	}
	override void error(lazy string error, Location loc){
		assert(loc.line>=1);
		nerrors++;
		result~=makeJS(error,loc,"error",true);
	}
	override void warning(lazy string warning, Location loc){
		assert(loc.line>=1);
		nerrors++;
		result~=makeJS(warning,loc,"warning",true);
	}
	override void note(lazy string note, Location loc){
		assert(result.length>0);
		assert(loc.line>=1);
		result[$-1]["relatedInformation"]~=[makeJS(note,loc,"note",false)];
	}
	override void message(lazy string message, Location loc){
		assert(loc.line>=1);
		result~=[makeJS(message,loc,"message",false)];
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
	override void error(lazy string err, Location loc){
		nerrors++;
		impl(err, loc, "error");
	}
	override void warning(lazy string warn, Location loc){
		impl(warn, loc, "warning");
	}
	override void note(lazy string err, Location loc){
		impl(err, loc, "note");
	}
	override void message(lazy string err, Location loc){
		impl(err, loc, "message");
	}
	private void impl(lazy string err, Location loc, string severity){
		if(loc.line == 0||!loc.rep.length){ // just here for robustness
			stderr.writeln("(location missing): "~err);
			return;
		}
		auto src = loc.source;
		auto source = src.name;
		auto line = src.getLineOf(loc.rep);
		if(loc.rep.ptr<line.ptr) loc.rep=loc.rep[line.ptr-loc.rep.ptr..$];
		auto column=getColumn(loc,tabsize);
		write(source, loc.line, column, err, severity);
		if(line.length&&line[0]){
			display(line);
			highlight(column,column-getColumn(loc,tabsize-1), loc.rep);
		}
	}
protected:
	void write(string source, int line, int column, string error, string severity = "error"){
		stderr.writeln(source,':',line,":",column,": ",severity,": ",error);
	}
	void display(string line){
		stderr.writeln(line);
	}
	void highlight(int column, int ntabs, string rep){
		foreach(i;0..column-ntabs*(getTabsize()-1)) stderr.write(i<ntabs?"\t":" ");
		stderr.write(underlineArrow);
		rep.popFront();
		foreach(dchar x;rep){if(isNewLine(x)) break; stderr.write(underlineStroke);}
		stderr.writeln();
	}
}

import util.terminal;
class FormattingErrorHandler: VerboseErrorHandler{
protected:
	override void write(string source, int line, int column, string error, string severity = "error"){
		if(isATTy(stderr)){
			if(severity=="error") stderr.writeln(BOLD,source,':',line,":",column,": ",RED,"error:",RESET,BOLD," ",error,RESET);
			else stderr.writeln(BOLD,source,':',line,":",column,": ",BLACK,severity,":",RESET,BOLD," ",error,RESET);
		}else super.write(source, line, column, error, severity);
	}
	override void highlight(int column, int ntabs, string rep){
		if(isATTy(stderr)){
			foreach(i;0..column-ntabs*(getTabsize()-1)) stderr.write(i<ntabs?"\t":" ");
			//stderr.write(CSI~"A",GREEN,";",CSI~"D",CSI~"B");
			stderr.write(BOLD,GREEN,underlineArrow);
			rep.popFront();
			foreach(dchar x;rep){if(isNewLine(x)) break; stderr.write(underlineStroke);}
			stderr.writeln(RESET);
		}else super.highlight(column, ntabs, rep);
	}
}

string formatError(string msg,Location loc){
	import std.conv;
	return text(loc.line,": ",msg); // TODO: column
}
