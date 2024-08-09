module ast.modules;

import util.tuple: Q=Tuple, q=tuple;
import util: mallocAppender;

import astopt;
import ast.parser;
import ast.error: ErrorHandler;
import ast.lexer: Source, Location;
import ast.scope_: Scope, TopScope;
import ast.declaration;
import ast.expression: Expression;

private TopScope preludeScope=null;
private Source preludeSrc=null;
private TopScope operatorScope=null;
private static Q!(Expression[],TopScope)[string] modules;

import util.io;
string readCode(File f){
	// TODO: use memory-mapped file with 4 padding zero bytes
	auto app=mallocAppender!(char[])();
	foreach(r;f.byChunk(1024)){app.put(cast(char[])r);}
	app.put("\0\0\0\0"); // insert 4 padding zero bytes
	return cast(string)app.data;
}
string readCode(string path){ return readCode(File(path)); }

string readBuiltin(string[] paths)(int index){
	import std.file: thisExePath;
	import std.path: dirName;
	string binPath = dirName(thisExePath());
	string path = paths[index];
	foreach(tryPath; [
		binPath ~ "/library/" ~ path,
		binPath ~ "/../share/silq/library/" ~ path,
	]) {
		try return readCode(tryPath);
		catch(Exception) {}
	}
	switch(index){
		static foreach(i,p;paths){
			case i:
			// 4 padding bytes required by lexer
			return import(p) ~ "\0\0\0\0";
		}
		default: assert(0);
	}
}

Scope getPreludeScope(ErrorHandler err, Location loc){
	import ast.semantic_: semantic;
	if(preludeScope) return preludeScope;
	preludeScope = new TopScope(err);
	preludeSrc = new Source(".prelude", readBuiltin!preludePaths(preludeIndex));
	int nerr = err.nerrors;
	auto exprs = parseSource(preludeSrc, err);
	exprs = semantic(exprs, preludeScope);
	if(nerr != err.nerrors) {
		if(loc.line) preludeScope.error("failed to import prelude", loc);
		else preludeScope.message("failed to import prelude");
	}
	return preludeScope;
}

bool isInPrelude(Declaration decl){
	if(!preludeScope) return false;
	return decl.scope_.isNestedIn(preludeScope);
}

bool isPreludeSource(Source src){
	return src is preludeSrc;
}

int importModule(string path,ErrorHandler err,out Expression[] exprs,out TopScope sc,Location loc=Location.init){
	import ast.semantic_: semantic;
	if(path in modules){
		auto exprssc=modules[path];
		exprs=exprssc[0],sc=exprssc[1];
		if(!sc){
			if(loc.line) err.error("circular imports not supported",loc);
			else err.message("error: circular imports not supported");
			return 1;
		}
		return 0;
	}
	modules[path]=q(Expression[].init,TopScope.init);
	scope(success) modules[path]=q(exprs,sc);
	if(auto r=parseFile(getActualPath(path),err,exprs,loc))
		return r;
	sc=new TopScope(err);
	sc.import_(getPreludeScope(err, loc));
	int nerr=err.nerrors;
	exprs=semantic(exprs,sc);
	if(nerr!=err.nerrors){
		if(loc.line) sc.error("errors in imported file",loc);
		return 1;
	}
	return 0;
}

int parseFile(string path,ErrorHandler err,ref Expression[] r,Location loc=Location.init){
	string code;
	try code=readCode(path);
	catch(Exception){
		string error;
		if(!file.exists(path)){
			// bake prelude into binary as a fallback
			void noSuchFile(){ error = path ~ ": no such file"; }
			static if(language==psi){
				if(path=="prelude.psi") code=import("prelude.psi") ~ "\0\0\0\0";
				else if(path=="prelude-nocheck.psi") code=import("prelude-nocheck.psi") ~ "\0\0\0\0";
				else noSuchFile();
			}else noSuchFile();
		}else error = path ~ ": error reading file";
		if(error){
			if(loc.line) err.error(error,loc);
			else stderr.writeln("error: "~error);
			return 1;
		}
	}
	auto src=new Source(path, code);
	auto nerr=err.nerrors;
	r=parseSource(src,err);
	return nerr!=err.nerrors;
}

static if(language==silq)
Scope getOperatorScope(ErrorHandler err, Location loc){
	import ast.semantic_: semantic;
	if(operatorScope) return operatorScope;
	operatorScope = new TopScope(err);
	operatorScope.import_(getPreludeScope(err, loc));
	auto src = new Source(".operators", readBuiltin!([operatorsPath])(0));
	int nerr = err.nerrors;
	auto exprs = parseSource(src, err);
	exprs = semantic(exprs,operatorScope);
	if(nerr != err.nerrors) {
		if(loc.line) operatorScope.error("failed to import operators", loc);
		else operatorScope.message("failed to import operators");
	}
	return operatorScope;
}

static if(language==silq)
bool isInOperators(Declaration decl){
	static if(operatorLowering) {
		if(!operatorScope) return false;
		return decl.scope_.isNestedIn(operatorScope);
	} else {
		return false;
	}
}
