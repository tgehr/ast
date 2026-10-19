// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

// diagnostics for syntax from other languages that is not valid Silq syntax, e.g., `var x = 3;`, `if c:` or `c ? a : b`
// (`ForeignSyntax` is mixed into the parser, which parses such syntax for error recovery, reporting an error with a note on what
// to write instead; where the syntax may also be valid Silq syntax, it is first checked speculatively that it does not parse as
// Silq, see `parsesAsSilq`, so these diagnostics never cause valid Silq syntax to be rejected)
module ast.foreignsyntax;

import std.format: format;
import std.algorithm: canFind;
import ast.lexer, ast.expression;
static import util;

mixin template ForeignSyntax(){
	import std.format: format;
	import ast.foreignsyntax: adjacent, snippet, isAssignmentOperator, isStatement, isStatementStart, cannotStartOperand, conditionalSuggestion;

	int foreignSyntaxDisabled=0; // (while parsing speculatively whether code is valid Silq syntax)

	/// reports an error for syntax from another language, with a note on what to write instead
	void pitfall(string err,Location loc,string note,Location noteLoc){
		if(muteerr){ mutedErrors++; return; } // speculative parse
		handler.error(err,loc);
		if(note.length) handler.note(note,noteLoc);
	}
	/// speculatively, whether `parse` succeeds without errors when only Silq syntax is accepted (the state is restored)
	bool parsesAsSilq(scope bool delegate() parse){
		auto state=saveState();
		scope(exit) restoreState(state);
		foreignSyntaxDisabled++;
		scope(exit) foreignSyntaxDisabled--;
		displayExpectErr=true;
		auto errors=mutedErrors;
		auto start=tok.loc.rep.ptr;
		bool ok;
		try ok=parse();
		catch(PEE) ok=false;
		return ok&&mutedErrors==errors&&!code.errors.any!(e=>start<=e.loc.rep.ptr&&e.loc.rep.ptr<tok.loc.rep.ptr);
	}
	/// whether the statement at the current token is valid Silq syntax
	bool isSilqStatement(){
		return parsesAsSilq((){
			auto e=parseExpression(0,true,true);
			return e.isCompound()||util.among(ttype,Tok!";",Tok!"}");
		});
	}

	/// note for the lexer error `err`, e.g., `#` starting a comment in Python
	void noteLexerError(ref const Token err){
		if(err.str=="unsupported character '#'") handler.note("comments start with `//`",err.loc); // (see `Lexer.lexTo`)
	}
	/// note for a stray token, e.g., `1j` from Python
	void noteStrayToken(){
		if(muteerr||ttype!=Tok!"i"||!util.among(ptok.type,Tok!"0",Tok!".0")||!adjacent(ptok,tok)) return;
		if(util.among(tok.name,"j","J")) handler.note(format("imaginary numbers are written with the suffix `i`, e.g., `%si`",ptok.loc.rep),ptok.loc.to(tok.loc));
		else if(tok.name.length&&tok.name[0]=='_') handler.note("digit separators are not supported",ptok.loc.to(tok.loc));
	}
	/// note for a missing token at `loc` before a comment that is likely an integer division, e.g., `n // 2` from Python
	void noteCommentedOperation(Location loc){
		if(muteerr||code.errors.length&&code.errors[0].loc.rep.ptr==loc.rep.ptr) return;
		static bool isOperandChar(char c){ return '0'<=c&&c<='9'||'a'<=c&&c<='z'||'A'<=c&&c<='Z'||c=='_'; }
		auto p=ptok.loc.rep.ptr+ptok.loc.rep.length;
		while(*p==' '||*p=='\t') p++;
		if(p[0]!='/'||p[1]!='/') return;
		auto q=p+2;
		while(*q==' ') q++;
		if(!isOperandChar(*q)) return;
		bool isNumber='0'<=*q&&*q<='9';
		while(isOperandChar(*q)) q++;
		while(*q==' ') q++;
		if(!";)],+-*/%^".canFind(*q)&&!(isNumber&&(*q=='\r'||*q=='\n'||*q==0))) return; // (e.g., not for `// TODO`)
		handler.note("`//` starts a comment, use `div` for integer division",Location(p[0..2],loc.line));
	}

	/// whether the current token is the name of a parameter whose type is written as in C, e.g., `x` in `int x`
	bool isCStyleParameter(){
		return !foreignSyntaxDisabled&&ttype==Tok!"i"&&util.among(peek().type,Tok!",",Tok!")",Tok!"]",Tok!"=");
	}
	/// the type of a parameter written as in C, e.g., `int x` (`name` is updated to the name of the parameter)
	Expression parseCStyleParameterType(ref Identifier name){
		auto type=name;
		name=parseIdentifier();
		auto note=snippet(name)?format("use `%s: %s`",name.name,type.name):"use `x: T` for a parameter `x` of type `T`";
		pitfall("parameter types are written after the parameter name",type.loc.to(name.loc),note,type.loc.to(name.loc));
		return type;
	}
	/// skips a default value of parameter `name` without a type, e.g., `n=3` (`n: !ℕ=3` is valid syntax, see `removeDefaultValue`)
	void skipDefaultValue(Identifier name){
		if(foreignSyntaxDisabled||ttype!=Tok!"="||!snippet(name)) return;
		auto loc=tok.loc;
		nextToken();
		auto value=parseExpression(rbp!(Tok!","));
		pitfall("parameters cannot have default values",loc.to(value.loc),null,Location.init);
	}
	/// skips type parameters in angle brackets, e.g., `def f<T>(x: T)` from C++ or Rust
	void skipAngleBracketParameters(Identifier name){
		if(foreignSyntaxDisabled||ttype!=Tok!"<") return;
		auto begin=tok.loc;
		nextToken();
		auto inner=tok.loc.rep.ptr;
		for(int depth=0;!util.among(ttype,Tok!"{",Tok!";",Tok!"EOF");nextToken()){
			if(util.among(ttype,Tok!"<",Tok!"(",Tok!"[")) depth++;
			if(util.among(ttype,Tok!")",Tok!"]")) depth--;
			if(ttype==Tok!">"&&!depth--) break;
		}
		auto params=inner[0..max(0,ptok.loc.rep.ptr+ptok.loc.rep.length-inner)];
		auto note=snippet(name)&&!params.canFind('\n')?format("use square brackets for type parameters: `%s[%s]`",name.name,params):"use square brackets for type parameters";
		pitfall("unexpected `<`",begin,note,begin.to(ttype==Tok!">"?tok.loc:ptok.loc));
		expect(Tok!">");
	}
	/// skips `:` starting the body of a function as in Python, e.g., `def f(x):`
	void skipPythonFunctionBodyColon(Identifier name,Location paramLoc){
		if(foreignSyntaxDisabled||!isPythonBlockStart()) return;
		bool isReturnType(){ // (a return type on the next line, followed by a body, or by `;` for a function without a body)
			nextToken();
			auto ret=parseType();
			return util.among(ttype,Tok!"{",Tok!"⇒",Tok!"↦",Tok!"=>")||ttype==Tok!";"&&!isStatement(ret);
		}
		if(parsesAsSilq(&isReturnType)) return;
		auto note=snippet(name)&&!paramLoc.rep.canFind('\n')&&paramLoc.rep.length<=60?format("function bodies are enclosed in braces: `def %s%s { … }`",name.name,paramLoc.rep):"function bodies are enclosed in braces";
		pitfall("unexpected `:`",tok.loc,note,tok.loc);
		nextToken();
		displayExpectErr=false; // (avoids an error for the missing `{`)
	}
	/// skips a return type annotated with an arrow, e.g., `def f(x) -> 𝔹` from Python or Rust
	void skipArrowReturnType(Expression[] params){
		if(foreignSyntaxDisabled||!isArrow(ttype)) return;
		auto arrow=tok;
		nextToken();
		auto ret=parseType();
		bool isParameter(Expression e){
			auto id=cast(Identifier)e;
			return id&&params.any!(p=>(cast(Parameter)p).name&&(cast(Parameter)p).name.name==id.name);
		}
		auto type=snippet(ret);
		string note;
		if(ttype==Tok!";"&&(isParameter(ret)||cast(LiteralExp)ret)) note=format("use `⇒ %s` for a function body that is an expression",type); // e.g., `→ x;` instead of `⇒ x;`
		else note=type?format("use `: %s` to annotate the return type",type):"use `:` to annotate the return type";
		pitfall(format("unexpected `%s`",arrow),arrow.loc,note,type?arrow.loc.to(ret.loc):arrow.loc);
	}

	/// whether the current token is `not` used as a prefix operator, e.g., `not a` from Python
	bool isPrefixNot(){
		if(foreignSyntaxDisabled||ttype!=Tok!"i"||tok.name!="not") return false;
		auto next=peek();
		switch(next.type){
			case Tok!"i":
				if(isOperatorIdentifier(next)) return false; // (e.g., `not and b`)
				return next.name!="x"||cannotStartOperand(peek(2).type); // (`not x T` is a product type)
			case Tok!"0",Tok!".0",Tok!"true",Tok!"false": return true;
			default: return false; // (e.g., `not(a)` and `not (a)` are calls)
		}
	}
	Expression parsePrefixNot(){
		auto loc=tok.loc;
		nextToken();
		auto operand=parseExpression(nbp,false);
		auto a=snippet(operand);
		pitfall("`not` is not an operator",loc,a?format("use `!%s` (or `¬%s`) for logical negation",a,a):"use `!` (or `¬`) for logical negation",a?loc.to(operand.loc):loc);
		return New!(UnaryExp!(Tok!"¬"))(operand);
	}
	/// whether the current token is `++` or `--` used as a prefix operator, e.g., `++x` from C
	bool isPrefixIncrement(){
		return !foreignSyntaxDisabled&&util.among(ttype,Tok!"++",Tok!"--")&&peek().type==Tok!"i";
	}
	Expression parsePrefixIncrement(){
		auto op=tok;
		nextToken();
		auto operand=parseExpression(nbp,false);
		auto x=snippet(operand), update=op.type==Tok!"++"?"+=":"-=";
		pitfall(format("`%s` is not an operator",op),op.loc,x?format("use `%s %s 1`",x,update):format("use `%s 1`",update),x?op.loc.to(operand.loc):op.loc);
		return New!ErrorExp();
	}
	static bool isOperatorIdentifier(Token t){ // identifiers that are parsed as binary operators, e.g., `div` and `and`
		if(t.type!=Tok!"i") return false;
		static foreach(op;binaryOpIds) if(t.name==op[0]) return true;
		return false;
	}

	/// whether the current token is `**` for exponentiation, e.g., `2**3` from Python
	/// (`x**(n+1)` and `x**-1` are valid syntax, using the kind `*`, see `explainDoubleStar`)
	bool isPythonPower(){
		if(foreignSyntaxDisabled||ttype!=Tok!"*"||peek().type!=Tok!"*"||!adjacent(tok,peek())) return false;
		auto next=peek(2);
		return util.among(next.type,Tok!"0",Tok!".0")||next.type==Tok!"i"&&!isOperatorIdentifier(next)&&next.name!="x";
	}
	Expression parsePythonPower(Expression left){
		auto opLoc=tok.loc.to(peek().loc);
		nextToken(); nextToken();
		auto right=parseExpression(rbp!(Tok!"^"),false);
		auto a=snippet(left), b=snippet(right);
		pitfall("`**` is not an operator",opLoc,a&&b?format("use `%s^%s` for exponentiation",a,b):"use `^` for exponentiation",a&&b?left.loc.to(right.loc):opLoc);
		return New!(BinaryExp!(Tok!"^"))(left,right);
	}
	/// whether the current token starts a conditional expression with `?`, e.g., `c ? a : b` from C
	bool isTernary(){
		if(foreignSyntaxDisabled||ttype!=Tok!"?") return false;
		auto state=saveState();
		scope(exit) restoreState(state);
		nextToken();
		if(ttype==Tok!":") return false;
		for(int depth=0;;nextToken()){
			switch(ttype){
				case Tok!"(",Tok!"[": depth++; break;
				case Tok!")",Tok!"]": if(--depth<0) return false; break;
				case Tok!":": if(!depth) return true; break;
				case Tok!"{",Tok!"}",Tok!";",Tok!"EOF": return false;
				default: break;
			}
		}
	}
	Expression parseTernary(Expression cond){
		auto opLoc=tok.loc;
		nextToken();
		auto then=parseExpression(lbp!(Tok!":")); // (stops before `:`)
		expect(Tok!":");
		auto othw=parseExpression(rbp!(Tok!"?"));
		pitfall("`?` is not an operator",opLoc,conditionalSuggestion(cond,then,othw),cond.loc.to(othw.loc));
		return New!ErrorExp();
	}
	/// whether the current token starts a conditional expression as in Python, e.g., `a if c else b`
	bool isPythonConditional(){
		if(foreignSyntaxDisabled||ttype!=Tok!"if") return false;
		auto state=saveState();
		scope(exit) restoreState(state);
		nextToken();
		for(int depth=0;;nextToken()){
			switch(ttype){
				case Tok!"(",Tok!"[": depth++; break;
				case Tok!")",Tok!"]": if(--depth<0) return false; break;
				case Tok!"else": if(!depth) return true; break;
				case Tok!"{",Tok!"}",Tok!";",Tok!"then",Tok!"if",Tok!"EOF": return false;
				default: break;
			}
		}
	}
	Expression parsePythonConditional(Expression then){
		auto ifLoc=tok.loc;
		nextToken();
		auto cond=parseExpression(rbp!(Tok!","));
		expect(Tok!"else");
		auto othw=parseExpression(rbp!(Tok!","));
		pitfall("unexpected `if`",ifLoc,conditionalSuggestion(cond,then,othw),then.loc.to(othw.loc));
		auto r=New!ErrorExp();
		r.loc=then.loc.to(othw.loc);
		return r;
	}
	/// whether the index at the current token is a slice as in Python, e.g., `x[:3]`, `x[1:]` or `x[::2]` (but not `x[1:3]`, which is an index with a type annotation)
	bool isPythonSlice(){
		if(foreignSyntaxDisabled) return false;
		auto state=saveState();
		scope(exit) restoreState(state);
		for(int depth=0;;nextToken()){
			switch(ttype){
				case Tok!"(",Tok!"[",Tok!"{": depth++; break;
				case Tok!")",Tok!"]",Tok!"}": if(--depth<0) return false; break;
				case Tok!":":
					if(depth) break;
					if(ptok.type==Tok!"["||util.among(peek().type,Tok!"]",Tok!":")) return true;
					break;
				case Tok!";",Tok!"EOF": return false;
				default: break;
			}
		}
	}
	Expression parsePythonSlice(Expression left,Location begin){
		Expression[3] parts; // start, end and step
		int numColons=0;
		while(ttype!=Tok!"]"&&ttype!=Tok!"EOF"){
			if(ttype==Tok!":"){
				numColons++;
				nextToken();
				continue;
			}
			auto part=parseExpression(lbp!(Tok!":")); // (stops before `:`)
			if(numColons<3&&!parts[numColons]) parts[numColons]=part;
			if(ttype!=Tok!":"&&ttype!=Tok!"]") break;
		}
		auto loc=begin.to(tok.loc);
		expect(Tok!"]");
		string note;
		if(numColons>1) note="slices with a step are not supported";
		else if(snippet(left)&&(!parts[0]||snippet(parts[0]))&&(!parts[1]||snippet(parts[1])))
			note=format("use `%s[%s..%s]` to take a slice",snippet(left),parts[0]?snippet(parts[0]):"0",parts[1]?snippet(parts[1]):snippet(left)~".length");
		else note="use `x[a..b]` to take a slice";
		pitfall("unsupported slice syntax",loc,note,left.loc.to(loc));
		auto r=New!ErrorExp();
		r.loc=left.loc.to(loc);
		return r;
	}

	/// a statement starting with a keyword from another language, e.g., `var x = 3;` or `fn f(x){ … }` (otherwise `null`)
	Expression tryParseForeignStatement(){
		if(foreignSyntaxDisabled||!util.among(ttype,Tok!"i",Tok!"let",Tok!"const")) return null;
		auto kw=tok;
		auto name=kw.toString();
		auto next=peek(), nnext=peek(2);
		if(ttype==Tok!"i"&&util.among(name,"fn","function","func","fun","operation","proc","procedure","method","void")&&next.type==Tok!"i"&&util.among(nnext.type,Tok!"(",Tok!"[",Tok!"<")){ // e.g., `fn f(x){ … }`
			if(isSilqStatement()) return null;
			pitfall(format("`%s` is not a keyword",name),kw.loc,"functions are defined with `def`",kw.loc);
			nextToken();
			return parseFunctionDef(false);
		}
		bool isAssignment=ttype==Tok!"i"&&name=="set"; // e.g., `set x += 1` from Q#
		bool isDefinition=ttype!=Tok!"i"||!!util.among(name,"var","val","mut","mutable","auto","local","my","dim","use","int","uint","float","double","bool","boolean","char","string","long","short","unsigned","qubit","Qubit");
		if(!isDefinition&&!isAssignment) return null;
		int skip=1;
		if(next.type==Tok!"i"&&next.name=="mut"){ // e.g., `let mut x = 3` from Rust
			skip++;
			next=nnext;
			nnext=peek(3);
		}
		if(next.type!=Tok!"i") return null;
		if(isDefinition&&!util.among(nnext.type,Tok!"=",Tok!":=",Tok!":",Tok!"←")) return null;
		if(isAssignment&&!isAssignmentOperator(nnext.type)) return null;
		if(kw.type==Tok!"let"&&hasIn()) return null; // (`let x := 3 in x`)
		if(isSilqStatement()) return null; // (e.g., `const x := 3`)
		foreach(i;0..skip) nextToken();
		auto e=parseExpression(0,true,true);
		string suggestion;
		if(isAssignment) suggestion=snippet(e);
		else if(auto ae=cast(AssignExp)e) suggestion=snippet(ae.e1)&&snippet(ae.e2)?format("%s := %s",snippet(ae.e1),snippet(ae.e2)):null;
		else if(cast(DefineExp)e) suggestion=snippet(e);
		auto note=isAssignment?"assign variables without `set`":"define variables with `:=`";
		if(suggestion.length) note=format("%s: `%s`",note,suggestion);
		pitfall(format("unexpected `%s`",name),kw.loc,note,e.loc);
		return e;
	}

	private bool hasIn(){ // (whether the statement at the current token contains `in`, e.g., `let x := 3 in x`)
		auto state=saveState();
		scope(exit) restoreState(state);
		for(int depth=0;;nextToken()){
			switch(ttype){
				case Tok!"(",Tok!"[",Tok!"{": depth++; break;
				case Tok!")",Tok!"]",Tok!"}": if(--depth<0) return false; break;
				case Tok!"in": if(!depth) return true; break;
				case Tok!";": if(!depth) return false; break;
				case Tok!"EOF": return false;
				default: break;
			}
		}
	}

	/// whether the current token is `:` followed by a statement on the next line, e.g., `else:` from Python
	bool isPythonBlockStart(){
		return ttype==Tok!":"&&peek().loc.line>tok.loc.line&&isStatementStart(peek(),peek(2));
	}
	/// whether the condition at the current token ends with `:` as in Python, e.g., `if c:` followed by a statement on the next line
	bool isPythonBlockHeader(){
		if(foreignSyntaxDisabled||!hasPythonBlockStart()) return false;
		return !parsesAsSilq((){ parseCondition(); return util.among(ttype,Tok!"{",Tok!"then"); }); // (`:` may be a type annotation)
	}
	Expression parsePythonBlockHeader(string keyword){
		auto e=parseExpression(lbp!(Tok!":")); // (stops before `:`)
		if(ttype==Tok!":"){
			auto colon=tok.loc;
			nextToken();
			auto note=snippet(e)?format("blocks are enclosed in braces: `%s %s { … }`",keyword,snippet(e)):"blocks are enclosed in braces";
			pitfall("unexpected `:`",colon,note,colon);
			displayExpectErr=false; // (avoids an error for the missing `{`)
		}
		return e;
	}
	private bool hasPythonBlockStart(){ // (whether the header at the current token ends with `:` followed by a statement on the next line)
		auto state=saveState();
		scope(exit) restoreState(state);
		for(int depth=0;;nextToken()){
			switch(ttype){
				case Tok!"(",Tok!"[": depth++; break;
				case Tok!")",Tok!"]": if(--depth<0) return false; break;
				case Tok!"{",Tok!"}",Tok!";",Tok!"EOF": return false;
				case Tok!":": if(!depth&&isPythonBlockStart()) return true; break;
				default: break;
			}
		}
	}
	/// skips `:` after `else`, as in Python
	void skipPythonElseColon(){
		if(foreignSyntaxDisabled||ttype!=Tok!":"||peek().loc.line<=tok.loc.line) return;
		pitfall("unexpected `:`",tok.loc,"blocks are enclosed in braces: `else { … }`",tok.loc);
		nextToken();
		displayExpectErr=false; // (avoids an error for the missing `{`)
	}
	/// whether the current token starts an `else if` branch with a keyword from another language, e.g., `elif` from Python
	bool isElif(){
		return !foreignSyntaxDisabled&&ttype==Tok!"i"&&util.among(tok.name,"elif","elsif","elseif")&&!isSilqStatement(); // (e.g., `elif(x);` is a call)
	}
	CompoundExp parseElif(){
		pitfall(format("`%s` is not a keyword",tok.name),tok.loc,"use `else if`",tok.loc);
		Expression o=parseIte(true);
		auto r=New!CompoundExp([o]);
		r.loc=o.loc;
		return r;
	}
	/// whether the `for` loop at the current token has a header as in Python, e.g., `for i in range(n):`
	bool isPythonForHeader(){
		if(foreignSyntaxDisabled||!hasPythonBlockStart()) return false;
		return !parsesAsSilq((){ parseForNoBody(); return ttype==Tok!"{"; }); // (`:` may be a type annotation)
	}
	ForExp parsePythonForHeader(Identifier var,Expression pattern){
		auto exp=parsePythonBlockHeader(format("for %s in",var&&var.name.length?var.name:snippet(pattern)?snippet(pattern):"…"));
		return New!ForExp(var,pattern,ForAggregate(ForContainer(exp)),null);
	}
	/// whether the `for` loop at the current token is a loop as in C, e.g., `for(i:=0;i<n;i+=1)`
	bool isCStyleFor(){
		if(foreignSyntaxDisabled||ttype!=Tok!"(") return false;
		auto state=saveState();
		scope(exit) restoreState(state);
		nextToken();
		for(int depth=0;;nextToken()){
			switch(ttype){
				case Tok!"(",Tok!"[",Tok!"{": depth++; break;
				case Tok!")",Tok!"]",Tok!"}": if(--depth<0) return false; break;
				case Tok!";": if(!depth) return true; break;
				case Tok!"EOF": return false;
				default: break;
			}
		}
	}
	ForExp parseCStyleFor(Location begin){
		auto suggestion=cStyleForSuggestion();
		nextToken();
		skipToUnmatched();
		auto header=begin.to(tok.loc);
		expect(Tok!")");
		pitfall("C-style `for` loops are not supported",header,suggestion.length?format("use `%s`",suggestion):"use `for i in [a..b) { … }` to loop over `a`, `a+1`, …, `b-1`",header);
		auto error=New!ErrorExp();
		error.loc=header;
		return New!ForExp(null,null,ForAggregate(ForContainer(error)),null);
	}
	private string cStyleForSuggestion(){ // e.g., `for i in [0..n) { … }` for `for(i:=0;i<n;i+=1)`
		auto state=saveState();
		scope(exit) restoreState(state);
		nextToken();
		if(ttype==Tok!"i"&&peek().type==Tok!"i"||util.among(ttype,Tok!"let",Tok!"const")) nextToken(); // e.g., `int i=0`
		auto init=parseExpression(0,true,true);
		if(ttype!=Tok!";") return null;
		nextToken();
		auto cond=parseExpression();
		if(ttype!=Tok!";") return null;
		nextToken();
		Identifier var;
		Expression start;
		if(auto de=cast(DefineExp)init){ var=cast(Identifier)de.e1; start=de.e2; }
		else if(auto ae=cast(AssignExp)init){ var=cast(Identifier)ae.e1; start=ae.e2; }
		if(!var) return null;
		bool isVar(Expression e){ auto id=cast(Identifier)e; return id&&id.name==var.name; }
		static bool isOne(Expression e){ auto lit=cast(LiteralExp)e; return lit&&lit.lit.type==Tok!"0"&&lit.lit.str=="1"; }
		Expression end;
		bool inclusive=false;
		if(auto lt=cast(LtExp)cond){ if(isVar(lt.e1)) end=lt.e2; }
		else if(auto le=cast(LeExp)cond){ if(isVar(le.e1)) end=le.e2, inclusive=true; }
		else if(auto ne=cast(NeqExp)cond){ if(isVar(ne.e1)) end=ne.e2; }
		if(!end) return null;
		bool increment=false;
		if(ttype==Tok!"++"&&peek().type==Tok!"i"&&peek().name==var.name){ // `++i`
			nextToken();
			nextToken();
			increment=true;
		}else{
			auto step=parseExpression(0,true,true);
			if(auto pe=cast(PostfixExp!(Tok!"++"))step) increment=isVar(pe.e);
			else if(auto ae=cast(AddAssignExp)step) increment=isVar(ae.e1)&&isOne(ae.e2);
			else if(auto ae=cast(AssignExp)step){
				if(auto add=cast(AddExp)ae.e2) increment=isVar(ae.e1)&&isVar(add.e1)&&isOne(add.e2);
			}
		}
		if(!increment||ttype!=Tok!")"||!snippet(start)||!snippet(end)) return null;
		return format("for %s in [%s..%s%s) { … }",var.name,snippet(start),snippet(end),inclusive?"+1":"");
	}
	/// whether the current token starts the condition of an `assert` without parentheses, e.g., `assert x == 1` from Python
	bool isUnparenthesizedAssert(){
		if(foreignSyntaxDisabled||ttype==Tok!"(") return false;
		return parsesAsSilq((){
			parseExpression(rbp!(Tok!","));
			if(ttype==Tok!","){ // (message)
				nextToken();
				parseExpression(rbp!(Tok!","));
			}
			return util.among(ttype,Tok!";",Tok!"}");
		});
	}
	AssertExp parseUnparenthesizedAssert(){
		auto exp=parseExpression(rbp!(Tok!","));
		if(ttype==Tok!","){ // (message)
			nextToken();
			parseExpression(rbp!(Tok!","));
		}
		pitfall("missing parentheses for `assert`",exp.loc,snippet(exp)?format("use `assert(%s)`",snippet(exp)):"use `assert(c)` for a condition `c`",exp.loc);
		return New!AssertExp(exp);
	}
}

package:

bool adjacent(Token a,Token b){ return a.loc.rep.ptr+a.loc.rep.length==b.loc.rep.ptr; }

bool isAssignmentOperator(TokenType t){
	return !!util.among(t,Tok!"=",Tok!"←",Tok!"+=",Tok!"-=",Tok!"*=",Tok!"·=",Tok!"/=",Tok!"^=",Tok!"⊕=",Tok!"~=",Tok!"%=",Tok!"div=",Tok!"sub=");
}

/// whether `t` cannot start an operand (for detecting `x` used as a variable rather than for a product type, e.g., `not x`)
bool cannotStartOperand(TokenType t){
	return !!util.among(t,Tok!";",Tok!",",Tok!")",Tok!"]",Tok!"}",Tok!"{",Tok!":",Tok!"then",Tok!"else",Tok!"EOF",Tok!"&&",Tok!"||",Tok!"==",Tok!"=",Tok!"!=",Tok!"≠");
}

/// whether `e` is a statement that is not an expression, e.g., `return x` (parsed as a type in `def f(x):\n return x;` from Python)
bool isStatement(Expression e){
	return cast(ReturnExp)e||cast(AAssignExp)e||cast(DefineExp)e||cast(AssertExp)e||cast(ForgetExp)e;
}

/// whether `t` (followed by `next`) starts a statement (for detecting blocks from Python, e.g., `if c:` followed by a statement on the next line)
bool isStatementStart(Token t,Token next){
	switch(t.type){
		case Tok!"return",Tok!"if",Tok!"for",Tok!"while",Tok!"repeat",Tok!"assert",Tok!"forget",Tok!"def": return true;
		case Tok!"i": return t.name=="pass"||isAssignmentOperator(next.type)||util.among(next.type,Tok!":=",Tok!"(");
		default: return false;
	}
}

string conditionalSuggestion(Expression cond,Expression then,Expression othw){
	if(!snippet(cond)||!snippet(then)||!snippet(othw)) return "use `if c then a else b` for a conditional expression";
	auto r=format("if %s then %s else %s",snippet(cond),snippet(then),snippet(othw));
	if(r.length>60) return "use `if c then a else b` for a conditional expression";
	return format("use `%s` for a conditional expression",r);
}

/// source code of `e` for a suggestion, or `null` if it is not suitable, e.g., missing because of a parse error, or long
string snippet(Expression e){
	if(!e||cast(ErrorExp)e) return null;
	if(auto id=cast(Identifier)e) if(!id.name.length) return null;
	auto r=e.loc.rep;
	if(!r.length||r.length>60||r.canFind('\0')||r.canFind('\n')) return null;
	int depth=0;
	foreach(c;r){
		if(c=='('||c=='['||c=='{') depth++;
		if(c==')'||c==']'||c=='}') if(--depth<0) return null;
	}
	return depth?null:r;
}
