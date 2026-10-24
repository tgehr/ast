// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.callfailure;
import astopt;

import std.conv, std.format, std.algorithm, std.range, std.array;
import std.uni: isAlphaNum;
import ast.lexer, ast.scope_, ast.expression, ast.type, ast.declaration, ast.conversion, util;
import ast.semantic_: unwrap, calleeFunctionDef, explainAnnotation, isPreludeSymbol, iDivType, isBuiltIn, statementSemantic, expressionSemantic, StmFlags, ExpSemContext, nestConst;
import ast.modules: isInPrelude;

// diagnostics for calls that do not type check and for other common pitfalls (e.g., syntax from other languages).

/// describes the function called by `ce`, e.g., "`f`" or "`f[3]`"
string describeFunction(CallExp ce){
	if(auto text=calleeText(ce)) return format("`%s`",text);
	return describeFunction(ce.e);
}

/// source code of the callee of `ce` (it may differ from `ce.e`, e.g., for `reverse(f)(x)`), if short
string calleeText(CallExp ce){
	auto r=ce.loc.rep, a=ce.arg.loc.rep;
	if(!r.length||!a.length||!(r.ptr<a.ptr&&a.ptr<=r.ptr+r.length)) return null;
	import std.string: strip;
	auto text=r[0..a.ptr-r.ptr].strip; // (source code before the arguments)
	if(!text.length||text.length>40||text.canFind('\n')) return null;
	return text;
}

/// describes the function `callee`
string describeFunction(Expression callee){
	static bool named(Expression e){
		e=unwrap(e);
		return cast(Identifier)e||cast(FieldExp)e;
	}
	auto e=unwrap(callee);
	if(named(e)) return format("`%s`",e);
	if(auto ce=cast(CallExp)e) if(ce.isSquare&&named(ce.e)) return format("`%s`",e);
	if(cast(LambdaExp)e) return "lambda";
	return "function";
}

/// reports that `ce` does not type check, where `ft` is the type of the callee and `inferTy` is the type
/// used to infer omitted square-bracket arguments (it differs from `ft` for data type constructors)
void explainCallFailure(CallExp ce,ProductTy ft,ProductTy inferTy,Scope sc){
	if(isGenerated(ce)||isReverseCall(ce)) // (arguments do not correspond to source code, or the type of `reverse` does not describe its use)
		return reportCallFailure(ce,ft,sc);
	auto fun=describeFunction(ce);
	if(ce.isSquare&&!ft.isSquare){
		sc.error(format("%s takes arguments in parentheses, not square brackets",fun),ce.loc);
		sc.note(format("%s has type `%s`",fun,ft),ce.e.loc);
		return;
	}
	if(!ce.isSquare&&ft.isSquare){
		auto codft=inferTy?cast(ProductTy)inferTy.cod:null;
		if(!codft){
			sc.error(format("%s takes arguments in square brackets, not parentheses",fun),ce.loc);
			sc.note(format("%s has type `%s`",fun,ft),ce.e.loc);
			auto callee=calleeText(ce);
			if(callee.length&&isTypeTy(ft.cod)&&!cast(TupleExp)ce.arg){ // e.g., `int(x)` instead of `x as int[n]`
				auto type=format("%s[%s]",callee,iota(ft.nargs).map!(i=>ft.names[i]?ft.names[i].str:"…").join(", "));
				sc.note(format("to convert `%s` to type `%s`, use `%s as %s`",stripParens(ce.arg.loc).rep,type,operandText(ce.arg),type),ce.loc);
			}
			return;
		}
		if(!codft.isSquare&&isAnalyzed(ce.arg)&&explainInferenceFailure(ce,inferTy,codft,sc,fun))
			return;
		return reportCallFailure(ce,ft,sc);
	}
	if(isAnalyzed(ce.arg)&&explainArgumentMismatch(ce,ft,sc,fun))
		return;
	reportCallFailure(ce,ft,sc);
}

/// reports a call to a function of type `ft` with `provided` arguments, which is the wrong number
/// (`tupleLength`: number of elements of a single tuple argument passed instead of separate arguments)
void explainArgumentCount(CallExp ce,ProductTy ft,size_t provided,Scope sc,size_t tupleLength=size_t.max){
	auto fun=describeFunction(ce);
	auto expected=ft.nargs;
	if(tupleLength!=size_t.max){
		sc.error(format("%s takes %s, but a tuple of %s elements was provided",fun,countArguments(expected,ft.isSquare),tupleLength),ce.loc);
		return;
	}
	auto decls=parameterDecls(ce.e,ft);
	if(ft.isTuple&&expected==1&&provided==1&&!cast(TupleExp)ce.arg){ // e.g., `f(x)` for `def f(x:𝔹,)`
		sc.error(format("%s takes a tuple with 1 element, but a single value was provided",fun),ce.loc);
		sc.note(format("add a trailing comma to pass a tuple with one element: `%s`",oneTupleCall(ce,ft.isSquare,true)),ce.loc);
		if(showDecls(decls)) sc.note("the trailing comma makes the parameter list a tuple with one element",decls[0].loc);
		return;
	}
	sc.error(format("%s takes %s, but %s %s provided",fun,countArguments(expected,ft.isSquare),provided,provided==1?"was":"were"),ce.loc);
	if(provided<expected){
		foreach(i;provided..expected){
			if(showDecls(decls)) sc.note(format("missing argument for %s",describeParam(ft,decls,i)),decls[i].loc);
			else sc.note(format("missing argument for %s of type `%s`",describeParam(ft,decls,i),ft.argTy(i)),ce.loc);
		}
	}else if(auto tpl=cast(TupleExp)ce.arg){
		foreach(i;expected..min(provided,tpl.length))
			sc.note("extra argument",tpl.e[i].loc);
		if(isPreludeSymbol(cast(Identifier)unwrap(ce.e))=="phase"&&tpl.length==2) // (e.g., `phase(φ, q)`, as for `R1(φ, q)`)
			sc.note(format("`phase(φ)` multiplies the state by `e^(iφ)`, to shift the phase of `%s` use `if %s { phase(%s); }`",sourceText(tpl.e[1]),sourceText(tpl.e[1]),sourceText(tpl.e[0])),ce.loc);
	}else if(expected==0) sc.note("extra argument",stripParens(ce.arg.loc));
}

/// reports a call of a value that is not a function
void explainNotCallable(CallExp ce,Scope sc){
	sc.error(format("cannot call expression of type `%s`",ce.e.type),ce.loc);
	auto callee=unwrap(ce.e);
	if(!ce.isSquare){
		if(explainDoubleStar(callee,sc)) return; // e.g., `x**(n+1)` from Python, parsed as `x * *(n+1)`
		if(sourceText(ce.e).endsWith(".length")){ // (`x.length` may already be replaced by its value)
			sc.note(format("`length` is not a function, use `%s` without parentheses",sourceText(ce.e)),ce.loc);
			return;
		}
		if(isType(callee)||isQNumeric(callee)){ // e.g., `𝔹(x)` instead of `x as 𝔹`
			explainTypeCall(ce,sc);
			return;
		}
		auto ty=ce.e.type;
		if(cast(VectorTy)ty||cast(ArrayTy)ty||ty.isTupleTy()||isFixedIntTy(ty)){ // e.g., `x(0)` instead of `x[0]`
			sc.note(format("use square brackets for indexing: `%s[%s]`",operandText(ce.e),stripParens(ce.arg.loc).rep),ce.loc);
			return;
		}
	}
	if(auto id=cast(Identifier)callee)
		if(id.meaning&&id.meaning.loc.rep.length)
			sc.note(format("`%s` declared here",id),id.meaning.loc);
}

/// explains a call of a type, e.g., `uint[3](x)` instead of the conversion `x as uint[3]`
void explainTypeCall(CallExp ce,Scope sc){
	if(ce.isSquare) return;
	if(auto tpl=cast(TupleExp)ce.arg) if(tpl.length!=1) return;
	auto type=sourceText(ce.e);
	if(precededBy(ce.loc,'!')) type="!"~type; // (`!ℝ(x)` is parsed as `!(ℝ(x))`)
	auto arg=stripParens(ce.arg.loc).rep;
	sc.note(format("to convert `%s` to type `%s`, use `%s as %s`",arg,type,operandText(ce.arg),type),ce.loc);
}

/// the kind of integer that a value of type `type` has to be (`ℕt` or `ℤt`), or `none` if it is not an integer type
NumericType integralKind(Expression type){
	if(!type) return NumericType.none;
	switch(isNumericTy(type)){
		case NumericType.ℕt: return NumericType.ℕt;
		case NumericType.ℤt: return NumericType.ℤt;
		default: return isFixedIntTy(type)?NumericType.ℤt:NumericType.none;
	}
}

/// explains why the operands `e1` and `e2` of an arithmetic operation `name` have incompatible types
void explainIncompatibleOperands(Scope sc,Expression e1,Expression e2,string name){
	if(name=="division"&&integralKind(e1.type)&&integralKind(e2.type)&&iDivType(e1.type,e2.type)){ // (e.g., `x/2` for `x:uint[n]`)
		sc.note(format("`/` is rational division, use `%s div %s` for integer division",operandText(e1),operandText(e2)),e1.loc.to(e2.loc));
		return;
	}
	foreach(swap;0..2){
		auto a=swap?e2:e1, b=swap?e1:e2;
		if(isFixedIntTy(b.type)&&explainNumericType(sc,a,NumericType.ℤt)) // (e.g., `x+=2^(n-1)` for `x:uint[n]`)
			return;
		if(name=="multiplication"&&explainDoubleStar(e2,sc)) return; // e.g., `x**-1` from Python, parsed as `(x * *) - 1`
		if(name=="multiplication"){ // (e.g., `[0:𝔹]*3` for repetition, as in Python)
			auto vec=cast(VectorExp)unwrap(a);
			if(vec&&vec.e.length==1&&isSubtype(b.type,ℕt(true))){
				sc.note(format("did you mean `vector(%s, %s)`?",sourceText(b),sourceText(vec.e[0])),e1.loc.to(e2.loc));
				return;
			}
		}
	}
}

/// error recovery for a default value of parameter `p`, e.g., `n: !ℕ=3`, where the type is parsed as `!ℕ=3`:
/// reports it and removes the default value
void removeDefaultValue(Parameter p,Scope sc){
	auto eq=cast(EqExp)p.dtype;
	if(!eq||eq.brackets) return;
	auto end=eq.e1.loc.rep.ptr+eq.e1.loc.rep.length;
	sc.error("parameters cannot have default values",Location(end[0..eq.e2.loc.rep.ptr+eq.e2.loc.rep.length-end],eq.e2.loc.line));
	p.dtype=eq.e1;
	p.setSemForceError();
}

/// explains why classical number `e` is not of kind `wanted` (`ℕt` or `ℤt`), e.g., `!ℚ` because of `/` instead of `div`
/// (returns whether any note was given)
bool explainNumericType(Scope sc,Expression e,NumericType wanted){
	if(wanted!=NumericType.ℕt&&wanted!=NumericType.ℤt) return false;
	NumericCause cause;
	if(!cause.explain(e,wanted)) return false;
	foreach(n;cause.notes) sc.note(n.msg,n.loc);
	return true;
}

/// explains why `id` is undefined, e.g., a name that differs only in case or a name from another language (such as `True` or `CX`)
/// (`called`: whether `id` is called; other short names are often variables, e.g., `x`, so they are only related to constants)
/// (`inType`: whether `id` is used in a type, then only names of types are suggested)
void explainUndefinedIdentifier(Identifier id,Scope sc,bool called=false,bool inType=false){
	if(!id.name.length) return;
	auto similar=similarNames(id.name,sc,inType);
	if(!called&&id.name.walkLength<=2) similar=similar.filter!(n=>!!util.among(n,"pi","true","false")).array;
	if(similar.length){
		sc.note(format("did you mean %s?",similar.map!(n=>format("`%s`",n)).join(" or ")),id.loc);
		return;
	}
	if(auto name=silqEquivalent(id.name,called)){
		sc.note(format("did you mean `%s`?",name),id.loc);
		return;
	}
	if(auto hint=foreignNameHint(id.name,called)) sc.note(hint,id.loc);
}

/// whether `ae` assigns only to undefined variables, e.g., `x = 3`, which is likely meant to be a definition `x := 3`
bool isUndefinedAssignment(AssignExp ae,Scope sc){
	auto ids=undefinedAssignees(ae.e1,sc);
	return ids.length&&!ids.any!(id=>ae.e2.hasFreeIdentifier(id.id));
}

/// error recovery for an assignment `ae` to undefined variables (see `isUndefinedAssignment`): reports it and analyzes
/// the definition `x := e` instead, which avoids errors for later uses of the variables
/// (returns `null` in a branch, where a definition would cause errors for variables defined on only one path)
Expression defineUndefinedAssignment(AssignExp ae,Scope sc,ref StmFlags flags){
	for(auto nsc=cast(NestedScope)sc;nsc&&!cast(FunctionScope)nsc;nsc=cast(NestedScope)nsc.parent){
		if(auto bsc=cast(BlockScope)nsc) if(bsc.isLoopBody) break;
		if(nsc.getSiblingScopes().length>1) return null;
	}
	foreach(id;undefinedAssignees(ae.e1,sc)) sc.error(format("undefined identifier `%s`",id.name),id.loc);
	explainUndefinedAssignment(ae,sc);
	auto de=new DefineExp(ae.e1,ae.e2);
	de.loc=ae.loc;
	auto r=statementSemantic(de,sc,flags);
	r.setSemForceError();
	return r;
}

/// explains an assignment `x = e` to an undefined variable `x`, which is likely meant to be a definition `x := e`
void explainUndefinedAssignment(AssignExp ae,Scope sc){
	auto lhs=componentsText(ae.e1), rhs=componentsText(ae.e2);
	auto what=cast(TupleExp)ae.e1?"new variables":"a new variable";
	if(lhs.length+rhs.length<=60&&!rhs.canFind('\n')) sc.note(format("use `:=` to define %s: `%s := %s`",what,lhs,rhs),ae.loc);
	else sc.note(format("use `:=` to define %s",what),ae.loc);
}

/// error recovery for a multiple assignment without parentheses, e.g., `a, b = b, a` (as in Python): reports it and
/// analyzes the assignment `(a, b) = (b, a)` or the definition `(a, b) := (b, a)` instead (returns `null` if `ce` is not
/// such an assignment)
Expression parenthesizeAssignment(CommaExp ce,Scope sc,ref StmFlags flags,bool resetConst){
	auto ae=parenthesizedAssignment(ce,sc);
	if(!ae) return null;
	sc.error("multiple values must be enclosed in parentheses",ce.loc);
	sc.note(format("use `%s %s %s`",componentsText(ae.e1),cast(DefineExp)ae?":=":"=",componentsText(ae.e2)),ce.loc);
	auto r=statementSemantic(ae,sc,flags,resetConst);
	r.setSemForceError();
	return r;
}

/// error recovery for a `for` loop over an erroneous container, e.g., `for i in range(n)`: the container is replaced by an
/// empty range (returns whether it was replaced, then the loop variable should have type `⊥`, so its uses are not reported)
bool replaceErroneousContainer(ForExp fe,ExpSemContext context){
	auto cnt=fe.aggr.isContainer();
	if(!cnt||!cnt.e.isSemError()) return false;
	Expression bound(){
		auto r=LiteralExp.makeInteger(0);
		r.loc=cnt.e.loc;
		return expressionSemantic(r,context.nestConst);
	}
	fe.aggr=ForAggregate(ForRange(false,bound(),null,true,bound()));
	return true;
}

/// records for diagnostics that the type of the variable defined by `de` is annotated, e.g., `q:=1/2:!ℚ` (see `VarDecl.explicitType`)
void recordExplicitType(DefineExp de){
	if(!cast(TypeAnnotationExp)de.e1&&!cast(TypeAnnotationExp)de.e2) return;
	if(auto id=cast(Identifier)unwrap(de.e1))
		if(auto vd=cast(VarDecl)id.meaning) vd.explicitType=true;
}

/// explains an index that is not a slice, e.g., `x[1:3]` instead of `x[1..3]`, where `index` is the index before analysis
void explainSliceSyntax(IndexExp idx,Expression index,Scope sc){
	auto tae=cast(TypeAnnotationExp)index;
	if(!tae||tae.annotationType!=TypeAnnotationType.annotation||!tae.t.isSemError()||!tae.t.type||isType(tae.t)||isQNumeric(tae.t)||idx.e.isSemError()||isType(idx.e)) return;
	sc.note(format("to take a slice, use `%s[%s..%s]`",operandText(idx.e),sourceText(tae.e),sourceText(tae.t)),stripParens(tae.loc));
}

/// explains a missing member, e.g., `x.size` instead of `x.length`, or a function used like a method, e.g., `x.measure()`
void explainNoMember(FieldExp fe,Scope sc){
	import std.uni: icmp;
	auto name=fe.f.name, ty=fe.e.type;
	if(!ty) return;
	auto receiver=operandText(fe.e);
	if(cast(VectorTy)ty||cast(ArrayTy)ty||ty.isTupleTy()){
		if(!icmp(name,"length")||util.among(name,"size","Size","len","Len","count","Count","shape","numel")){
			sc.note(format("did you mean `%s.length`?",receiver),fe.loc);
			return;
		}
	}
	ProductTy ft;
	auto fname=visibleFunction(name,sc,ft);
	if(!fname.length){
		if(auto hint=foreignNameHint(name,true)) sc.note(hint,fe.loc);
		return;
	}
	if(auto use=methodCallSuggestion(fname,ft,receiver,ty)){
		sc.note(format("`%s` is a function, not a member: use `%s`",fname,use),fe.loc);
		return;
	}
	if(auto next=elementType(ty)){ // e.g., `x.h(0)` for a vector of qubits `x`
		auto elem=receiver~"[i]";
		if(auto use=methodCallSuggestion(fname,ft,elem,next)){
			sc.note(format("`%s` is a function, not a member: use `%s` for an element `%s`",fname,use,elem),fe.loc);
			return;
		}
	}
	sc.note(format("`%s` is a function, not a member",fname),fe.loc);
}

/// explains why a type annotation does not type check, e.g., `0:𝔹^3` instead of `vector(3, 0:𝔹)`
bool explainAnnotationMismatch(TypeAnnotationExp tae,Scope sc){
	auto e=tae.e;
	if(auto vt=cast(VectorTy)tae.type){
		if(e.type&&e.type.isClassical()&&isSubtype(e.type,vt.next)){
			auto elem=e.type==vt.next?sourceText(e):format("%s:%s",operandText(e),vt.next);
			sc.note(format("did you mean `vector(%s, %s)`?",display(vt.num),elem),tae.loc);
			return true;
		}
	}
	return explainNumericType(sc,e,integralKind(tae.type));
}

/// explains that `decl` (referred to by `id`) is not a type, e.g., `int` instead of `int[n]`
bool explainNotAType(Identifier id,Declaration decl,Scope sc){
	auto dat=cast(DatDecl)decl;
	if(!dat||!dat.hasParams) return false;
	switch(isPreludeSymbol(dat)){
		case "int": sc.note("use `int[n]` for `n`-bit signed integers, or `!ℤ` for classical integers of any size",id.loc); return true;
		case "uint": sc.note("use `uint[n]` for `n`-bit unsigned integers, or `!ℕ` for classical natural numbers of any size",id.loc); return true;
		default: break;
	}
	sc.note(format("`%s` takes square-bracket arguments: `%s[%s]`",id.name,id.name,dat.params.map!(p=>p.getName).join(", ")),id.loc);
	if(!isInPrelude(dat)) sc.note("declared here",dat.loc);
	return true;
}

/// explains the negative index `c` of `idx` (negative indices do not count from the end)
void explainNegativeIndex(IndexExp idx,ℤ c,Scope sc){
	if(!idx) return;
	auto ty=idx.e.type;
	if(cast(VectorTy)ty||cast(ArrayTy)ty||ty&&ty.isTupleTy()){
		auto x=operandText(idx.e);
		sc.note(format("negative indices do not count from the end, use `%s[%s.length-%s]`",x,x,-c),stripParens(idx.a.loc));
	}else sc.note("negative indices do not count from the end",stripParens(idx.a.loc));
}

/// explains why the components of `tpl` cannot be defined by unpacking `rhs` of type `type`, e.g., `(a, b) := CNOT(a, b)`
void explainUnpacking(TupleExp tpl,Expression rhs,Expression type,Scope sc){
	auto ce=rhs?cast(CallExp)unwrap(rhs):null;
	auto ft=ce&&ce.e.type?cast(ProductTy)ce.e.type:null;
	if(!ft||ft.isSquare!=ce.isSquare||!type) return;
	auto args=callArguments(ce,ft);
	if(!args.length) return;
	static string name(Expression e){
		auto id=cast(Identifier)unwrap(e);
		return id?id.name:null;
	}
	string[] constArgs;
	foreach(i,arg;args)
		if(ft.isConst[i]&&name(arg).length&&tpl.e.any!(e=>name(e)==name(arg)))
			constArgs~=name(arg);
	if(!constArgs.length) return;
	auto rest=tpl.e.filter!(e=>!constArgs.canFind(name(e))).map!(e=>sourceText(e)).array;
	auto rtpl=type.isTupleTy();
	if(!(rest.length==1&&!rtpl||rtpl&&rest.length==rtpl.length)) return;
	auto lhs=rest.length==1?rest[0]:"("~rest.join(", ")~")";
	auto names=constArgs.map!(n=>format("`%s`",n)).join(" and ");
	sc.note(format("%s takes %s as `const` and does not return %s, use `%s := %s`",describeFunction(ce),names,constArgs.length==1?"it":"them",lhs,sourceText(ce)),tpl.loc);
}

/// reports that the result of the call statement `discarded` cannot be discarded if `expr` (not `lifted`) is that call,
/// e.g., `H(x);` instead of `x := H(x);` (returns whether it was reported)
bool discardedCallError(Expression expr,CallExp discarded,Scope sc){
	auto ce=cast(CallExp)expr;
	if(!ce||!discarded||ce.loc.rep !is discarded.loc.rep) return false;
	sc.error("cannot discard result of call that is not `lifted`",ce.loc);
	if(auto update=updateSuggestion(ce))
		sc.note(format("use `%s` to update %s",update.code,update.vars),ce.loc);
	return true;
}

/// explains why the call statement `ce` cannot consume the component `idx`, e.g., `H(x[i]);` instead of `x[i] := H(x[i]);`
bool explainConsumedComponent(IndexExp idx,CallExp ce,Scope sc){
	auto ft=ce&&ce.e.type?cast(ProductTy)ce.e.type:null;
	if(!ft||ft.isSquare!=ce.isSquare||ft.cod.hasAnyFreeVar(ft.names)) return false;
	auto k=callArguments(ce,ft).countUntil!(arg=>unwrap(arg) is idx);
	if(k==-1||ft.isConst[k]||ft.cod!=ft.argTy(k)) return false;
	sc.note(format("use `%s := %s` to update `%s`",sourceText(idx),sourceText(ce),sourceText(idx)),idx.loc);
	return true;
}

/// warns about a call statement `stm` whose result is uncomputed, so the statement has no effect, e.g., `X(x);`
void warnDiscardedCall(Expression stm,Scope sc){
	if(auto ce=cast(CompoundExp)stm) if(ce.s.length==1) stm=ce.s[0]; // (a call may be wrapped, e.g., to hoist temporaries)
	auto ce=cast(CallExp)stm;
	if(!ce||!ce.isSemCompleted()||!ce.type||ce.type.isClassical()||isGenerated(ce)) return;
	auto update=updateSuggestion(ce);
	if(!update||!shouldWarn(sc,ce.loc)) return;
	sc.handler.warning(format("call does not modify %s, its result is discarded",update.vars),ce.loc);
	sc.note(format("use `%s` to update %s",update.code,update.vars),ce.loc);
}

/// explains an unsupported expression, e.g., `x++` instead of `x += 1`
void explainUnsupportedExpression(Expression e,Scope sc){
	if(auto pe=cast(PostfixExp!(Tok!"++"))e) sc.note(format("use `%s += 1`",sourceText(pe.e)),e.loc);
	else if(auto pe=cast(PostfixExp!(Tok!"--"))e) sc.note(format("use `%s -= 1`",sourceText(pe.e)),e.loc);
}

private:

/// explains the identifier `e` for the kind `*` after `*`, i.e., `**` as in Python (returns whether it was explained)
bool explainDoubleStar(Expression e,Scope sc){
	auto id=cast(Identifier)e;
	if(!id||id.name!="*"||!precededBy(id.loc,'*')) return false;
	sc.note("`**` is not an operator, use `^` for exponentiation",Location((id.loc.rep.ptr-1)[0..2],id.loc.line));
	return true;
}

/// the variables assigned by `lhs` if none of them are defined, e.g., `x` for `x = 3` (likely meant to be a definition `x := 3`)
Identifier[] undefinedAssignees(Expression lhs,Scope sc){
	Identifier undefined(Expression e){
		if(auto tae=cast(TypeAnnotationExp)e) if(tae.annotationType==TypeAnnotationType.annotation) e=tae.e;
		if(auto ce=cast(UnaryExp!(Tok!"const"))e) e=ce.e; // (e.g., `const x = 3`)
		auto id=cast(Identifier)e;
		if(!id||id.meaning||!id.name.length||isBuiltIn(id)) return null;
		DeadDecl[] failures;
		if(sc.lookup(id,false,true,Lookup.probing,&failures)||failures.length) return null;
		return id;
	}
	Expression[] components=[lhs];
	if(auto tpl=cast(TupleExp)lhs) components=tpl.e;
	Identifier[] result;
	foreach(e;components){
		auto id=undefined(e);
		if(!id) return null;
		result~=id;
	}
	return result;
}

/// for `ce` of the form `a, b = b, a` (as in Python) or `a, b := b, a` (as in Go), the definition `(a, b) := (b, a)` if
/// each variable is new or used on the right-hand side (e.g., for a swap), and otherwise the assignment `(a, b) = (b, a)`
/// (`null` if `ce` is not of this form)
ABinaryExp parenthesizedAssignment(CommaExp ce,Scope sc){
	Expression[] elements;
	void flatten(Expression e){
		if(auto c=cast(CommaExp)e) if(!c.brackets){
			flatten(c.e1);
			flatten(c.e2);
			return;
		}
		elements~=e;
	}
	flatten(ce);
	if(elements.length<3||elements.length%2==0) return null;
	auto k=elements.length/2;
	auto ae=cast(ABinaryExp)elements[k];
	if(!(cast(AssignExp)ae||cast(DefineExp)ae)||ae.brackets||!isAssignable(ae.e1)) return null;
	foreach(i,e;elements) if(i!=k&&(cast(AssignExp)e||cast(DefineExp)e||i<k&&!isAssignable(e))) return null;
	auto lhs=new TupleExp(elements[0..k]~ae.e1), rhs=new TupleExp(ae.e2~elements[k+1..$]);
	lhs.loc=elements[0].loc.to(ae.e1.loc);
	rhs.loc=ae.e2.loc.to(elements[$-1].loc);
	bool isNewOrUsed(Expression e){
		auto id=assignedVariable(e);
		return !sc.lookup(id,false,true,Lookup.probing,null)||rhs.hasFreeIdentifier(id.id);
	}
	ABinaryExp r=lhs.e.all!isNewOrUsed?new DefineExp(lhs,rhs):new AssignExp(lhs,rhs);
	r.loc=ce.loc;
	return r;
}

/// the variable that `e` assigns to, e.g., `x` for `x[i]` (where `isAssignable(e)`)
Identifier assignedVariable(Expression e){
	e=unwrap(e);
	if(auto idx=cast(IndexExp)e) return assignedVariable(idx.e);
	return cast(Identifier)e;
}

struct Note{
	string msg;
	Location loc;
}

NumericType classicalNumericTy(Expression type){
	return type&&type.isClassical()?isNumericTy(type):NumericType.none;
}

/// the classical numeric type of operand `e`, where a variable whose type is widened by a loop has its type before the loop
/// (e.g., `x` in `x/2` for `x:=1; while c { x=x/2; }`, as the loop body only widens the type of `x` because of `/`)
NumericType operandNumericTy(Expression e){
	auto ty=classicalNumericTy(e.type);
	auto id=cast(Identifier)unwrap(e);
	for(auto vd=id?cast(VarDecl)id.meaning:null;vd;vd=cast(VarDecl)vd.splitFrom){
		auto sty=classicalNumericTy(vd.vtype);
		if(sty&&sty<ty) ty=sty;
	}
	return ty;
}

/// finds the cause of an expression not being a classical number of a given kind, with notes explaining it
struct NumericCause{
	Note[] notes;
	Declaration[] visited; // (variables whose types are traced, each is explained at most once)
	Expression update; // (the operation of an update that is traced, e.g., `x - 1` for `x -= 1`, which is suggested to be `x sub= 1`)

	/// finds the cause of `e` not being a classical number of kind `wanted` (returns whether it was found)
	bool explain(Expression e,NumericType wanted,int depth=0){
		if(!e||!e.type||depth>8) return false;
		if(depth&&cast(TypeAnnotationExp)e) return false; // (the type is explicit, e.g., for `q:=1/2:!ℚ`)
		auto ty=classicalNumericTy(e.type);
		if(!ty||ty<=wanted) return false;
		bool rec(Expression sub,NumericType w){ return explain(sub,w,depth+1); }
		auto ue=unwrap(e);
		auto loc=stripParens(e.loc);
		if(auto de=cast(DivExp)ue){
			auto t1=operandNumericTy(de.e1), t2=operandNumericTy(de.e2);
			if(t1&&t2&&t1<=NumericType.ℤt&&t2<=NumericType.ℤt){
				notes~=Note(format("`/` is rational division, use `%s div%s %s` for integer division",operandText(de.e1),ue is update?"=":"",operandText(de.e2)),loc);
				auto rty=max(t1,t2,NumericType.ℕt); // (type of the result of `div`)
				if(rty>wanted) rec(t1>wanted?de.e1:de.e2,wanted);
				return true;
			}
			return rec(de.e1,wanted)||rec(de.e2,wanted);
		}
		if(auto se=cast(SubExp)ue){
			auto t1=operandNumericTy(se.e1), t2=operandNumericTy(se.e2);
			if(wanted==NumericType.ℕt&&t1&&t2&&t1<=NumericType.ℕt&&t2<=NumericType.ℕt){
				notes~=Note(format("subtracting natural numbers yields an integer, use `%s sub%s %s` for natural subtraction (checked to be non-negative)",operandText(se.e1),ue is update?"=":"",operandText(se.e2)),loc);
				return true;
			}
			return rec(se.e1,wanted)||rec(se.e2,wanted);
		}
		if(auto pe=cast(PowExp)ue){
			auto tb=operandNumericTy(pe.e1), tx=operandNumericTy(pe.e2);
			if(tb&&tb<=NumericType.ℤt&&tx==NumericType.ℤt){ // (an integer exponent may be negative)
				notes~=Note(format("`%s` is rational because the exponent `%s` is an integer (it may be negative)",sourceText(ue),sourceText(pe.e2)),loc);
				rec(pe.e2,NumericType.ℕt);
				return true;
			}
			return rec(pe.e1,wanted)||rec(pe.e2,NumericType.ℕt);
		}
		if(auto ume=cast(UMinusExp)ue){
			if(auto lit=cast(LiteralExp)ume.e) if(wanted==NumericType.ℕt&&classicalNumericTy(lit.type)<=NumericType.ℕt){
				notes~=Note(format("`%s` is negative",sourceText(ue)),loc);
				return true;
			}
			return rec(ume.e,wanted);
		}
		if(cast(AddExp)ue||cast(MulExp)ue||cast(ModExp)ue||cast(IDivExp)ue||cast(NSubExp)ue){
			auto be=cast(ABinaryExp)ue;
			return rec(be.e1,wanted)||rec(be.e2,wanted);
		}
		if(auto lit=cast(LiteralExp)ue){
			if(wanted<=NumericType.ℤt&&ty>NumericType.ℤt){
				notes~=Note(format("`%s` is not an integer",sourceText(ue)),loc);
				return true;
			}
			return false;
		}
		if(auto id=cast(Identifier)ue) return variable(cast(VarDecl)id.meaning,e,wanted,depth);
		return false;
	}

	/// traces the type of variable `vd` (used in `use`) to where it is determined, e.g., its definition or an assignment in a branch
	bool variable(VarDecl vd,Expression use,NumericType wanted,int depth){
		if(!vd||vd.explicitType||depth>8||visited.canFind(vd)||classicalNumericTy(vd.vtype)<=wanted) return false;
		visited~=vd;
		bool explainVia(scope bool delegate() sources,string msg){ // (the note for `vd` precedes the notes explaining its sources)
			auto k=notes.length;
			if(!sources()) return false;
			notes=notes[0..k]~Note(format(msg,vd.getName,vd.vtype),vd.loc)~notes[k..$];
			return true;
		}
		bool via(Expression source,string msg){
			return source&&explainVia(()=>explain(source,wanted,depth+1),msg);
		}
		if(auto fe=cast(ForExp)vd.typeSource){
			auto range=fe.aggr.isRange;
			return range&&explainVia(()=>explain(range.left,wanted,depth+1)||explain(range.right,wanted,depth+1),"`%s` has type `%s` because of the bounds of the loop");
		}
		if(vd.loweredFrom) return variable(vd.loweredFrom,use,wanted,depth+1);
		if(auto ae=cast(AssignExp)vd.typeSource) return via(assignedValue(ae.e1,ae.e2,vd.getName),"`%s` is assigned a value of type `%s` here");
		if(auto ae=cast(AAssignExp)vd.typeSource) return via(update=updateOperation(ae),"`%s` is updated to type `%s` here");
		if(vd.initializer) return vd.initializer!is use&&via(vd.initializer,"`%s` is defined with type `%s` here");
		if(vd.mergedFrom.length){ // (defined on several paths, e.g., in both branches of an `if`)
			bool found=false;
			foreach(d;vd.mergedFrom) found|=variable(cast(VarDecl)d,use,wanted,depth+1);
			return found;
		}
		return variable(cast(VarDecl)vd.splitFrom,use,wanted,depth+1);
	}
}

/// the value assigned to variable `name` by `lhs = rhs`, e.g., `n/2` for `x` in `(x, y) = (n/2, 3)`
Expression assignedValue(Expression lhs,Expression rhs,string name){
	if(auto id=cast(Identifier)lhs) return id.name==name?rhs:null;
	auto tl=cast(TupleExp)lhs, tr=cast(TupleExp)unwrap(rhs);
	if(tl&&tr&&tl.length==tr.length)
		foreach(i;0..tl.length)
			if(auto r=assignedValue(tl.e[i],tr.e[i],name))
				return r;
	return null;
}

/// the operation performed by an update `ae`, e.g., `x + n/2` for `x += n/2`
Expression updateOperation(AAssignExp ae){
	import ast.parser: binaryOps;
	static foreach(op;binaryOps)
		static if(op.endsWith("←")&&op!="←")
			if(auto be=cast(BinaryExp!(Tok!op))ae)
				return be.operation;
	return null;
}

/// `ce` with a single argument `x` passed as `(x,)` if `asTuple`, otherwise as `(x)`, e.g., `f(x,)` (or a generic example)
string oneTupleCall(CallExp ce,bool isSquare,bool asTuple){
	auto callee=calleeText(ce), arg=sourceText(asTuple?ce.arg:(cast(TupleExp)ce.arg).e[0]);
	if(!callee||!arg.length||arg.length>40||arg.canFind('\n')) callee="f", arg="x";
	return format("%s%s%s%s%s",callee,isSquare?"[":"(",arg,asTuple?",":"",isSquare?"]":")");
}

/// generic report, used if there is no more specific explanation
void reportCallFailure(CallExp ce,ProductTy ft,Scope sc){
	Expression aty=ce.arg.type?ce.arg.type:ce.arg;
	if(ce.isSquare!=ft.isSquare)
		sc.error(text("function of type `",ft,"` cannot be called with arguments `",ce.isSquare?"[":"",aty,ce.isSquare?"]":"","`"),ce.loc);
	else sc.error(format("expected argument types `%s`, but `%s` was provided",ft.dom,aty),ce.loc);
}

/// whether `ce` was created by the frontend (e.g., a call of a reversed function for a call on the left-hand side of `:=`)
bool isGenerated(CallExp ce){
	auto r=ce.loc.rep, a=ce.arg.loc.rep;
	return !r.length||a.length&&r.ptr==a.ptr; // (the location of a call written in the source includes the callee before the arguments)
}

bool isReverseCall(CallExp ce){
	auto id=cast(Identifier)unwrap(ce.e);
	return id&&isPreludeSymbol(id)=="reverse";
}

bool isAnalyzed(Expression arg){
	if(!arg.type) return false;
	if(auto tpl=cast(TupleExp)arg) return tpl.e.all!(e=>!!e.type);
	return true;
}

string countArguments(size_t n,bool isSquare=false){
	auto kind=isSquare?"square-bracket argument":"argument";
	return n==0?format("no %ss",kind):n==1?format("1 %s",kind):format("%s %ss",n,kind);
}

/// `loc` without one level of enclosing brackets (the location of a single argument includes the brackets of the call)
Location stripParens(Location loc){
	auto r=loc.rep;
	if(r.length<3||!(r[0]=='('&&r[$-1]==')'||r[0]=='['&&r[$-1]==']')) return loc; // (`()` is not stripped: the location would be empty)
	int depth=0;
	foreach(i,char c;r[0..$-1]){
		if(c=='('||c=='[') depth++;
		else if((c==')'||c==']')&&--depth==0) return loc; // (brackets do not enclose all of `loc`)
	}
	return Location(r[1..$-1],loc.line);
}

/// `e` as displayed in a note (without enclosing parentheses)
string display(Expression e){
	auto brackets=e.brackets;
	e.brackets=0;
	scope(exit) e.brackets=brackets;
	return e.toString();
}

/// source code of `e`
string sourceText(Expression e){
	return e.loc.rep.length?stripParens(e.loc).rep:display(e);
}

/// source code of `e`, parenthesized if needed to serve as an operand in a suggestion
string operandText(Expression e){
	auto r=sourceText(e);
	int depth=0;
	foreach(dchar c;r){
		if(c=='('||c=='['){ depth++; continue; }
		if(c==')'||c==']'){ depth--; continue; }
		if(depth||c=='_'||c=='\''||c=='.'||isAlphaNum(c)) continue;
		return "("~r~")";
	}
	return r;
}

/// `def f[n](x)` is a function taking `n` that returns a lambda taking `x`
FunctionDef innerFunctionDef(FunctionDef fd){
	if(!fd||!fd.isSquare||!fd.body_||fd.body_.s.length!=1) return null;
	if(auto ret=cast(ReturnExp)fd.body_.s[0]) return calleeFunctionDef(ret.e);
	return null;
}

/// declarations of the parameters of the function of type `ft` that `callee` refers to, if known
Parameter[] parameterDecls(Expression callee,ProductTy ft){
	auto fd=calleeFunctionDef(callee);
	if(fd&&fd.isSquare&&!ft.isSquare) fd=innerFunctionDef(fd);
	if(!fd||fd.isSquare!=ft.isSquare||fd.params.length!=ft.nargs) return null;
	return fd.params;
}

/// whether notes should point to the parameter declarations `decls` (not for prelude functions)
bool showDecls(Parameter[] decls){
	return decls&&!decls.any!(p=>p.scope_&&isInPrelude(p));
}

string parameterName(ProductTy ft,Parameter[] decls,size_t i){
	if(decls&&decls[i].name) return decls[i].getName;
	if(ft.names[i]) return ft.names[i].str;
	return null;
}

string describeParam(ProductTy ft,Parameter[] decls,size_t i){
	auto kind=ft.isSquare?"square-bracket parameter":"parameter";
	auto name=parameterName(ft,decls,i);
	return name.length?format("%s `%s`",kind,name):kind;
}

struct Argument{
	Expression exp;
	Expression type;
	Location loc;
}

/// explains why the arguments of `ce` cannot be passed to the parameters of `ft`, focusing on the problematic arguments
/// (`inferred`: description of inferred square-bracket arguments, if any)
bool explainArgumentMismatch(CallExp ce,ProductTy ft,Scope sc,string fun,string inferred=null){
	auto decls=parameterDecls(ce.e,ft);
	void noteInferred(){
		if(inferred.length) sc.note(inferred,ce.e.loc);
	}
	Argument[] args;
	if(ft.isTuple){
		if(auto tpl=cast(TupleExp)ce.arg){
			if(tpl.length!=ft.nargs){
				explainArgumentCount(ce,ft,tpl.length,sc);
				return true;
			}
			args=tpl.e.map!(e=>Argument(e,e.type,e.loc)).array;
		}else{ // single argument for multiple parameters
			auto ttpl=ce.arg.type.isTupleTy();
			if(!ttpl){
				explainArgumentCount(ce,ft,1,sc);
				return true;
			}
			if(ttpl.length!=ft.nargs){
				explainArgumentCount(ce,ft,1,sc,ttpl.length);
				return true;
			}
			auto failing=iota(ft.nargs).filter!(i=>!isSubtype(ttpl[i],ft.argTy(i))).array;
			if(!failing.length) return false;
			auto loc=stripParens(ce.arg.loc);
			sc.error(format("cannot pass argument of type `%s` to parameters of type `%s`",ce.arg.type,ft.dom),loc);
			foreach(i;failing){
				sc.note(format("element at index %s has type `%s`, but %s has type `%s`",i,ttpl[i],describeParam(ft,decls,i),ft.argTy(i)),loc);
				explainMismatch(sc,null,ttpl[i],ft.argTy(i),loc);
			}
			noteInferred();
			if(showDecls(decls)) foreach(i;failing) sc.note(format("%s declared here",describeParam(ft,decls,i)),decls[i].loc);
			return true;
		}
	}else{
		auto tpl=cast(TupleExp)ce.arg;
		if(tpl&&tpl.length!=1&&isScalar(ft.argTy(0))){
			explainArgumentCount(ce,ft,tpl.length,sc);
			return true;
		}
		if(tpl&&tpl.length==1&&tpl.e[0].type&&isSubtype(tpl.e[0].type,ft.argTy(0))){ // e.g., `g(x,)` for `def g(x:𝔹)`
			sc.error(format("%s takes a single argument, but a tuple with 1 element was provided",fun),ce.loc);
			sc.note(format("remove the trailing comma to pass a single argument: `%s`",oneTupleCall(ce,ft.isSquare,false)),ce.loc);
			return true;
		}
		args=[Argument(ce.arg,ce.arg.type,stripParens(ce.arg.loc))];
	}
	auto failing=iota(args.length).filter!(i=>!isSubtype(args[i].type,ft.argTy(i))).array;
	if(!failing.length) return false;
	foreach(i;failing){
		auto pty=ft.argTy(i);
		sc.error(format("cannot pass argument of type `%s` to %s of type `%s`",args[i].type,describeParam(ft,decls,i),pty),args[i].loc);
		explainMismatch(sc,args[i].exp,args[i].type,pty,args[i].loc,!pty.hasAnyFreeVar(ft.names));
		noteInferred();
		if(showDecls(decls)) sc.note(format("%s declared here",describeParam(ft,decls,i)),decls[i].loc);
	}
	noteSwapped(sc,ft,decls,args,failing);
	return true;
}

/// notes that two arguments may have been passed in the wrong order
void noteSwapped(Scope sc,ProductTy ft,Parameter[] decls,Argument[] args,size_t[] failing){
	if(failing.length!=2) return;
	auto i=failing[0], j=failing[1];
	if(!isSubtype(args[i].type,ft.argTy(j))||!isSubtype(args[j].type,ft.argTy(i))) return;
	auto pi=parameterName(ft,decls,i), pj=parameterName(ft,decls,j);
	if(pi.length&&pj.length) sc.note(format("the arguments for parameters `%s` and `%s` may be swapped",pi,pj),args[j].loc);
	else sc.note("these two arguments may be swapped",args[j].loc);
}

/// whether `type` certainly does not accept multiple arguments packed into a tuple
bool isScalar(Expression type){
	return isNumericTy(type)||isFixedIntTy(type)||cast(ProductTy)type;
}

/// whether a literal `e` can be given type `type` with a type annotation (see `annotateLiteral`)
bool literalAnnotatable(Expression e,Expression type){
	if(!isLiteral(e)||!e.type) return false;
	auto lit=cast(LiteralExp)e, negLit=cast(UMinusExp)e?cast(LiteralExp)(cast(UMinusExp)e).e:null;
	if(isSubtype(e.type,ℕt(false))&&isFixedIntTy(type)) return true;
	if(isSubtype(e.type,ℤt(false))&&isInt(type)) return true;
	if(isSubtype(e.type,ℤt(false)))
		if(auto zmod=isℤmodTy(type))
			if(!zmod.isStar||lit&&lit.isOne()||negLit&&negLit.isOne())
				return true;
	if(isSubtype(e.type,ℝ(false))&&(isRat(type)||isFloat(type))) return true;
	return false;
}

/// whether `a` and `b` are known to be equal (`1`), known to differ (`0`), or neither (`-1`)
int compareValues(Expression a,Expression b){
	if(a==b) return 1;
	auto eq=new EqExp(a,b);
	eq.loc=a.loc;
	eq.type=Bool(true);
	eq.setSemCompleted();
	auto r=eq.eval();
	if(r==LiteralExp.makeBoolean(1)) return 1;
	if(r==LiteralExp.makeBoolean(0)) return 0;
	return -1;
}

/// sizes of `from` and `to` if both are vectors with compatible elements or both are fixed-size integers of the same kind
bool getSizes(Expression from,Expression to,out Expression fromSize,out Expression toSize,out string what){
	if(auto fv=cast(VectorTy)from) if(auto tv=cast(VectorTy)to){
		if(!isSubtype(fv.next,tv.next)) return false;
		fromSize=fv.num, toSize=tv.num, what="length";
		return true;
	}
	auto ff=isFixedIntTy(from), tf=isFixedIntTy(to);
	if(ff&&tf&&ff.isSigned==tf.isSigned&&(ff.isClassical||!tf.isClassical)){
		fromSize=ff.bits, toSize=tf.bits, what="bit width";
		return true;
	}
	return false;
}

/// whether integer `v` is in the range of fixed-size integer type `fit` (if the range is known)
bool fitsInto(ℤ v,FixedIntTy fit,out ℤ lo,out ℤ hi){
	auto b=fit.bits.eval().asIntegerConstant();
	if(!b||b.get<0||b.get>1024) return true;
	auto m=ℤ(1)<<b.get.to!size_t;
	lo=fit.isSigned?-(m/2):ℤ(0), hi=(fit.isSigned?m/2:m)-1;
	return lo<=v&&v<=hi;
}

/// explains why value `e` (if known) of type `from` at `loc` cannot be used where type `to` is expected
/// (`concrete`: whether `to` does not depend on unknown parameters, so sizes can be compared and conversions suggested)
void explainMismatch(Scope sc,Expression e,Expression from,Expression to,Location loc,bool concrete=true,int depth=0){
	if(!from||!to||depth>4) return;
	if(e&&!e.type) e=null;
	Expression fromSize,toSize;
	string what;
	if(concrete&&getSizes(from,to,fromSize,toSize,what)){ // (vectors and fixed-size integers)
		auto equal=compareValues(fromSize,toSize);
		if(equal==0){
			sc.note(format("%s `%s` differs from expected %s `%s`",what,display(fromSize),what,display(toSize)),loc);
			return;
		}
		if(equal==-1) sc.note(format("%s `%s` is not known to be equal to `%s`",what,display(fromSize),display(toSize)),loc);
	}
	if(auto ff=isFixedIntTy(from)) if(auto tf=isFixedIntTy(to)) if(ff.isSigned!=tf.isSigned){
		static string signedness(FixedIntTy fit){ return fit.isSigned?"a signed":"an unsigned"; }
		sc.note(format("argument is %s integer, but %s integer is expected",signedness(ff),signedness(tf)),loc);
	}
	if(auto ftpl=from.isTupleTy()) if(auto ttpl=to.isTupleTy()){
		if(ftpl.length!=ttpl.length){
			sc.note(format("tuple has %s elements, but %s %s expected",ftpl.length,ttpl.length,ttpl.length==1?"is":"are"),loc);
			return;
		}
		auto tpl=e?cast(TupleExp)unwrap(e):null;
		if(tpl&&tpl.length!=ftpl.length) tpl=null;
		foreach(i;0..ftpl.length){
			if(isSubtype(ftpl[i],ttpl[i])) continue;
			auto ei=tpl?tpl.e[i]:null;
			auto li=ei?ei.loc:loc;
			sc.note(format("element at index %s has type `%s`, but `%s` is expected",i,ftpl[i],ttpl[i]),li);
			explainMismatch(sc,ei,ftpl[i],ttpl[i],li,concrete,depth+1);
		}
		return;
	}
	if(e&&isType(e)&&!isTypeTy(to)){
		sc.note(format("`%s` is a type, not a value",sourceText(e)),loc);
		return;
	}
	if(auto ffun=cast(ProductTy)from) if(auto tfun=cast(ProductTy)to){
		explainFunctionMismatch(sc,e,ffun,tfun,loc);
		return;
	}
	if(explainElementMismatch(sc,from,to,loc)) return;
	if(e&&e.type.isClassical()){ // (constants that do not have the expected type)
		auto integral=isNumericTy(to)==NumericType.Bool||isNumericTy(to)==NumericType.ℕt||isNumericTy(to)==NumericType.ℤt||isFixedIntTy(to);
		if(auto v=classicalIntConstant(e)){
			if(isNumericTy(to)==NumericType.ℕt&&v.get<0){
				sc.note(format("`%s` is negative",v.get),loc);
				return;
			}
			if(isNumericTy(to)==NumericType.Bool&&v.get!=0&&v.get!=1){
				sc.note(format("`%s` is not a boolean value (`0` or `1`)",v.get),loc);
				return;
			}
			ℤ lo,hi;
			if(auto fit=isFixedIntTy(to)) if(!fitsInto(v.get,fit,lo,hi)){
				sc.note(format("`%s` is out of range for `%s` (from `%s` to `%s`)",v.get,to,lo,hi),loc);
				return;
			}
		}else if(integral&&isLiteral(e)&&isNumericTy(e.type)>NumericType.ℤt){
			sc.note(format("`%s` is not an integer",sourceText(e)),loc);
			return;
		}
	}
	static if(language==silq){
		if(to.isClassical()&&!from.isClassical()){
			sc.note("a classical value is required, but this value is quantum",loc);
			return;
		}
	}
	if(e&&explainNumericType(sc,e,integralKind(to))) return;
	if(!concrete||!e) return;
	if(literalAnnotatable(e,to))
		sc.note(format("did you mean to write `%s:%s`?",operandText(e),to),loc);
	else if(typeExplicitConversion(from,to,TypeAnnotationType.conversion))
		sc.note(format("explicit conversion possible, use `%s as %s`",operandText(e),to),loc);
	else if(typeExplicitConversion(from,to,TypeAnnotationType.coercion))
		sc.note(format("(unsafe type coercion possible, use `%s coerce %s`)",operandText(e),to),loc);
}

/// explains a mismatch between a single element and a vector or fixed-size integer of such elements
bool explainElementMismatch(Scope sc,Expression from,Expression to,Location loc){
	if(auto fv=cast(VectorTy)from) if(isSubtype(fv.next,to)){
		sc.note(format("argument is a vector of `%s`, but a single `%s` is expected",fv.next,to),loc);
		return true;
	}
	if(auto fa=cast(ArrayTy)from) if(isSubtype(fa.next,to)){
		sc.note(format("argument is an array of `%s`, but a single `%s` is expected",fa.next,to),loc);
		return true;
	}
	if(auto ff=isFixedIntTy(from)) if(isSubtype(Bool(ff.isClassical),to)){
		sc.note(format("argument is an integer with `%s` bits, but a single `%s` is expected",display(ff.bits),to),loc);
		return true;
	}
	if(auto tv=cast(VectorTy)to) if(isSubtype(from,tv.next)){
		sc.note(format("a vector of `%s` is expected, but a single `%s` was provided",tv.next,from),loc);
		return true;
	}
	if(auto ta=cast(ArrayTy)to) if(isSubtype(from,ta.next)){
		sc.note(format("an array of `%s` is expected, but a single `%s` was provided",ta.next,from),loc);
		return true;
	}
	return false;
}

/// explains why function `e` (if known) of type `from` cannot be used where a function of type `to` is expected
void explainFunctionMismatch(Scope sc,Expression e,ProductTy from,ProductTy to,Location loc){
	if(from.isSquare!=to.isSquare){
		static string brackets(bool isSquare){ return isSquare?"square brackets":"parentheses"; }
		sc.note(format("function takes arguments in %s, but a function taking arguments in %s is expected",brackets(from.isSquare),brackets(to.isSquare)),loc);
		if(e&&from.isSquare&&cast(ProductTy)from.cod)
			sc.note(format("perhaps provide its square-bracket arguments: `%s[…]`",operandText(e)),loc);
		return;
	}
	if(from.nargs!=to.nargs){
		sc.note(format("function takes %s, but a function taking %s is expected",countArguments(from.nargs),countArguments(to.nargs)),loc);
		return;
	}
	if(from.annotation<to.annotation){
		auto ann=annotationToString(to.annotation);
		if(!e||!explainAnnotation(sc,calleeFunctionDef(e),format("`%s`",sourceText(e)),to.annotation))
			sc.note(format("function is not `%s`",ann),loc);
	}
	static if(language==silq){
		if(to.isClassical_&&!from.isClassical_)
			sc.note("a classical function is required, but this function is quantum",loc);
		foreach(i;0..from.nargs){ // (see `ProductTy.isConstCompatible`)
			if(from.isConst[i]==to.isConst[i]||from.argTy(i).isClassical()||to.argTy(i).isClassical()) continue;
			auto which=from.nargs==1?"its argument":format("its argument at index %s",i);
			if(from.isConst[i]) sc.note(format("function takes %s as `const`, but a function consuming it is expected",which),loc);
			else sc.note(format("function consumes %s, but a function taking it as `const` is expected",which),loc);
		}
	}
	if(from.cod.hasAnyFreeVar(from.names)||to.cod.hasAnyFreeVar(to.names)) return;
	foreach(i;0..from.nargs){
		if(!isSubtype(to.argTy(i),from.argTy(i)))
			sc.note(format("function takes `%s`, but it must accept `%s`",from.argTy(i),to.argTy(i)),loc);
	}
	if(!isSubtype(from.cod,to.cod))
		sc.note(format("function returns `%s`, but it must return `%s`",from.cod,to.cod),loc);
}

/// explains why the square-bracket arguments of `ce` cannot be inferred for `ft`, where `cod` is the type of the
/// function that `ft` returns, mirroring `ProductTy.tryMatch`
bool explainInferenceFailure(CallExp ce,ProductTy ft,ProductTy cod,Scope sc,string fun){
	alias UnificationResult=Expression.UnificationResult;
	auto nnames=ft.freshNames(ce.arg);
	auto sft=nnames!=ft.names?ft.relabelAll(nnames):ft;
	cod=cast(ProductTy)sft.cod;
	if(!cod) return false;
	auto names=sft.names;
	if(ft.names.any!(n=>!n||n.str.startsWith("`"))) return false; // (generated by the frontend)
	string displayName(size_t k){ return ft.names[k].str; }
	auto squareDecls=parameterDecls(ce.e,ft);
	auto roundDecls=parameterDecls(ce.e,cod);
	Expression[] atys,aexps;
	auto tpl=ce.arg.type.isTupleTy();
	if(cod.isTuple&&tpl){
		if(tpl.length!=cod.nargs){
			explainArgumentCount(ce,cod,tpl.length,sc);
			return true;
		}
		atys=iota(tpl.length).map!(i=>tpl[i]).array;
		auto texp=cast(TupleExp)ce.arg;
		aexps=texp&&texp.length==atys.length?texp.e:new Expression[](atys.length);
	}else{
		if(cod.isTuple&&cod.nargs!=1){
			explainArgumentCount(ce,cod,1,sc);
			return true;
		}
		atys=[ce.arg.type];
		aexps=[ce.arg];
	}
	Location argLoc(size_t i){ return i<aexps.length&&aexps[i]&&aexps[i]!is ce.arg?aexps[i].loc:stripParens(ce.arg.loc); }
	MapSX!(Id,UnificationResult) subst;
	foreach(n;names) subst[n]=UnificationResult.init;
	auto source=new size_t[](names.length); // argument that first determined each square-bracket argument
	source[]=size_t.max;
	static Expression boundWithDirection(UnificationResult ur,out bool meet){
		meet=!ur.bound(false);
		return ur.bound(meet);
	}
	static Expression bound(UnificationResult ur){
		bool meet;
		return boundWithDirection(ur,meet);
	}
	foreach(i,aty;atys){
		if(i>=cod.nargs) continue;
		auto before=subst.dup;
		if(cod.argTy(i).unify(aty,subst,false)){
			foreach(k,n;names)
				if(source[k]==size_t.max&&bound(subst[n]))
					source[k]=i;
			continue;
		}
		// unification failed at argument `i`, check whether the argument is compatible on its own
		MapSX!(Id,UnificationResult) alone;
		foreach(n;names) alone[n]=UnificationResult.init;
		auto pty=cod.argTy(i);
		if(pty.unify(aty,alone,false)){
			foreach(k,n;names){
				bool meet;
				auto prior=boundWithDirection(before[n],meet), current=bound(alone[n]);
				if(!prior||!current) continue;
				MapSX!(Id,UnificationResult) noVars;
				if(prior.unify(current,noVars,meet)) continue; // (compatible, as for `Identifier.unifyImpl`)
				sc.error(format("cannot infer `%s` in call to %s",displayName(k),fun),ce.loc);
				string ofType(size_t j,Expression value){ return j<atys.length&&atys[j]!=value?format(" of type `%s`",atys[j]):""; }
				sc.note(format("`%s` inferred as `%s` from this argument%s",displayName(k),display(prior),ofType(source[k],prior)),argLoc(source[k]));
				string reason=isType(prior)&&isType(current)&&!joinTypes(prior,current)?format(" (`%s` and `%s` have no common supertype)",display(prior),display(current)):"";
				sc.note(format("but this argument%s requires `%s` to be `%s`%s",ofType(i,current),displayName(k),display(current),reason),argLoc(i));
				return true;
			}
		}
		sc.error(format("cannot pass argument of type `%s` to %s of type `%s`",aty,describeParam(cod,roundDecls,i),pty),argLoc(i));
		auto known=iota(names.length).filter!(k=>!!bound(before[names[k]])).map!(k=>format("`%s` inferred as `%s`",displayName(k),display(bound(before[names[k]])))).array;
		if(known.length) sc.note(format("with %s from earlier arguments",known.join(", ")),argLoc(i));
		static if(language==silq){
			if(auto id=cast(Identifier)pty){
				auto k=names.countUntil(id.id);
				if(k!=-1&&sft.argTy(k)==ctypeTy()&&!aty.isClassical())
					sc.note(format("`%s` must be a classical type, but `%s` is quantum",displayName(k),aty),argLoc(i));
			}
		}
		Expression asize,psize;
		string what;
		if(getSizes(aty,pty,asize,psize,what)&&psize.hasAnyFreeVar(names)){ // (unification only solves simple equations)
			auto unknowns=iota(names.length).filter!(k=>psize.hasFreeVar(names[k])).map!(k=>format("`%s`",displayName(k))).join(", ");
			sc.note(format("cannot determine %s such that %s `%s` equals `%s`",unknowns,what,display(psize),display(asize)),argLoc(i));
			auto callee=calleeText(ce);
			sc.note(format("square-bracket arguments can be provided explicitly: `%s[…](…)`",callee?callee:operandText(ce.e)),ce.loc);
		}else explainMismatch(sc,aexps[i],aty,pty,argLoc(i),!pty.hasAnyFreeVar(names));
		if(showDecls(roundDecls)) sc.note(format("%s declared here",describeParam(cod,roundDecls,i)),roundDecls[i].loc);
		return true;
	}
	// determine the square-bracket arguments (as in `ProductTy.tryMatch`)
	auto gargs=new Expression[](names.length);
	foreach(k,n;names){
		Expression value=null;
		if(auto low=subst[n].bound(false)){
			if(sft.argTy(k)==qtypeTy||isQNumericTy(sft.argTy(k)))
				low=low.getQuantum();
			if(low&&!value) value=low;
		}
		if(auto high=subst[n].bound(true)){
			if(sft.argTy(k)==ctypeTy)
				high=high.getClassical();
			else if(isQNumericTy(sft.argTy(k)))
				high=high.getQuantum();
			if(high&&!value) value=high;
		}
		if(!value){
			sc.error(format("cannot infer `%s` in call to %s",displayName(k),fun),ce.loc);
			if(!iota(cod.nargs).any!(i=>cod.argTy(i).hasFreeVar(n)))
				sc.note(format("`%s` does not occur in the parameter types of %s",displayName(k),fun),showDecls(squareDecls)?squareDecls[k].loc:ce.loc);
			else sc.note(format("`%s` cannot be determined from the argument types",displayName(k)),stripParens(ce.arg.loc));
			auto callee=calleeText(ce);
			sc.note(format("square-bracket arguments can be provided explicitly: `%s[…](…)`",callee?callee:operandText(ce.e)),ce.loc);
			return true;
		}
		gargs[k]=value;
	}
	Expression garg;
	if(sft.isTuple){
		auto tgarg=new TupleExp(gargs);
		tgarg.type=tupleTy(gargs.map!(garg=>garg.type).array);
		tgarg.setSemCompleted();
		garg=tgarg;
	}else garg=gargs[0];
	string inferredValues(){
		return format("with %s",iota(names.length).map!(k=>format("`%s` inferred as `%s`",displayName(k),display(gargs[k]))).join(", "));
	}
	auto inst=cast(ProductTy)sft.tryApply(garg,true);
	if(!inst){
		foreach(k,n;names){
			if(!gargs[k].type||isSubtype(gargs[k].type,sft.argTy(k))) continue;
			sc.error(format("cannot infer `%s` in call to %s",displayName(k),fun),ce.loc);
			sc.note(format("`%s` inferred as `%s`, but it must have type `%s`",displayName(k),display(gargs[k]),sft.argTy(k)),argLoc(source[k]));
			return true;
		}
		return false;
	}
	return explainArgumentMismatch(ce,inst,sc,fun,inferredValues());
}

/// visible names that are equal to `name` up to case (e.g., `H` for `h`), only names of types if `inType`
string[] similarNames(string name,Scope sc,bool inType=false){
	import std.uni: icmp;
	string[] result;
	void consider(string candidate){
		if(candidate!=name&&!icmp(candidate,name)&&!result.canFind(candidate)) result~=candidate;
	}
	static bool isTypeDecl(Declaration decl){
		if(cast(DatDecl)decl) return true;
		if(auto vd=cast(VarDecl)decl) return vd.vtype&&isTypeTy(vd.vtype);
		return false;
	}
	void visit(Scope s){
		foreach(k,decl;s.symtab)
			if(decl&&!cast(DeadDecl)decl&&(!inType||isTypeDecl(decl))) consider(k.str);
	}
	Scope top=sc;
	for(auto s=sc;s;s=s.parentScope()) visit(top=s);
	if(auto tsc=cast(TopScope)top) foreach(imp;tsc.importedScopes) visit(imp);
	if(!inType) foreach(builtin;["true","false","pi"]) consider(builtin);
	result.sort();
	return result;
}

/// the Silq name for something called `name` in other languages, e.g., `CNOT` for `CX` (if there is a direct equivalent)
/// (`called`: whether `name` is called, names of functions are only related for calls, as they may also be variable names)
string silqEquivalent(string name,bool called){
	if(auto type=sizedIntegerType(name)) return type;
	if(name=="M_PI") return "pi";
	if(!called) return null;
	switch(name){
		case "M","Mz","MZ","MResetZ","measure_all","measureAll","MeasureAll","MultiM": return "measure";
		case "Rx","RX","rx": return "rotX";
		case "Ry","RY","ry": return "rotY";
		case "Rz","RZ","rz": return "rotZ";
		case "CX","cx","Cx": return "CNOT";
		case "hadamard","Hadamard": return "H";
		case "qnot","QNot": return "X";
		case "copy","Copy","clone","Clone","deepcopy": return "dup";
		default: return null;
	}
}

/// e.g., `int[32]` for `int32` or `i32`, and `uint[8]` for `uint8_t` or `u8`
string sizedIntegerType(string name){
	import std.uni: toLower;
	import std.string: chomp;
	auto s=name.chomp("_t").toLower;
	bool isUnsigned=s.startsWith("u");
	if(isUnsigned) s=s[1..$];
	if(s.startsWith("int")) s=s["int".length..$];
	else if(!isUnsigned&&s.startsWith("i")) s=s[1..$];
	else if(!isUnsigned) return null;
	if(!util.among(s,"8","16","32","64","128","256")) return null;
	return format("%s[%s]",isUnsigned?"uint":"int",s);
}

/// a hint for a name that is not defined in Silq, but used in other languages for something that Silq expresses differently
/// (`called`: whether `name` is called, names of functions are only explained for calls, as they may also be variable names)
string foreignNameHint(string name,bool called){
	switch(name){
		// types and values
		case "Qubit","qubit","QUBIT","Qbit","qbit": return "qubits have type `𝔹` (or `B`), a fresh qubit is `0:𝔹`";
		case "Qubits","qubits","QuantumRegister","qreg","QReg": return "a register of `n` fresh qubits is `vector(n, 0:𝔹)`, of type `𝔹^n`";
		case "bit","Bit","cbit","ClassicalRegister","creg","Result": return "classical bits have type `!𝔹`";
		case "One": return "measurement results of qubits have type `!𝔹`, use `true` instead of `One`";
		case "Zero": return "measurement results of qubits have type `!𝔹`, use `false` instead of `Zero`";
		case "integer","Integer","long","Long","BigInt","bigint": return "use `!ℤ` (or `Int`) for classical integers, or `int[n]` for `n`-bit integers";
		case "unsigned","natural","Natural","usize","size_t": return "use `!ℕ` (or `Nat`) for classical natural numbers, or `uint[n]` for `n`-bit unsigned integers";
		case "float","Float","double","Double","f32","f64","float32","float64","number","Number": return "use `!ℝ` (or `Real`) for real numbers";
		case "boolean","Boolean": return "use `𝔹` (or `bool`) for quantum booleans, and `!𝔹` (or `Bool`) for classical booleans";
		case "void","Void": return "use `𝟙` (or `unit`) for the unit type, whose value is `()`";
		case "list","List","Array","ArrayList","Vec","Vector": return "arrays have type `τ[]`, and vectors of length `n` have type `τ^n`";
		case "math","Math","np","numpy","cmath": return "functions and constants such as `sqrt` and `pi` are available without a prefix";
		// statements
		case "break": return "loops cannot be exited early, use a `while` loop with a condition instead";
		case "continue": return "loop iterations cannot be skipped, use an `if` statement instead";
		case "pass": return "no statement is needed, blocks can be empty: `{}`";
		default: break;
	}
	if(!called) return null;
	switch(name){
		// gates and other quantum operations
		case "CY","cy": return "use a quantum `if` for a controlled gate, e.g., `if a { b := Y(b); }`";
		case "CZ","cz": return "use a quantum `if` for a controlled gate, e.g., `if a { b := Z(b); }`";
		case "CH","ch": return "use a quantum `if` for a controlled gate, e.g., `if a { b := H(b); }`";
		case "CCX","ccx","CCNOT","ccnot","Toffoli","toffoli","TOFFOLI": return "use a quantum `if` for a controlled gate, e.g., `if a && b { c := X(c); }`";
		case "SWAP","Swap","swap": return "swap two values with `(a, b) := (b, a)`";
		case "CSWAP","cswap","Fredkin","fredkin": return "use a quantum `if` for a controlled swap, e.g., `if c { (a, b) := (b, a); }`";
		case "R1","P","U1","u1","PhaseShift","phase_shift": return "use `phase` under a quantum `if` to shift the phase of a qubit `q`, e.g., `if q { phase(φ); }`";
		case "CP","cp","CPhase","cphase","CR1","CU1","cu1": return "use `phase` under a quantum `if` for a controlled phase shift, e.g., `if a && b { phase(φ); }`";
		case "Sdg","sdg","SDG","Sdag","sdag","SAdj": return "use `reverse(S)` for the inverse of `S`";
		case "Tdg","tdg","TDG","Tdag","tdag","TAdj": return "use `reverse(T)` for the inverse of `T`";
		case "Adjoint","adjoint","Inverse","inverse","inv","Dagger","dagger","dag": return "use `reverse(f)` for the inverse of a function `f`";
		case "Controlled","controlled","Ctrl","ctrl","control": return "use a quantum `if` to control an operation, e.g., `if c { x := f(x); }`";
		case "Reset","reset","ResetAll","resetAll": return "to discard a qubit `x`, measure it: `measure(x);`";
		case "qalloc","alloc","allocate": return "a register of `n` fresh qubits is `vector(n, 0:𝔹)`, of type `𝔹^n`";
		case "ApplyToEach","ApplyToEachA","ApplyToEachC","ApplyToEachCA": return "use a `for` loop, e.g., `for i in [0..n) { x[i] := H(x[i]); }`";
		// other functions
		case "len","length","Length","size","numel": return "use `x.length` for the length of `x`";
		case "range","xrange": return "use a range such as `[0..n)`, e.g., `for i in [0..n) { … }`";
		case "pow","Pow","power": return "use the operator `^` for exponentiation, e.g., `x^y`";
		case "append","push","push_back","concat","concatenate","extend": return "concatenate vectors or arrays with `~`, e.g., `a ~ b`";
		case "not","Not","NOT": return "use `!a` (or `¬a`) for logical negation";
		case "elif","elsif","elseif": return "use `else if`";
		default: return null;
	}
}

/// name of a visible function that `name` may refer to (e.g., `H` for `h` or `CNOT` for `cx`), with its type if known
string visibleFunction(string name,Scope sc,out ProductTy ft){
	string[] candidates=[name];
	auto similar=similarNames(name,sc);
	if(similar.length==1) candidates~=similar[0];
	if(auto equivalent=silqEquivalent(name,true)) candidates~=equivalent;
	foreach(candidate;candidates){
		auto decl=sc.lookup(new Identifier(candidate),false,true,Lookup.probing,null);
		if(auto fd=cast(FunctionDef)decl){
			ft=fd.ftype;
			return candidate;
		}
		if(auto vd=cast(VarDecl)decl){
			if(auto pt=cast(ProductTy)vd.vtype){
				ft=pt;
				return candidate;
			}
		}
	}
	return null;
}

/// a call of the function `fname` of type `ft` on `arg` of type `argTy`, e.g., `x := H(x)` for `x.H()`
string methodCallSuggestion(string fname,ProductTy ft,string arg,Expression argTy){
	if(!ft||ft.isSquare) return format("%s(%s)",fname,arg); // (unknown or generic function, e.g., `measure`)
	if(!ft.nargs||!isSubtype(argTy,ft.argTy(0))) return null;
	auto pty=ft.argTy(0);
	auto call=ft.nargs==1?format("%s(%s)",fname,arg):format("%s(%s, …)",fname,arg);
	if(ft.nargs==1&&!ft.isConst[0]&&!pty.isClassical()&&ft.cod==pty) return format("%s := %s",arg,call);
	return call;
}

/// the type of the elements of vector or array type `type`
Expression elementType(Expression type){
	if(auto vt=cast(VectorTy)type) return vt.next;
	if(auto at=cast(ArrayTy)type) return at.next;
	return null;
}

/// the arguments of `ce` for the parameters of `ft` (empty if they do not correspond)
Expression[] callArguments(CallExp ce,ProductTy ft){
	if(!ft.isTuple) return [ce.arg];
	auto tpl=cast(TupleExp)ce.arg;
	if(!tpl||tpl.length!=ft.nargs) return null;
	return tpl.e;
}

struct Update{
	string code; // e.g., `x := H(x)`
	string vars; // e.g., "`x`"
	bool opCast(T:bool)(){ return !!code.length; }
}

/// assignment of the result of `ce` to the variables it consumes, e.g., `x := H(x)` (if their types match)
Update updateSuggestion(CallExp ce){
	auto ft=ce.e.type?cast(ProductTy)ce.e.type:null;
	if(!ft||ft.isSquare!=ce.isSquare||!ce.type||isGenerated(ce)) return Update.init;
	auto args=callArguments(ce,ft);
	if(!args.length) return Update.init;
	Expression[] consumed;
	foreach(i,arg;args){
		arg=unwrapImplicitDup(arg);
		if(ft.isConst[i]||!arg.type||arg.type.isClassical()) continue;
		if(!isAssignable(arg)) return Update.init;
		consumed~=arg;
	}
	if(!consumed.length) return Update.init;
	if(consumed.length==1){
		if(ce.type!=consumed[0].type) return Update.init;
	}else{
		auto tt=ce.type.isTupleTy();
		if(!tt||tt.length!=consumed.length||iota(tt.length).any!(i=>tt[i]!=consumed[i].type)) return Update.init;
	}
	auto names=consumed.map!(e=>sourceText(e)).array;
	auto lhs=names.length==1?names[0]:"("~names.join(", ")~")";
	return Update(format("%s := %s",lhs,sourceText(ce)),names.map!(n=>format("`%s`",n)).join(" and "));
}

/// `e` without a `dup` that was inserted by the frontend (e.g., for a component `x[i]` passed to a call statement)
Expression unwrapImplicitDup(Expression e){
	auto ce=cast(CallExp)e;
	if(!ce||!isGenerated(ce)) return e;
	auto callee=ce.e;
	if(auto sce=cast(CallExp)callee) if(sce.isSquare) callee=sce.e;
	if(isPreludeSymbol(cast(Identifier)callee)!="dup") return e;
	return ce.arg;
}

/// source code of `e`, e.g., `(a, b)` for a tuple
string componentsText(Expression e){
	if(auto tpl=cast(TupleExp)e) return "("~tpl.e.map!(e=>sourceText(e)).join(", ")~")";
	return sourceText(e);
}

/// whether `e` is a variable or a component of a variable
bool isAssignable(Expression e){
	e=unwrap(e);
	if(cast(Identifier)e) return true;
	if(auto idx=cast(IndexExp)e) return isAssignable(idx.e);
	return false;
}

/// whether the source code before `loc` is `c`
bool precededBy(Location loc,char c){
	if(!loc.rep.length) return false;
	auto src=Source.get(loc.rep);
	return src&&loc.rep.ptr>src.code.ptr&&loc.rep.ptr[-1]==c;
}

bool[size_t[2]] warnedLocations; // (code may be analyzed repeatedly, e.g., in loops, but each warning is shown once)
bool shouldWarn(Scope sc,Location loc){
	if(sc.handler.suppress||!loc.rep.length) return false;
	size_t[2] key=[cast(size_t)loc.rep.ptr,loc.rep.length];
	if(key in warnedLocations) return false;
	warnedLocations[key]=true;
	return true;
}
