// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.callfailure;
import astopt;

import std.conv, std.format, std.algorithm, std.range, std.array;
import std.uni: isAlphaNum;
import ast.lexer, ast.scope_, ast.expression, ast.type, ast.declaration, ast.conversion, util;
import ast.semantic_: unwrap, calleeFunctionDef, explainAnnotation, isPreludeSymbol;
import ast.modules: isInPrelude;

// diagnostics for calls that do not type check.

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
	sc.error(format("%s takes %s, but %s %s provided",fun,countArguments(expected,ft.isSquare),provided,provided==1?"was":"were"),ce.loc);
	auto decls=parameterDecls(ce.e,ft);
	if(provided<expected){
		foreach(i;provided..expected){
			if(showDecls(decls)) sc.note(format("missing argument for %s",describeParam(ft,decls,i)),decls[i].loc);
			else sc.note(format("missing argument for %s of type `%s`",describeParam(ft,decls,i),ft.argTy(i)),ce.loc);
		}
	}else if(auto tpl=cast(TupleExp)ce.arg){
		foreach(i;expected..min(provided,tpl.length))
			sc.note("extra argument",tpl.e[i].loc);
	}else if(expected==0) sc.note("extra argument",stripParens(ce.arg.loc));
}

/// reports a call of a value that is not a function
void explainNotCallable(CallExp ce,Scope sc){
	sc.error(format("cannot call expression of type `%s`",ce.e.type),ce.loc);
	if(auto id=cast(Identifier)unwrap(ce.e))
		if(id.meaning&&id.meaning.loc.rep.length)
			sc.note(format("`%s` declared here",id),id.meaning.loc);
}

private:

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
	if(r.length<2||!(r[0]=='('&&r[$-1]==')'||r[0]=='['&&r[$-1]==']')) return loc;
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
	if(e&&explainArithmetic(sc,e,to,loc)) return;
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

/// explains common pitfalls with integer arithmetic, e.g., `n/2` or `n-1` passed for a natural number
bool explainArithmetic(Scope sc,Expression e,Expression to,Location loc){
	static NumericType classicalNumericTy(Expression t){ return t&&t.isClassical()?isNumericTy(t):NumericType.none; }
	static bool isNatural(Expression t){ auto n=classicalNumericTy(t); return n==NumericType.Bool||n==NumericType.ℕt; }
	static bool isIntegral(Expression t){ return isNatural(t)||classicalNumericTy(t)==NumericType.ℤt; }
	auto ue=unwrap(e);
	if(auto de=cast(DivExp)ue){
		if(!isIntegral(de.e1.type)||!isIntegral(de.e2.type)) return false;
		auto rty=isNatural(de.e1.type)&&isNatural(de.e2.type)?ℕt(true):ℤt(true);
		if(!isSubtype(rty,to)) return false;
		sc.note(format("`/` is rational division, use `%s div %s` for integer division",operandText(de.e1),operandText(de.e2)),loc);
		return true;
	}
	if(auto se=cast(SubExp)ue){
		if(!isNatural(se.e1.type)||!isNatural(se.e2.type)||!isSubtype(ℕt(true),to)) return false;
		sc.note(format("subtracting natural numbers yields an integer, use `%s sub %s` for natural subtraction (checked to be non-negative)",operandText(se.e1),operandText(se.e2)),loc);
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
