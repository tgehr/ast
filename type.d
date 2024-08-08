// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.type;
import astopt;

static if(language==silq){
	enum Annotation{
		none,
		mfree,
		qfree,
	}
	enum deterministic=Annotation.mfree;
	enum pure_=Annotation.qfree;
}else static if(language==psi){
	enum Annotation{
		none,
		pure_,
	}
	enum deterministic=Annotation.pure_;
	enum pure_=Annotation.pure_;
}

import std.array, std.algorithm, std.conv;
import std.functional, std.range;
import ast.expression, ast.declaration, util;

bool isSameType(Expression lhs,Expression rhs){
	return lhs.eval() == rhs.eval(); // TODO: evaluation context?
}

enum NumericType{
	none,
	Bool,
	ℕt,
	ℤt,
	ℚt,
	ℝ,
	ℂ,
}

NumericType whichNumeric(Expression t){ // TODO: more general solution
	import std.traits: EnumMembers;
	static foreach(type;[EnumMembers!NumericType].filter!(x=>x!=NumericType.none))
		if(mixin(text("cast(",to!string(type).endsWith("t")?to!string(type)[0..$-1]:to!string(type),"Ty)t"))) return type;
	return NumericType.none;
}

bool isNumeric(Expression t){
	return whichNumeric(t)!=NumericType.none;
}

Expression getNumeric(int which,bool classical){
	final switch(which){
		import std.traits: EnumMembers;
		static foreach(type;[EnumMembers!NumericType].filter!(x=>x!=NumericType.none))
			case mixin(text("NumericType.",type)): return mixin(text(type))(classical);
		case NumericType.none: return null;
	}
}

struct FixedIntTy {
	Expression bits;
	bool isSigned, isClassical;

	bool opCast(T: bool)() const pure @safe nothrow {
		return !!bits;
	}
}

FixedIntTy isFixedIntTy(Expression e){
	import ast.semantic_: modules;
	if(preludePath() !in modules) return FixedIntTy();
	auto exprssc=modules[preludePath()];
	auto sc=exprssc[1];

	auto ce=cast(CallExp)e;
	if(!ce || !ce.isSquare) return FixedIntTy();
	auto bits=ce.arg;
	bool isClassical=ce.isClassical_;

	auto id=cast(Identifier)ce.e;
	if(!id||!id.meaning||id.meaning.scope_ !is sc) return FixedIntTy();

	bool isSigned;
	switch(id.name){
		case "int":
			isSigned=true;
			break;
		case "uint":
			isSigned=false;
			break;
		default:
			return FixedIntTy();
	}
	return FixedIntTy(bits, isSigned, isClassical);
}

bool isInt(Expression e){
	if(auto ty=isFixedIntTy(e)) return ty.isSigned;
	else return false;
}
bool isUint(Expression e){
	if(auto ty=isFixedIntTy(e)) return !ty.isSigned;
	else return false;
}

string preludeNumericTypeName(Expression e){
	import ast.semantic_: modules;
	if(preludePath() !in modules) return null;
	auto exprssc=modules[preludePath()];
	auto sc=exprssc[1];
	auto ce=cast(CallExp)e;
	if(!ce || !ce.isSquare) return null;
	auto id=cast(Identifier)ce.e;
	if(!id) return null;
	if(!id.meaning||id.meaning.scope_ !is sc) return null;
	return id.name;
}

bool isFloat(Expression e){ return preludeNumericTypeName(e)=="float"; }
bool isRat(Expression e){ return preludeNumericTypeName(e)=="rat"; }

bool isSubtype(Expression lhs,Expression rhs){
	if(!lhs||!rhs) return false;
	if(lhs is rhs) return true;
	auto l=lhs.eval(), r=rhs.eval();
	if(l.isClassical()&&!r.isClassical()) return isSubtype(l,r.getClassical());
	if(!l.isClassical()&&r.isClassical()) return false;
	auto wl=whichNumeric(l), wr=whichNumeric(r);
	if(wl==NumericType.none||wr==NumericType.none) return l.isSubtypeImpl(r);
	return wl<=wr;
}

Expression combineTypes(Expression lhs,Expression rhs,bool meet,bool allowQNumeric=false){ // TODO: more general solution // TODO: ⊤/⊥?
	if(!lhs) return rhs;
	if(!rhs) return lhs;
	if(lhs == rhs) return lhs;
	auto l=lhs.eval(), r=rhs.eval();
	auto wl=whichNumeric(l), wr=whichNumeric(r);
	if(wl==NumericType.none&&wr==NumericType.none) return l.combineTypesImpl(r,meet);
	if(wl==NumericType.none||wr==NumericType.none) return null;
	auto result=getNumeric(meet?min(wl,wr):max(wl,wr),meet?lhs.isClassical()||rhs.isClassical():lhs.isClassical()&&rhs.isClassical());
	if(!allowQNumeric&&isQNumeric(result)) return null;
	return result;
}

Expression joinTypes(Expression lhs,Expression rhs){
	return combineTypes(lhs,rhs,false);
}
Expression meetTypes(Expression lhs,Expression rhs){
	return combineTypes(lhs,rhs,true);
}

abstract class Type: Expression{
	this(){ if(!this.type) this.type=typeTy; sstate=SemState.completed; }
	override @property string kind(){ return "type"; }
	override string toString(){ return "T"; }
	abstract override bool opEquals(Object r);
	override Annotation getAnnotation(){ return pure_; }
}

class ErrorTy: Type{
	this(){}//{sstate = SemState.error;}
	override ErrorTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){return "__error";}
	mixin VariableFree;
}

class BoolTy: Type{
	private bool classical;
	private this(bool classical){
		this.classical=classical;
		this.type=typeOfBoolTy(classical);
		super();
	}
	override BoolTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!𝔹":"𝔹";
		else return "𝔹";
	}
	override bool opEquals(Object o){
		auto r=cast(BoolTy)o;
		return r && classical==r.classical;
	}
	override BoolTy getClassical(){
		return Bool(true);
	}
	override BoolTy getQuantum(){
		return Bool(false);
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}
static if(language==silq) private BoolTy[2] theBool;
else private BoolTy theBool;

BoolTy Bool(bool classical=true){
	static if(language==silq) return theBool[classical]?theBool[classical]:(theBool[classical]=new BoolTy(classical));
	else return theBool?theBool:(theBool=new BoolTy(true));
}

class ℕTy: Type{
	static if(language==silq) private bool classical;
	else private enum classical=true;
	private this(bool classical){
		static if(language==silq) this.classical=classical;
		this.type=typeOfNumericTy(classical);
		super();
	}
	override ℕTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!ℕ":"ℕ";
		else return "ℕ";
	}
	override bool opEquals(Object o){
		auto r=cast(ℕTy)o;
		return r&&classical==r.classical;
	}
	override ℕTy getClassical(){
		return ℕt(true);
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}
static if(language==silq) private ℕTy[2] theℕ;
else private ℕTy theℕ;

ℕTy ℕt(bool classical=true){
	static if(language==silq) return theℕ[classical]?theℕ[classical]:(theℕ[classical]=new ℕTy(classical));
	else return theℕ?theℕ:(theℕ=new ℕTy(true));
}

class ℤTy: Type{
	static if(language==silq) private bool classical;
	else private enum classical=true;
	private this(bool classical){
		static if(language==silq) this.classical=classical;
		this.type=typeOfNumericTy(classical);
		super();
	}
	override ℤTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!ℤ":"ℤ";
		else return "ℤ";
	}
	override bool opEquals(Object o){
		auto r=cast(ℤTy)o;
		return r&&classical==r.classical;
	}
	override ℤTy getClassical(){
		return ℤt(true);
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}
static if(language==silq) private ℤTy[2] theℤ;
else private ℤTy theℤ;

ℤTy ℤt(bool classical=true){
	static if(language==silq) return theℤ[classical]?theℤ[classical]:(theℤ[classical]=new ℤTy(classical));
	else return theℤ?theℤ:(theℤ=new ℤTy(true));
}

class ℚTy: Type{
	static if(language==silq) private bool classical;
	else private enum classical=true;
	private this(bool classical){
		static if(language==silq) this.classical=classical;
		this.type=typeOfNumericTy(classical);
		super();
	}
	override ℚTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!ℚ":"ℚ";
		else return "ℚ";
	}
	override bool opEquals(Object o){
		auto r=cast(ℚTy)o;
		return r&&classical==r.classical;
	}
	override ℚTy getClassical(){
		return ℚt(true);
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}
static if(language==silq) private ℚTy[2] theℚ;
else private ℚTy theℚ;

ℚTy ℚt(bool classical=true){
	static if(language==silq) return theℚ[classical]?theℚ[classical]:(theℚ[classical]=new ℚTy(classical));
	else return theℚ?theℚ:(theℚ=new ℚTy(true));
}

class ℝTy: Type{
	static if(language==silq) private bool classical;
	else private enum classical=true;
	private this(bool classical){
		static if(language==silq) this.classical=classical;
		this.type=typeOfNumericTy(classical);
		super();
	}
	override ℝTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!ℝ":"ℝ";
		else return "ℝ";
	}
	override bool opEquals(Object o){
		auto r=cast(ℝTy)o;
		return r&&classical==r.classical;
	}
	override ℝTy getClassical(){
		return ℝ(true);
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}
static if(language==silq) private ℝTy[2] theℝ;
else private ℝTy theℝ;

ℝTy ℝ(bool classical=true){
	static if(language==silq) return theℝ[classical]?theℝ[classical]:(theℝ[classical]=new ℝTy(classical));
	else return theℝ?theℝ:(theℝ=new ℝTy(true));
}

class ℂTy: Type{
	static if(language==silq) private bool classical;
	else private enum classical=true;
	private this(bool classical){
		static if(language==silq) this.classical=classical;
		this.type=typeOfNumericTy(classical);
		super();
	}
	override ℂTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!ℂ":"ℂ";
		else return "ℂ";
	}
	override bool opEquals(Object o){
		auto r=cast(ℂTy)o;
		return r&&classical==r.classical;
	}
	override ℂTy getClassical(){
		return ℂ(true);
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}
static if(language==silq) private ℂTy[2] theℂ;
else private ℂTy theℂ;

ℂTy ℂ(bool classical=true){
	static if(language==silq) return theℂ[classical]?theℂ[classical]:(theℂ[classical]=new ℂTy(classical));
	else return theℂ?theℂ:(theℂ=new ℂTy(true));
}



class AggregateTy: Type{
	DatDecl decl;
	static if(language==silq){
		bool classical;
		private AggregateTy classicalTy;
		private AggregateTy quantumTy;
	}else enum classical=true;
	this(DatDecl decl,bool classical,AggregateTy classicalTy=null,AggregateTy quantumTy=null){
		if(!classical) assert(decl.isQuantum);
		this.decl=decl;
		static if(language==silq){
			this.classical=classical;
			if(classical) this.classicalTy=this;
			else this.classicalTy=classicalTy?classicalTy:New!AggregateTy(decl,true,null,decl.isQuantum?this:null);
			if(decl.isQuantum){
				if(!classical) this.quantumTy=this;
				else this.quantumTy=quantumTy?quantumTy:New!AggregateTy(decl,false,this,null);
			}
		}
	}
	override AggregateTy copyImpl(CopyArgs args){
		return this;
	}
	override bool opEquals(Object o){
		if(auto r=cast(AggregateTy)o)
			return decl is r.decl && classical==r.classical;
		return false;
	}
	override string toString(){
		return decl&&decl.name?decl.name.name:"<anonymous aggregate>";
	}
	override AggregateTy getClassical(){
		static if(language==silq) return classicalTy;
		else return this;
	}
	override AggregateTy getQuantum(){
		static if(language==silq) return quantumTy;
		else return this;
	}

	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) e){
		return 0;
	}
}

class ContextTy: Type{
	static if(language==silq) private bool classical;
	else private enum classical=true;
	private this(bool classical){
		static if(language==silq) this.classical=classical;
	}
	override ContextTy copyImpl(CopyArgs args){
		return this;
	}
	override bool opEquals(Object o){
		auto ctx=cast(ContextTy)o;
		return ctx&&ctx.classical==classical;
	}
	override string toString(){
		static if(language==silq) return (classical?"!":"")~"`Ctx";
		else return "`Ctx";
	}
	override ContextTy getClassical(){
		return contextTy(true);
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) e){
		return 0;
	}
}
static if(language==silq) private ContextTy[2] theContextTy;
else private ContextTy theContextTy;
ContextTy contextTy(bool classical=true){
	static if(language==silq) return theContextTy[classical]?theContextTy[classical]:(theContextTy[classical]=new ContextTy(classical));
	else return theContextTy?theContextTy:(theContextTy=new ContextTy(true));
}

interface ITupleTy{
	@property size_t length();
	Expression opIndex(size_t i);
	Expression opSlice(size_t l,size_t r);
}

class TupleTy: Type,ITupleTy{
	Expression[] types;
	override ITupleTy isTupleTy(){ return this; }
	@property size_t length(){ return types.length; }
	Expression opIndex(size_t i){ return types[i]; }
	Expression opSlice(size_t l,size_t r){ return tupleTy(types[l..r]); }
	private this(Expression[] types)in{
		assert(types.all!(e=>isType(e)||isQNumeric(e)));
		assert(!types.length||!types[1..$].all!(x=>x==types[0]));
	}do{
		this.types=types;
		this.type=typeOfTupleTy(types);
		super();
	}
	override TupleTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		if(!types.length) return "𝟙";
		if(types.length==1) return "("~types[0].toString()~")¹";
		string addp(Expression a){
			if(cast(FunTy)a) return "("~a.toString()~")";
			return a.toString();
		}
		return types.map!(a=>a.isTupleTy()&&a!is unit?"("~a.toString()~")":addp(a)).join(" × ");
	}
	override int freeVarsImpl(scope int delegate(Identifier) dg){
		foreach(t;types)
			if(auto r=t.freeVarsImpl(dg))
				return r;
		return 0;
	}
	override Type substituteImpl(Expression[string] subst){
		auto ntypes=types.dup;
		foreach(ref t;ntypes) t=t.substitute(subst);
		return tupleTy(ntypes);
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto tt=rhs.isTupleTy();
		if(!tt||types.length!=tt.length) return false;
		return all!(i=>types[i].unify(tt[i],subst,meet))(iota(types.length));

	}
	override bool opEquals(Object o){
		if(auto r=cast(TupleTy)o)
			return types==r.types;
		return false;
	}
	override bool isSubtypeImpl(Expression r){
		auto ltup=this,rtup=r.isTupleTy();
		if(rtup&&ltup.types.length==rtup.length)
			return all!(i=>isSubtype(ltup.types[i],rtup[i]))(iota(ltup.types.length));
		auto rarr=cast(ArrayTy)r;
		if(rarr) return all!(i=>isSubtype(ltup.types[i],rarr.next))(iota(ltup.types.length));
		return false;
	}
	override Expression combineTypesImpl(Expression r,bool meet){
		auto ltup=this,rtup=r.isTupleTy();
		if(rtup&&ltup.types.length==rtup.length){
			auto rtypes=zip(ltup.types,iota(rtup.length).map!(i=>rtup[i])).map!((t)=>combineTypes(t.expand,meet)).array;
			if(all!(x=>x !is null)(rtypes)) return tupleTy(rtypes);
		}
		auto rarr=cast(ArrayTy)r;
		if(!rarr&&!meet){
			if(auto rvec=cast(VectorTy)r)
				rarr=arrayTy(rvec.next);
		}
		if(rarr){
			if(meet){
				auto rtypes=zip(ltup.types,iota(length).map!(i=>rarr.next)).map!((t)=>combineTypes(t.expand,meet)).array;
				if(all!(x=>x !is null)(rtypes)) return tupleTy(rtypes);
			}else{
				auto rtype=ltup.types.fold!((a,b)=>combineTypes(a,b,meet))(rarr.next);
				if(rtype) return arrayTy(rtype);
			}
		}
		return null;
	}
	override Expression getClassical(){
		auto ntypes=types.map!(x=>x.getClassical()).array;
		if(all!(x=>x !is null)(ntypes)) return tupleTy(ntypes);
		return null;
	}
	override Expression getQuantum(){
		auto ntypes=types.map!(x=>x.getQuantum()).array;
		if(all!(x=>x !is null)(ntypes)) return tupleTy(ntypes);
		return null;
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		foreach(x;types) if(auto r=dg(x)) return r;
		return 0;
	}
	override Expression evalImpl(Expression ntype){
		assert(isTypeTy(ntype));
		auto ntypes=types.map!(t=>t.eval()).array;
		if(ntypes==types) return this;
		return tupleTy(ntypes);
	}
}

Type unit(){ return tupleTy([]); }

Type tupleTy(Expression[] types)in{
	assert(types.all!(e=>isType(e)||isQNumeric(e)));
}do{
	import ast.lexer: Token,Tok;
	if(types.length&&types.all!(x=>x==types[0])){
		auto len=LiteralExp.makeInteger(types.length);
		return vectorTy(types[0],len);
	}
	return memoize!((Expression[] types)=>new TupleTy(types))(types);
}

size_t numComponents(Expression t){
	if(auto tpl=t.isTupleTy())
		return tpl.length;
	return 1;
}

class ArrayTy: Type{
	Expression next;
	private this(Expression next)in{
		assert(isType(next)||isQNumeric(next));
	}do{
		this.next=next;
		this.type=typeOfArrayTy(next);
		super();
	}
	override ArrayTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		bool p=cast(FunTy)next||next.isTupleTy()&&next!is unit;
		return p?"("~next.toString()~")[]":next.toString()~"[]";
	}
	override int freeVarsImpl(scope int delegate(Identifier) dg){
		return next.freeVarsImpl(dg);
	}
	override ArrayTy substituteImpl(Expression[string] subst){
		return arrayTy(next.substitute(subst));
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		if(auto vt=cast(VectorTy)rhs)
			return next.unifyImpl(vt.next,subst,meet);
		if(auto tt=cast(TupleTy)rhs)
			return tt.types.all!(ty=>next.unifyImpl(ty,subst,meet));
		if(auto at=cast(ArrayTy)rhs)
			return next.unifyImpl(at.next,subst,meet);
		return false;
	}
	override ArrayTy evalImpl(Expression ntype){
		assert(isTypeTy(ntype));
		return arrayTy(next.eval());
	}
	override bool opEquals(Object o){
		if(auto r=cast(ArrayTy)o)
			return next==r.next;
		return false;
	}
	override bool isSubtypeImpl(Expression r){
		auto larr=this,rarr=cast(ArrayTy)r;
		if(!rarr) return false;
		return isSubtype(larr.next,rarr.next);
	}
	override Expression combineTypesImpl(Expression r,bool meet){
		auto larr=this,rarr=cast(ArrayTy)r;
		if(rarr){
			auto combinedNext=combineTypes(larr.next,rarr.next,meet);
			if(combinedNext) return arrayTy(combinedNext);
		}
		if(auto rvec=cast(VectorTy)r){
			auto nnext=combineTypes(next,rvec.next,meet);
			if(nnext){
				if(meet) return vectorTy(nnext,rvec.num);
				else return arrayTy(nnext);
			}
		}
		if(auto rtup=r.isTupleTy()){
			if(meet){
				auto ntypes=iota(rtup.length).map!(i=>combineTypes(next,rtup[i],meet)).array;
				if(all!(x=>x is null)(ntypes)) return tupleTy(ntypes);
			}else{
				auto rtype=iota(rtup.length).map!(i=>rtup[i]).fold!((a,b)=>combineTypes(a,b,meet))(next);
				if(rtype) return arrayTy(rtype);
			}
		}
		return null;
	}
	override Expression getClassical(){
		auto nnext=next.getClassical();
		if(!nnext) return null;
		return arrayTy(nnext);
	}
	override Expression getQuantum(){
		auto nnext=next.getQuantum();
		if(!nnext) return null;
		return arrayTy(nnext);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(next);
	}
}

ArrayTy arrayTy(Expression next)in{
	assert(isType(next)||isQNumeric(next));
}do{
	return memoize!((Expression next)=>new ArrayTy(next))(next);
}

class VectorTy: Type, ITupleTy{
	Expression next,num;
	override ITupleTy isTupleTy(){
		if(cast(LiteralExp)num) return this;
		return null;
	}
	override VectorTy copyImpl(CopyArgs args){
		return this;
	}
	@property size_t length(){
		auto lit=cast(LiteralExp)num;
		assert(!!lit);
		return to!size_t(lit.lit.str); // TODO: avoid crash if length is too big
	}
	Expression opIndex(size_t i){ return next; }
	Expression opSlice(size_t l,size_t r){
		assert(0<=l&&l<=r&&r<=length);
		auto len=LiteralExp.makeInteger(r-l);
		return vectorTy(next,len);
	}
	private this(Expression next,Expression num)in{
		assert(isType(next)||isQNumeric(next));
		assert(isSubtype(num.type,ℕt(true)));
	}do{
		this.next=next;
		this.num=num;
		this.type=typeOfVectorTy(next,num);
		super();
	}
	override string toString(){
		bool p=cast(FunTy)next||next.isTupleTy&&next!is unit;
		bool q=!cast(Identifier)num&&!cast(LiteralExp)num; // TODO: improve
		return (p?"("~next.toString()~")^":next.toString()~"^")~(q?"("~num.toString()~")":num.toString());
	}
	override int freeVarsImpl(scope int delegate(Identifier) dg){
		if(auto r=next.freeVarsImpl(dg)) return r;
		return num.freeVarsImpl(dg);
	}
	override VectorTy substituteImpl(Expression[string] subst){
		return vectorTy(next.substitute(subst),num.substitute(subst));
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		if(auto tt=cast(TupleTy)rhs)
			return tt.types.all!(ty=>next.unifyImpl(ty,subst,meet)) && num.unifyImpl(LiteralExp.makeInteger(tt.length),subst,meet);
		if(auto vt=cast(VectorTy)rhs)
			return next.unifyImpl(vt.next,subst,meet) && num.unifyImpl(vt.num,subst,meet);
		return false;
	}
	override VectorTy evalImpl(Expression ntype){
		assert(isTypeTy(ntype));
		return vectorTy(next.eval(),num.eval());
	}
	override bool opEquals(Object o){
		if(auto r=cast(VectorTy)o)
			return next==r.next&&num==r.num;
		return false;
	}
	override bool isSubtypeImpl(Expression r){
		if(auto rarr=cast(ArrayTy)r) return isSubtype(next,rarr.next);
		auto lvec=this,rvec=cast(VectorTy)r;
		if(rvec) return isSubtype(lvec.next,rvec.next) && num==rvec.num;
		auto ltup=this.isTupleTy(),rtup=r.isTupleTy();
		if(ltup&&rtup&&ltup.length==rtup.length)
			return all!(i=>isSubtype(ltup[i],rtup[i]))(iota(ltup.length));
		return false;
	}
	override Expression combineTypesImpl(Expression r,bool meet){
		if(auto rarr=cast(ArrayTy)r){
			auto nnext=combineTypes(next,rarr.next,meet);
			if(nnext){
				if(meet) return vectorTy(nnext,num);
				else return arrayTy(nnext);
			}
		}
		auto lvec=this,rvec=cast(VectorTy)r;
		if(rvec){
			auto nnext=combineTypes(lvec.next,rvec.next,meet);
			if(!nnext) return null;
			if(num==rvec.num){
				return vectorTy(nnext,num);
			}else if(!meet){
				return arrayTy(nnext);
			}else return null;
		}
		auto ltup=this.isTupleTy(),rtup=r.isTupleTy();
		if(rtup){
			bool equal=false;
			if(ltup) equal=ltup.length==rtup.length;
			else equal=num==LiteralExp.makeInteger(rtup.length);
			if(equal){
				auto rtypes=iota(rtup.length).map!(i=>combineTypes(next,rtup[i],meet)).array;
				if(all!(x=>x !is null)(rtypes)) return tupleTy(rtypes);
			}else if(!meet){
				auto nnext=iota(rtup.length).map!(i=>rtup[i]).fold!((a,b)=>combineTypes(a,b,meet))(next);
				if(nnext) return arrayTy(nnext);
			}else return null;
		}
		return null;
	}
	override Expression getClassical(){
		auto nnext=next.getClassical();
		if(!nnext) return null;
		return vectorTy(nnext,num);
	}
	override Expression getQuantum(){
		auto nnext=next.getQuantum();
		if(!nnext) return null;
		return vectorTy(nnext,num);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(next)) return r;
		return dg(num);
	}
}

VectorTy vectorTy(Expression next,Expression num)in{
	assert(isType(next)||isQNumeric(next));
	assert(num&&isSubtype(num.type,ℕt(true)));
}do{
	return memoize!((Expression next,Expression num)=>new VectorTy(next,num))(next,num);
}

static Expression elementType(Expression ty){
	if(auto at=cast(ArrayTy)ty) return at.next;
	if(auto vt=cast(VectorTy)ty) return vt.next;
	return null;
}

class StringTy: Type{
	static if(language==silq) bool classical;
	else enum classical=true;
	private this(bool classical){
		this.type=typeOfStringTy(classical);
	}
	override StringTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!string":"string";
		else return "string";
	}
	override bool opEquals(Object o){
		return !!cast(StringTy)o;
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}

StringTy stringTy(bool classical=true){
	static if(language==silq) return memoize!((bool classical)=>new StringTy(classical))(classical);
	else return memoize!(()=>new StringTy(true));
}

string annotationToString(Annotation annotation){
	static if(language==silq) return annotation?text(annotation):"";
	static if(language==psi){
		final switch(annotation){
			case Annotation.none: return "";
			case Annotation.pure_: return "pure";
		}
	}
}

class RawProductTy: Expression{
	Parameter[] params;
	Expression cod;
	bool isSquare,isTuple;
	Annotation annotation;
	this(Parameter[] params,Expression cod,bool isSquare,bool isTuple,Annotation annotation){
		this.params=params; this.cod=cod;
		this.isSquare=isSquare; this.isTuple=isTuple;
		this.annotation=annotation;
	}
	override RawProductTy copyImpl(CopyArgs args){
		return new RawProductTy(params.map!(p=>p.copy(args)).array,cod.copy(args),isSquare,isTuple,annotation);
	}
	override string toString(){
		return "<unanalyzed Π type>"; // TODO: format nicely.
	}

	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}

class ProductTy: Type{
	bool[] isConst;
	string[] names;
	Expression dom, cod;
	bool isSquare,isTuple;
	Annotation annotation;
	static if(language==silq){
		private ProductTy classicalTy;
		bool isClassical_;
	}else enum isClassical_=true;
	private this(bool[] isConst,string[] names,Expression dom,Expression cod,bool isSquare,bool isTuple,Annotation annotation,bool isClassical_)in{
		// TODO: assert that all names are distinct
		if(isTuple){
			auto tdom=dom.isTupleTy;
			assert(!!tdom);
			assert(names.length==tdom.length);
			assert(isConst.length==tdom.length);
		}else{
			assert(names.length==1);
			assert(isConst.length==1);
		}
		assert(isType(cod)||isQNumeric(cod),text(cod));
	}do{
		this.isConst=isConst; // TODO: don't track this in PSI
		this.names=names; this.dom=dom;
		this.isSquare=isSquare; this.isTuple=isTuple;
		Expression[string] subst;
		foreach(i;0..names.length)
			if(names[i]!="")
				subst[names[i]]=varTy(names[i],argTy(i));
		assert(!cod.hasFreeVar(""));
		cod=cod.substitute(subst); // TODO: only do this if necessary?
		this.cod=cod;
		this.annotation=annotation;
		this.type=typeOfProductTy(isConst,names,dom,cod,isSquare,isTuple,annotation,isClassical_);
		super();
		static if(language==silq){
			this.isClassical_=isClassical_;
			if(isClassical_) classicalTy=this;
			else classicalTy=new ProductTy(isConst,names,dom,cod,isSquare,isTuple,annotation,true);
		}
		assert(isClassical(this)==this.isClassical_);
		// TODO: report DMD bug, New!ProductTy does not work
	}
	override ProductTy copyImpl(CopyArgs args){
		return this;
	}
	/+private+/ @property ITupleTy tdom()in{ // TODO: make private
		assert(isTuple);
	}do{
		auto r=dom.isTupleTy;
		assert(!!r);
		return r;
	}
	override string toString(){
		auto c=cod.toString();
		auto del=isSquare?"[]":"()";
		string getParamKind(bool const_){
			string paramKind=null;
			static if(language==silq){
				if(const_&&!isSquare) paramKind="const ";
				if(!const_&&isSquare) paramKind="moved ";
			}
			return paramKind;
		}
		string r;
		if(!cod.hasAnyFreeVar(names)){
			string d;
			string addp(bool const_,Expression a,string del="()"){
				auto paramKind=getParamKind(const_);
				if(cast(FunTy)a) return del[0]~(paramKind?paramKind~"(":"")~a.toString()~(paramKind?")":"")~del[1];
				if(a.isTupleTy()) return (paramKind?paramKind~"(":"")~a.toString()~(paramKind?")":"");
				return paramKind~a.toString();
			}
			if(isSquare&&all(isConst)||!isSquare&&all!(x=>!x)(isConst)){
				d=dom.toString();
			}else if(auto tpl=dom.isTupleTy()){
				if(isTuple){
					assert(!!tpl.length);
					auto paramKind=getParamKind(isConst[0]);
					if(tpl.length!=1){
						assert(tpl.length==isConst.length);
						d=zip(isConst,iota(tpl.length).map!(i=>tpl[i])).map!((a){
							auto paramKind=getParamKind(a[0]);
							return (a[1].isTupleTy()&&a[1]!is unit?"("~paramKind~a[1].toString()~")":addp(a[0],a[1]));
						}).join(" × ");
					}else d="("~paramKind~tpl[0].toString()~")¹";
				}else d=addp(isConst[0],dom,del);
			}else d=addp(isConst[0],dom,del);
			static if(language==silq) auto arrow=(isClassical_?"!":"")~"→";
			else enum arrow="→";
			if(isSquare) d=del[0]~d~del[1];
			r=d~" "~arrow~(annotation?annotationToString(annotation):"")~" "~c;
		}else{
			assert(names.length);
			string args;
			if(isTuple){
				args=zip(isConst,names,iota(tdom.length).map!((i)=>tdom[i])).map!((x){
					auto paramKind=getParamKind(x[0]);
					return paramKind~x[1]~":"~x[2].toString();
				}).join(",");
				if(nargs==1) args~=",";
			}else{
				auto paramKind=getParamKind(isConst[0]);
				args=paramKind~names[0]~":"~dom.toString();
			}
			static if(language==silq) auto pi=(isClassical_?"!":"")~"∏";
			else enum pi="Π";
			r=pi~del[0]~args~del[1]~annotationToString(annotation)~". "~c;
		}
		return r;
	}
	@property size_t nargs(){
		if(isTuple) return tdom.length;
		return 1;
	}
	Expression argTy(size_t i)in{assert(i<nargs);}do{
		if(isTuple) return tdom[i];
		return dom;
	}
	override int freeVarsImpl(scope int delegate(Identifier) dg){
		if(auto r=dom.freeVarsImpl(dg)) return r;
		return cod.freeVarsImpl(v=>names.canFind(v.name)?0:dg(v));
	}
	private ProductTy relabel(string oname,string nname)in{
		assert(names.canFind(oname));
		assert(!hasFreeVar(nname));
		assert(!names.canFind(nname));
	}out(r){
		if(oname!=""&&oname!=nname){
			assert(r.names.canFind(nname));
			assert(!r.names.canFind(oname));
		}
	}do{
		if(oname==""||oname==nname) return this;
		import std.algorithm;
		auto i=names.countUntil(oname);
		assert(i!=-1);
		auto nnames=names.dup;
		nnames[i]=nname;
		auto nvar=varTy(nname,argTy(i));
		return productTy(isConst,nnames,dom,cod.substitute(oname,nvar),isSquare,isTuple,annotation,isClassical_);
	}
	private ProductTy relabelAway(string oname)in{
		assert(names.canFind(oname));
	}out(r){
		if(oname!="") assert(!r.names.canFind(oname));
	}do{
		if(oname=="") return this;
		auto nname=oname;
		while(names.canFind(nname)||hasFreeVar(nname)) nname~="'";
		return relabel(oname,nname);
	}
	private string freshName(string base,Expression block){
		auto nn=base;
		while(hasFreeVar(nn)||block.hasFreeVar(nn)) nn~="'";
		return nn;
	}
	string[] freshNames(Expression block){
		auto nnames=names.dup;
		foreach(i,ref nn;nnames){
			if(nn=="") nn="x";
			while(hasFreeVar(nn)||block.hasFreeVar(nn)||nnames[0..i].canFind(nn)) nn~="'";
		}
		return nnames;
	}
	ProductTy relabelAll(string[] nnames)out(r){
		assert(nnames.length==names.length);
		foreach(n;nnames) assert(!hasFreeVar(n));
	}do{
		if(nnames==names) return this;
		Expression[string] subst;
		foreach(i;0..names.length) subst[names[i]]=varTy(nnames[i],argTy(i));
		return productTy(isConst,nnames,dom,cod.substitute(subst),isSquare,isTuple,annotation,isClassical_);
	}
	override ProductTy substituteImpl(Expression[string] subst){
		foreach(n;names){
			if(n=="") continue;
			bool ok=true;
			foreach(k,v;subst) if(v.hasFreeVar(n)) ok=false;
			if(ok) continue;
			auto r=cast(ProductTy)relabelAway(n).substitute(subst);
			assert(!!r);
			return r;
		}
		auto ndom=dom.substitute(subst);
		auto nsubst=subst.dup;
		foreach(n;names) nsubst.remove(n);
		auto ncod=cod.substitute(nsubst);
		return productTy(isConst,names,ndom,ncod,isSquare,isTuple,annotation,isClassical_);
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto r=cast(ProductTy)rhs; // TODO: get rid of duplication (same code in opEquals)
		if(!r) return false;
		if(isTuple&&!r.dom.isTupleTy()) return false;
		r=r.setTuple(isTuple);
		if(!r) return false;
		if(isConst.length!=r.isConst.length) return false;
		if(isSquare!=r.isSquare||annotation>r.annotation||
		   isClassical_!=r.isClassical_||nargs!=r.nargs)
			return false;
		if(names.any!(name=>r.hasFreeVar(name)))
			return false;
		if(r.names.any!(name=>hasFreeVar(name)))
			return false;
		r=r.relabelAll(iota(names.length).map!(i=>names[i]!=""?names[i]:r.names[i]).array);
		Expression[string] nsubst;
		foreach(k,v;subst) if(!names.canFind(k)) nsubst[k]=v;
		auto res=dom.unify(r.dom,nsubst,!meet)&&cod.unify(r.cod,nsubst,meet);
		foreach(k,v;nsubst) subst[k]=v;
		return res;
	}
	Expression tryMatch(Expression arg,out Expression garg)in{assert(isSquare&&cast(ProductTy)cod);}do{
		auto cod=cast(ProductTy)this.cod;
		assert(!!cod);
		auto nnames=freshNames(arg);
		if(nnames!=names) return relabelAll(nnames).tryMatch(arg,garg);
		Expression[] atys;
		auto tpl=arg.type.isTupleTy();
		if(cod.isTuple&&tpl){
			atys=iota(tpl.length).map!(i=>tpl[i]).array;
			if(atys.length!=cod.nargs) return null;
		}else atys=[arg.type];
		Expression[string] subst;
		foreach(i,n;names) subst[n]=null;
		foreach(i,aty;atys){
			if(i>=cod.nargs) continue;
			if(!cod.argTy(i).unify(aty,subst,false))
				return null;
		}
		auto gargs=new Expression[](names.length);
		foreach(i,n;names){
			if(!subst[n]) return null;
			gargs[i]=subst[n];
		}
		if(!isTuple) assert(gargs.length==1);
		if(isTuple){
			auto tgarg=new TupleExp(gargs);
			tgarg.type=tupleTy(gargs.map!(garg=>garg.type).array);
			tgarg.sstate=SemState.completed;
			garg=tgarg;
		}else garg=gargs[0];
		cod=cast(ProductTy)tryApply(garg,true);
		if(!cod) return null;
		return cod.tryApply(arg,false);
	}
	Expression tryApply(Expression arg,bool isSquare){
		if(isSquare != this.isSquare) return null;
		if(!isSubtype(arg.type,dom)) return null;
		Expression[string] subst;
		if(isTuple){
			auto targTy=arg.type.isTupleTy();
			assert(!!tdom);
			foreach(i,n;names){
				auto exp=new IndexExp(arg,LiteralExp.makeInteger(i));
				exp.type=targTy[i];
				exp.sstate=SemState.completed;
				subst[n]=exp.eval();
			}
		}else{
			assert(names.length==1);
			subst[names[0]]=arg;
		}
		return cod.substitute(subst);
	}
	override bool opEquals(Object o){
		auto r=cast(ProductTy)o;
		if(!r) return false;
		if(isTuple&&!r.dom.isTupleTy()) return false;
		r=r.setTuple(isTuple);
		if(!r) return false;
		assert(isTuple==r.isTuple);
		if(isConst!=r.isConst||isSquare!=r.isSquare||annotation!=r.annotation||
		   isClassical_!=r.isClassical_||nargs!=r.nargs)
			return false;
		return this.isSubtypeImpl(r)&&r.isSubtypeImpl(this);
	}
	auto isConstForReverse(){
		return iota(nargs).map!(i=>isConst[i]||argTy(i).isClassical&&!argTy(i).isQuantum);
	}
	auto isConstForSubtyping(){
		return iota(nargs).map!(i=>isConst[i]||argTy(i).isClassical);
	}
	override bool isSubtypeImpl(Expression rhs){
		auto r=cast(ProductTy)rhs;
		if(!r) return false;
		if(isTuple&&!r.dom.isTupleTy()) return false;
		r=r.setTuple(isTuple);
		if(!r) return false;
		if(!equal(this.isConstForSubtyping,r.isConstForSubtyping)||isSquare!=r.isSquare||nargs!=r.nargs)
			return false;
		if(annotation<r.annotation||!isClassical_&&r.isClassical_)
			return false;
		auto name=freshName("x",r);
		auto vars=varTy(name,r.dom);
		auto lCod=tryApply(vars,isSquare);
		auto rCod=r.tryApply(vars,isSquare);
		if(!lCod) return false;
		assert(!!rCod);
		return isSubtype(lCod,rCod);
	}
	override Expression combineTypesImpl(Expression rhs,bool meet){
		auto r=cast(ProductTy)rhs;
		if(!r) return null;
		auto nannotation=meet?min(annotation,r.annotation):max(annotation,r.annotation);
		auto nisClassical=meet?isClassical_||r.isClassical_:isClassical_&&r.isClassical_;
		auto ndom=combineTypes(dom,r.dom,!meet);
		if(!ndom) return null;
		auto tpl=isTuple?ndom.isTupleTy():null;
		if(isTuple!=r.isTuple||isTuple&&!tpl||isTuple&&names!=r.names){
			auto nl=setTuple(false);
			auto nr=r.setTuple(false);
			if(!nl||!nr) return null;
			return combineTypes(nl,nr,meet);
		}
		if(!equal(isConstForSubtyping,r.isConstForSubtyping)||isSquare!=r.isSquare||nargs!=r.nargs)
			return null;
		auto nIsConst=isConst==r.isConst?isConst:zip(isConst,r.isConst).map!(x=>x[0]&&x[1]).array;
		if(isTuple){
			assert(names==r.names);
			assert(!!tpl);
			if(tpl.length!=names.length) return null;
			auto vars=new TupleExp(iota(names.length).map!(i=>cast(Expression)varTy(names[i],tpl[i])).array);
			vars.type=ndom;
			vars.sstate=SemState.completed;
			auto lCod=tryApply(vars,isSquare);
			auto rCod=r.tryApply(vars,isSquare);
			assert(lCod&&rCod);
			auto ncod=combineTypes(lCod,rCod,meet);
			if(!ncod) return null;
			return productTy(nIsConst,names,ndom,ncod,isSquare,isTuple,nannotation,nisClassical);
		}else{
			auto name=names[0]==r.names[0]?names[0]:freshName("x",r);
			auto var=varTy(name,ndom);
			auto lCod=tryApply(var,isSquare);
			auto rCod=r.tryApply(var,isSquare);
			assert(lCod&&rCod);
			auto ncod=combineTypes(lCod,rCod,meet);
			if(!ncod) return null;
			return productTy(nIsConst,names,ndom,ncod,isSquare,isTuple,nannotation,nisClassical);
		}
	}
	final ProductTy setAnnotation(Annotation annotation){
		return productTy(isConst,names,dom,cod,isSquare,isTuple,annotation,isClassical_);
	}
	ProductTy setTuple(bool tuple)in{
		assert(!tuple||dom.isTupleTy());
	}do{
		if(tuple==isTuple) return this;
		string[] nnames;
		bool[] nIsConst;
		if(tuple){
			auto tpl=dom.isTupleTy();
			assert(!!tpl);
			assert(!isTuple&&names.length==1);
			nnames=iota(tpl.length).map!(i=>names[0]~lowNum(i)).array;
			assert(isConst.length==1);
			nIsConst=isConst[0].repeat(tpl.length).array;
		}else{
			if(!isConst.empty&&!isConst.all!(x=>x==isConst.front))
				return null;
			nnames=["t"];
			nIsConst=[isConst.empty?false:isConst.front];
		}
		foreach(i,ref nn;nnames) while(hasFreeVar(nn)) nn~="'";
		Expression narg;
		if(tuple){
			auto tpl=dom.isTupleTy();
			assert(!!tpl);
			assert(!isTuple&&names.length==1);
			auto vars=new TupleExp(iota(nnames.length).map!(i=>cast(Expression)varTy(nnames[i],tpl[i])).array);
			vars.type=dom;
			vars.sstate=SemState.completed;
			narg=vars;
		}else{
			assert(isTuple&&nnames.length==1);
			narg=varTy(nnames[0],dom);
		}
		auto ncod=tryApply(narg,isSquare);
		assert(!!ncod);
		return productTy(nIsConst,nnames,dom,ncod,isSquare,tuple,annotation,isClassical(this));
	}
	override ProductTy getClassical(){
		static if(language==silq) return classicalTy;
		else return this;
	}
	override int componentsImpl(scope int delegate(Expression) e){
		return 0; // TODO: ok?
	}
	override Expression evalImpl(Expression ntype){
		assert(isTypeTy(ntype));
		auto ndom=dom.eval(),ncod=cod.eval();
		if(ndom==dom&&ncod==cod) return this;
		return productTy(isConst,names,ndom,ncod,isSquare,isTuple,annotation,isClassical_);
	}
}

ProductTy productTy(bool[] isConst,string[] names,Expression dom,Expression cod,bool isSquare,bool isTuple,Annotation annotation,bool isClassical)in{
	assert(dom&&cod);
	if(isTuple){
		auto tdom=dom.isTupleTy();
		assert(tdom&&names.length==tdom.length&&isConst.length==tdom.length);
	}else assert(names.length==1&&isConst.length==1);
}do{
	return memoize!((bool[] isConst,string[] names,Expression dom,Expression cod,bool isSquare,bool isTuple,Annotation annotation,bool isClassical)=>new ProductTy(isConst,names,dom,cod,isSquare,isTuple,annotation,isClassical))(isConst,names,dom,cod,isSquare,isTuple,annotation,isClassical);
}

alias FunTy=ProductTy;
FunTy funTy(bool[] isConst,Expression dom,Expression cod,bool isSquare,bool isTuple,Annotation annotation,bool isClassical)in{
	assert(dom&&cod);
	if(isTuple){
		auto tdom=dom.isTupleTy();
		assert(tdom&&isConst.length==tdom.length);
	}else assert(isConst.length==1);
}do{
	auto nargs=1+[].length;
	if(isTuple) if(auto tpl=dom.isTupleTy()) nargs=tpl.length;
	return productTy(isConst,iota(nargs).map!(_=>"").array,dom,cod,isSquare,isTuple,annotation,isClassical);
}

FunTy funTy(Expression dom,Expression cod,bool isSquare,bool isTuple,Annotation annotation,bool isClassical)in{
	assert(dom&&cod);
}do{
	auto nargs=1+[].length;
	if(isTuple) if(auto tpl=dom.isTupleTy()) nargs=tpl.length;
	return funTy(false.repeat(nargs).array,dom,cod,isSquare,isTuple,annotation,isClassical);
}

FunTy funTy(Expression dom,Expression cod,bool isSquare,bool isTuple,bool isClassical)in{
	assert(dom&&cod);
}do{
	return funTy(dom,cod,isSquare,isTuple,pure_,isClassical);
}

Identifier varTy(string name,Expression type,bool classical=false)in{
	assert(name!=""&&type);
}do{
	return memoize!((string name,Expression type,bool classical){
		auto r=new Identifier(name);
		static if(language==silq) r.classical=classical;
		r.type=type;
		r.sstate=SemState.completed;
		return r;
	})(name,type,classical);
}

struct FreeIdentifiers{
	Expression self;
	int opApply(scope int delegate(Identifier) dg){
		int rec(Expression e){
			if(auto id=cast(Identifier)e) if(auto r=dg(id)) return r;
			if(auto pt=cast(ProductTy)e){
				foreach(id;pt.dom.freeIdentifiers)
					if(auto r=dg(id)) return r;
				foreach(id;pt.cod.freeIdentifiers){
					if(pt.names.canFind(id.name)) continue;
					if(auto r=dg(id)) return r;
				}
			}
			// TODO: LambdaExp
			foreach(x;e.components)
				if(auto r=rec(x))
					return r;
			return 0;
		}
		return rec(self);
	}
}
auto freeIdentifiers(Expression self){
	return FreeIdentifiers(self);
}
bool hasFreeIdentifier(Expression self,string name){
	foreach(id;self.freeIdentifiers) if(id.name==name) return true;
	return false;
}

static if(language==silq)
class UTypeTy: Type{
	this(){ this.type=ctypeTy; super(); } // TODO: types capturing quantum values?
	override UTypeTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		return "utype";
	}
	override bool opEquals(Object o){
		return !!cast(UTypeTy)o;
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
	override bool isSubtypeImpl(Expression r){
		return util.among(r,this,ctypeTy,qtypeTy,typeTy);
	}
	override Expression combineTypesImpl(Expression r,bool meet){
		if(meet){
			if(isSubtypeImpl(r)) return this;
			return null;
		}else{
			if(isSubtypeImpl(r)) return r;
			return null;
		}
	}
}
static if(language==silq){
	private UTypeTy theUTypeTy;
	UTypeTy utypeTy(){ return theUTypeTy?theUTypeTy:(theUTypeTy=new UTypeTy()); }
}else alias utypeTy=typeTy;

static if(language==silq)
class CTypeTy: Type{
	this(){ this.type=this; super(); } // TODO: types capturing quantum values?
	override CTypeTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		return "ctype";
	}
	override bool opEquals(Object o){
		return !!cast(CTypeTy)o;
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
	override bool isSubtypeImpl(Expression r){
		return util.among(r,this,typeTy);
	}
	override Expression combineTypesImpl(Expression r,bool meet){
		if(meet){
			if(r==qtypeTy) return utypeTy;
			if(r==typeTy) return this;
			return null;
		}else{
			if(r==qtypeTy||r==typeTy) return typeTy;
			return null;
		}
	}
}
static if(language==silq){
	private CTypeTy theCTypeTy;
	CTypeTy ctypeTy(){ return theCTypeTy?theCTypeTy:(theCTypeTy=new CTypeTy()); }
}else alias ctypeTy=typeTy;

static if(language==silq)
class QTypeTy: Type{
	this(){ this.type=ctypeTy; super(); } // TODO: types capturing quantum values?
	override QTypeTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		return "qtype";
	}
	override bool opEquals(Object o){
		return !!cast(QTypeTy)o;
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
	override bool isSubtypeImpl(Expression r){
		return r==this||r==typeTy;
	}
	override Expression combineTypesImpl(Expression r,bool meet){
		if(meet){
			if(r==ctypeTy) return utypeTy;
			if(r==typeTy) return this;
			return null;
		}else{
			if(r==ctypeTy||r==typeTy) return typeTy;
			return null;
		}
	}
}
static if(language==silq){
	private QTypeTy theQTypeTy;
	QTypeTy qtypeTy(){ return theQTypeTy?theQTypeTy:(theQTypeTy=new QTypeTy()); }
}else alias qtypeTy=typeTy;


class TypeTy: Type{
	this(){
		static if(language==silq){
			// TODO: types capturing quantum values?
			this.type=ctypeTy; // this.type=this?
		}else this.type=this;
		super();
	}
	override TypeTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		return "*";
	}
	override bool opEquals(Object o){
		return !!cast(TypeTy)o;
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
	override bool isSubtypeImpl(Expression r){
		return r==typeTy;
	}
	override Expression combineTypesImpl(Expression r,bool meet){
		if(meet){
			if(r.isSubtypeImpl(this)) return r;
			return null;
		}else{
			if(r.isSubtypeImpl(this)) return this;
			return null;
		}
	}
}
private TypeTy theTypeTy;
TypeTy typeTy(){ return theTypeTy?theTypeTy:(theTypeTy=new TypeTy()); }

bool isTypeTy(Expression e){ return isSubtype(e,typeTy); }
bool isType(Expression e){ return e&&isTypeTy(e.type); }

bool isClassicalTy(Expression e){ return isSubtype(e,ctypeTy); }
bool isClassical(Expression e){ return e&&isClassicalTy(e.type); }

bool isQuantumTy(Expression e){
	static if(language==silq) return isSubtype(e,qtypeTy);
	else return false;
}
bool isQuantum(Expression e){ return e&&isQuantumTy(e.type); }

Expression getClassicalTy(Expression e)in{ // typeof(!x) for x:e
	assert(isType(e));
}do{
	return ctypeTy;
}

bool hasClassicalComponentTy(Expression e){ return !isQuantumTy(e); }
bool hasClassicalComponent(Expression e){ return e&&hasClassicalComponentTy(e.type); }

bool hasQuantumComponentTy(Expression e){ return !isClassicalTy(e); }
bool hasQuantumComponent(Expression e){ return e&&hasQuantumComponentTy(e.type); }

Expression typeOfBoolTy(bool classical){
	return classical?ctypeTy:qtypeTy;
}

static if(language==silq)
class QNumericTy: Type{
	this(){ this.type=ctypeTy; super(); } // TODO: types capturing quantum values?
	override QNumericTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		return "qnumeric";
	}
	override bool opEquals(Object o){
		return !!cast(QNumericTy)o;
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}
static if(language==silq){
	private QNumericTy theQNumericTy;
	QNumericTy qnumericTy(){ return theQNumericTy?theQNumericTy:(theQNumericTy=new QNumericTy()); }
	bool isQNumericTy(Expression e){ return e==qnumericTy; }
	bool isQNumeric(Expression e){ return e&&isQNumericTy(e.type); }
}else{
	bool isQNumericTy(Expression e){ return false; }
	bool isQNumeric(Expression e){ return false; }
}

Expression typeOfNumericTy(bool classical){
	if(classical) return ctypeTy;
	static if(language==silq) return qnumericTy;
	else return typeTy;
}

Expression typeOfTupleTy(scope Expression[] e...)in{
	assert(e.all!(e=>isType(e)||isQNumeric(e)));
}do{
	if(!e.length) return utypeTy;
	static if(language==silq){
		if(e.any!isQNumeric) return qnumericTy;
	}
	if(e.all!isClassical) return ctypeTy;
	if(e.all!isQuantum) return qtypeTy;
	return typeTy;
}

Expression typeOfArrayTy(Expression e)in{
	assert(isType(e)||isQNumeric(e));
}do{
	static if(language==silq){
		if(isQNumeric(e)) return qnumericTy;
	}
	return typeOfTupleTy(e,ctypeTy);
}

Expression typeOfVectorTy(Expression e,Expression num)in{
	assert(isType(e)||isQNumeric(e));
	assert(num&&isSubtype(num.type,ℕt(true)));
}do{
	// TODO: num=0 ↦ utype
	return e.type;
}

Expression typeOfStringTy(bool classical){ return classical?ctypeTy:typeTy; }

Expression typeOfProductTy(bool[] isConst,string[] names,Expression dom,Expression cod,bool isSquare,bool isTuple,Annotation annotation,bool isClassical){
	return isClassical?ctypeTy:typeTy;
}
