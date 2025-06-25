// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.type;
import astopt;
import std.format: format;

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
import ast.modules: isInPrelude;

enum NumericType{
	none,
	Bool,
	ℕt,
	ℤt,
	ℚt,
	ℝ,
	ℂ,
}

NumericType isNumericTy(Expression t){
	assert(t);
	assert(t.isSemEvaluated());
	auto ty = cast(NumericTy)t;
	if(!ty) return NumericType.none;
	return ty.nty;
}

struct FixedIntTy {
	Expression bits;
	bool isSigned, isClassical;

	bool opCast(T: bool)() const pure @safe nothrow {
		return !!bits;
	}
}

FixedIntTy isFixedIntTy(Expression e){
	assert(e);
	assert(e.isSemEvaluated());
	auto ce=cast(CallExp)e;
	if(!ce || !ce.isSquare) return FixedIntTy();
	auto bits=ce.arg;
	bool isClassical=ce.isClassical_;

	auto id=cast(Identifier)ce.e;
	if(!id||!id.meaning||!isInPrelude(id.meaning)) return FixedIntTy();

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
	auto ce=cast(CallExp)e;
	if(!ce || !ce.isSquare) return null;
	auto id=cast(Identifier)ce.e;
	if(!id||!id.meaning||!isInPrelude(id.meaning)) return null;
	return id.name;
}

bool isFloat(Expression e){ return preludeNumericTypeName(e)=="float"; }
bool isRat(Expression e){ return preludeNumericTypeName(e)=="rat"; }

bool isSubtype(Expression lhs,Expression rhs){
	if(!lhs||!rhs) return false;
	assert(lhs.isSemEvaluated());
	assert(rhs.isSemEvaluated());
	if(lhs is rhs) return true;
	if(lhs.isClassical()&&!rhs.isClassical()) {
		rhs = rhs.getClassical();
		if(!rhs) return false;
		if(lhs is rhs) return true;
	} else if(!lhs.isClassical()&&rhs.isClassical()) {
		return false;
	}
	return lhs.isSubtypeImpl(rhs);
}

Expression combineTypes(Expression lhs,Expression rhs,bool meet,bool allowQNumeric=false){ // TODO: more general solution // TODO: ⊤/⊥?
	if(!lhs||isEmpty(lhs)) return rhs;
	if(!rhs||isEmpty(rhs)) return lhs;
	if(lhs == rhs) return lhs;
	auto l=lhs.eval(), r=rhs.eval();
	if(isEmpty(lhs)) return meet?lhs:rhs;
	if(isEmpty(rhs)) return meet?rhs:lhs;
	auto result = l.combineTypesImpl(r,meet);
	if(!allowQNumeric && isQNumeric(result)) return null;
	return result;
}

Expression joinTypes(Expression lhs,Expression rhs){
	return combineTypes(lhs,rhs,false);
}
Expression meetTypes(Expression lhs,Expression rhs){
	return combineTypes(lhs,rhs,true);
}

abstract class Type: Expression{
	override @property string kind(){ return "type"; }
	override string toString(){ return "T"; }
	abstract override bool opEquals(Object r);
	override Annotation getAnnotation(){ return pure_; }
}

class NumericTy: Type{
	private NumericType nty;
	static if(language==silq) {
		private bool classical;
		private this(NumericType nty, bool classical){
			assert(nty);
			assert(!theNumeric[nty][classical]);
			this.nty = nty;
			this.classical = classical;
			this.type = classical ? ctypeTy() : nty == NumericType.Bool ? qtypeTy() : qnumericTy();
			setSemEvaluated();
		}
	} else {
		private enum classical=true;
		private this(NumericType nty) {
			assert(!theNumeric[nty]);
			this.nty = nty;
			this.type = typeTy();
			setSemEvaluated();
		}
	}
	override NumericTy getClassical(){
		if(this.classical) return this;
		return numericTy(this.nty, true);
	}
	override NumericTy getQuantum(){
		if(!this.classical) return this;
		return numericTy(this.nty, false);
	}
	override Expression combineTypesImpl(Expression r, bool meet){
		auto ty = cast(NumericTy)r;
		if(!ty) return null;
		if(meet) return numericTy(min(nty, ty.nty), classical || ty.classical);
		return numericTy(max(nty, ty.nty), classical && ty.classical);
	}
	override bool isSubtypeImpl(Expression r){
		auto ty = cast(NumericTy)r;
		if(!ty) return false;
		assert(ty !is this);
		return nty <= ty.nty && classical >= ty.classical;
	}
	override NumericTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		size_t i = 1;
		static if(language==silq) {
			i = !classical;
		}
		final switch(nty) {
			case NumericType.none: assert(0);
			case NumericType.Bool: return "!𝔹"[i..$];
			case NumericType.ℕt: return "!ℕ"[i..$];
			case NumericType.ℤt: return "!ℤ"[i..$];
			case NumericType.ℚt: return "!ℚ"[i..$];
			case NumericType.ℝ: return "!ℝ"[i..$];
			case NumericType.ℂ: return "!ℂ"[i..$];
		}
	}
	override bool isConstant(){ return true; }
	override bool isTotal(){ return true; }
	override bool opEquals(Object o){
		return o is this;
	}
	override Expression evalImpl(){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}
static if(language==silq) private NumericTy[2][7] theNumeric;
else private NumericTy[7] theNumeric;

NumericTy Bool(bool classical=true){
	return numericTy(NumericType.Bool, classical);
}

NumericTy ℕt(bool classical=true){
	return numericTy(NumericType.ℕt, classical);
}

NumericTy ℤt(bool classical=true){
	return numericTy(NumericType.ℤt, classical);
}

NumericTy ℚt(bool classical=true){
	return numericTy(NumericType.ℚt, classical);
}

NumericTy ℝ(bool classical=true){
	return numericTy(NumericType.ℝ, classical);
}

NumericTy ℂ(bool classical=true){
	return numericTy(NumericType.ℂ, classical);
}

NumericTy numericTy(NumericType which, bool classical){
	if(!which) return null;
	static if(language==silq){
		return theNumeric[which][classical] ? theNumeric[which][classical] : (theNumeric[which][classical] = new NumericTy(which, classical));
	} else {
		return theNumeric[which] ? theNumeric[which] : (theNumeric[which] = new NumericTy(which));
	}
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
		this.type=typeTy(); // TODO
		setSemEvaluated();
	}
	override AggregateTy copyImpl(CopyArgs args){
		return this;
	}
	override bool opEquals(Object o){
		if(o is this) return true;
		if(auto r=cast(AggregateTy)o)
			return decl is r.decl && classical==r.classical;
		return false;
	}
	override string toString(){
		return decl&&decl.name?decl.name.name:"<anonymous aggregate>";
	}
	override bool isConstant(){ return true; }
	override bool isTotal(){ return true; }
	override AggregateTy getClassical(){
		static if(language==silq) return classicalTy;
		else return this;
	}
	override AggregateTy getQuantum(){
		static if(language==silq) return quantumTy;
		else return this;
	}

	override Expression evalImpl(){ return this; }
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
		this.type = classical ? ctypeTy() : typeTy();
		setSemEvaluated();
	}
	override ContextTy copyImpl(CopyArgs args){
		return this;
	}
	override bool isConstant(){ return true; }
	override bool isTotal(){ return true; }
	override bool opEquals(Object o){
		if(o is this) return true;
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
	override Expression evalImpl(){ return this; }
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


class BottomTy: Type{
	this(){
		type = etypeTy;
		setSemEvaluated();
	}
	override BottomTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		return "⊥";
	}
	override bool isConstant(){ return true; }
	override bool isTotal(){ return true; }
	override bool opEquals(Object o){
		auto bot=cast(BottomTy)o;
		return !!bot;
	}
	override bool isSubtypeImpl(Expression r){
		return true;
	}
	override Expression combineTypesImpl(Expression r,bool meet){
		return meet?this:r;
	}
	override BottomTy getClassical(){
		return this;
	}
	override Expression evalImpl(){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) e){
		return 0;
	}
}
private BottomTy theBottomTy;
BottomTy bottom(){
	return theBottomTy?theBottomTy:(theBottomTy=new BottomTy());
}


class ClassicalTy: Expression{
	Expression inner;
	this(Expression inner){
		this.inner = inner;
	}
	override string toString(){
		return "!" ~ inner.toString();
	}
	override ClassicalTy copyImpl(CopyArgs args){
		return new ClassicalTy(inner.copy(args));
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(inner);
	}
	override int freeVarsImpl(scope int delegate(Identifier) dg){
		return inner.freeVarsImpl(dg);
	}
	override Expression substituteImpl(Expression[Id] subst){
		return new ClassicalTy(inner.substitute(subst));
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		assert(false);
	}
	override Annotation getAnnotation(){
		return pure_;
	}
	override Expression evalImpl(){
		return inner.eval().getClassical();
	}
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
	this(Expression[] types)in{
		assert(types.all!());
	}do{
		this.types=types;
	}
	override TupleTy copyImpl(CopyArgs args){
		return new TupleTy(types.map!(ty => ty.copy(args)).array);
	}
	override string toString(){
		if(!types.length) return "𝟙";
		if(types.length==1) return "("~types[0].toString()~")¹";
		string addp(Expression a){
			if(cast(FunTy)a) return "("~a.toString()~")";
			return a.toString();
		}
		return types.map!(a=>a.isTupleTy()&&a!=unit?"("~a.toString()~")":addp(a)).join(" × ");
	}
	override bool isConstant(){ return types.all!(ty=>ty.isConstant()); }
	override bool isTotal(){ return types.all!(ty=>ty.isTotal()); }
	override int freeVarsImpl(scope int delegate(Identifier) dg){
		foreach(t;types)
			if(auto r=t.freeVarsImpl(dg))
				return r;
		return 0;
	}
	override Type substituteImpl(Expression[Id] subst){
		auto ntypes=types.dup;
		foreach(ref t;ntypes) t=t.substitute(subst);
		return tupleTy(ntypes);
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		auto tt=rhs.isTupleTy();
		if(!tt||types.length!=tt.length) return false;
		return all!(i=>types[i].unify(tt[i],subst,meet))(iota(types.length));

	}
	override bool opEquals(Object o){
		if(o is this) return true;
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
	override bool mayBeClassical(){ return types.all!(x=>x.mayBeClassical()); }
	override bool mayBeQuantum(){ return types.all!(x=>x.mayBeQuantum()); }
	override int componentsImpl(scope int delegate(Expression) dg){
		foreach(x;types) if(auto r=dg(x)) return r;
		return 0;
	}
	override Expression evalImpl(){
		assert(isTypeTy(type) || isQNumericTy(type));
		auto ntypes=types.map!(t=>t.eval()).array;
		if(iota(types.length).all!(i => ntypes[i] is types[i])) return this;
		return tupleTy(ntypes);
	}
}

Type unit(){ return tupleTy([]); }

Type tupleTy(Expression[] types)in{
	assert(types.all!(e=>isType(e)||isQNumeric(e)));
	assert(types.all!(e=>e.isSemEvaluated()));
}do{
	import ast.lexer: Token,Tok;
	if(types.length&&types.all!(x=>x==types[0])){
		return vectorTy(types[0], types.length);
	}
	return memoize!((Expression[] types){
		auto r = new TupleTy(types);
		r.type = typeOfTupleTy(r.types);
		r.setSemEvaluated();
		return r;
	})(types);
}

size_t numComponents(Expression t){
	if(auto tpl=t.isTupleTy())
		return tpl.length;
	return 1;
}

class ArrayTy: Type{
	Expression next;
	this(Expression next)in{
		assert(next);
	}do{
		this.next=next;
	}
	override ArrayTy copyImpl(CopyArgs args){
		return new ArrayTy(next.copy(args));
	}
	override string toString(){
		bool p=cast(FunTy)next||next.isTupleTy()&&next!=unit;
		return p?"("~next.toString()~")[]":next.toString()~"[]";
	}
	override bool isConstant(){ return next.isConstant(); }
	override bool isTotal(){ return next.isTotal(); }
	override int freeVarsImpl(scope int delegate(Identifier) dg){
		return next.freeVarsImpl(dg);
	}
	override ArrayTy substituteImpl(Expression[Id] subst){
		return arrayTy(next.substitute(subst));
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		if(auto vt=cast(VectorTy)rhs)
			return next.unifyImpl(vt.next,subst,meet);
		if(auto tt=cast(TupleTy)rhs)
			return tt.types.all!(ty=>next.unifyImpl(ty,subst,meet));
		if(auto at=cast(ArrayTy)rhs)
			return next.unifyImpl(at.next,subst,meet);
		return false;
	}
	override ArrayTy evalImpl(){
		assert(isTypeTy(type) || isQNumericTy(type));
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
				auto rtype=iota(rtup.length).map!(i=>rtup[i]).fold!((a,b)=>a?combineTypes(a,b,meet):null)(next);
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
		return null; // length is classical
	}
	override bool mayBeClassical(){ return next.mayBeClassical(); }
	override bool mayBeQuantum(){ return false; } // TODO: ok?
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(next);
	}
}

ArrayTy arrayTy(Expression next)in{
	assert(isType(next)||isQNumeric(next));
	assert(next.isSemEvaluated());
}do{
	return memoize!((Expression next){
		auto r = new ArrayTy(next);
		r.type = typeOfArrayTy(next);
		r.setSemEvaluated();
		return r;
	})(next);
}

class VectorTy: Type, ITupleTy{
	Expression next,num;
	this(Expression next,Expression num)in{
		assert(next);
		assert(num);
	}do{
		this.next=next;
		this.num=num;
	}
	override ITupleTy isTupleTy(){
		if(auto len=num.asIntegerConstant())
			if(len.get()<=size_t.max) return this;
		return null;
	}
	override VectorTy copyImpl(CopyArgs args){
		return new VectorTy(next.copy(args), num.copy(args));
	}
	@property size_t length(){
		auto lit=cast(LiteralExp)num;
		assert(!!lit);
		return lit.asIntegerConstant().get().to!size_t(); // TODO: avoid crash if length is too big
	}
	Expression opIndex(size_t i){ return next; }
	Expression opSlice(size_t l,size_t r){
		assert(0<=l&&l<=r&&r<=length);
		auto len=LiteralExp.makeInteger(r-l);
		return vectorTy(next,len);
	}
	override string toString(){
		bool p=cast(FunTy)next||next.isTupleTy&&next!=unit;
		bool q=!cast(Identifier)num&&!cast(LiteralExp)num; // TODO: improve
		return (p?"("~next.toString()~")^":next.toString()~"^")~(q?"("~num.toString()~")":num.toString());
	}
	override bool isConstant(){ return next.isConstant() && num.isConstant(); }
	override bool isTotal(){ return next.isTotal() && num.isTotal(); }
	override int freeVarsImpl(scope int delegate(Identifier) dg){
		if(auto r=next.freeVarsImpl(dg)) return r;
		return num.freeVarsImpl(dg);
	}
	override VectorTy substituteImpl(Expression[Id] subst){
		return vectorTy(next.substitute(subst),num.substitute(subst));
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		if(auto tt=cast(TupleTy)rhs)
			return tt.types.all!(ty=>next.unifyImpl(ty,subst,meet)) && num.unifyImpl(LiteralExp.makeInteger(tt.length),subst,meet);
		if(auto vt=cast(VectorTy)rhs){
			auto r=next.unifyImpl(vt.next,subst,meet);
			if(auto nlit=num.asIntegerConstant())
				if(nlit.get()==0&&num==vt.num) return true;
			return r && num.unifyImpl(vt.num,subst,meet);
		}
		return false;
	}
	override VectorTy evalImpl(){
		assert(isTypeTy(type) || isQNumericTy(type));
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
		if(rvec){
			if(num!=rvec.num) return false;
			if(auto nlit=num.asIntegerConstant())
				if(nlit.get()==0) return true;
			return isSubtype(lvec.next,rvec.next);
		}
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
	override bool mayBeClassical(){ return next.mayBeClassical(); }
	override bool mayBeQuantum(){ return next.mayBeQuantum(); }
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(next)) return r;
		return dg(num);
	}
}

VectorTy vectorTy(Expression next,Expression num)in{
	assert(isType(next)||isQNumeric(next));
	assert(next.isSemEvaluated(), format("unevaluated vector item type %s", next));
	assert(num&&isSubtype(num.type,ℕt(true)));
	assert(num.isSemEvaluated(), format("unevaluated vector length %s", num));
}do{
	return memoize!((Expression next,Expression num){
		auto r = new VectorTy(next,num);
		r.type = typeOfVectorTy(next, num);
		r.setSemEvaluated();
		return r;
	})(next,num);
}
VectorTy vectorTy(Expression next, size_t num){
	return vectorTy(next, LiteralExp.makeInteger(num));
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
		setSemEvaluated();
	}
	override StringTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!string":"string";
		else return "string";
	}
	override bool isConstant(){ return true; }
	override bool isTotal(){ return true; }
	override bool opEquals(Object o){ return o is this; }
	override Expression evalImpl(){ return this; }
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

class ProductTy: Type{
	Parameter[] params;
	bool[] isConst;
	Id[] names;
	Expression dom, cod; // `dom` set by semantic analysis
	bool isSquare,isTuple;
	Annotation annotation;
	static if(language==silq){
		private ProductTy classicalTy;
		bool isClassical_;
	}else enum isClassical_=true;
	this(Parameter[] params, Expression cod, bool isSquare, bool isTuple, Annotation annotation, bool isClassical_)in{
		assert(cod);
		// TODO: assert that all names are distinct
	}do{
		this.params = params;
		this.isConst = params.map!(p => p.isConst).array;
		this.names = params.map!(p => p.name ? p.getId : Id()).array;
		this.isSquare = isSquare;
		this.isTuple = isTuple;
		this.cod = cod;
		this.annotation = annotation;
		static if(language==silq){
			this.isClassical_=isClassical_;
		}
	}
	override void setSemCompleted() {
		assert(dom && dom.isSemEvaluated(), format("completed semantic analysis of product type without domain: %s", this));
		assert(cod && cod.isSemCompleted(), format("completed semantic analysis of product type without codomain: %s", this));
		super.setSemCompleted();
	}
	override ProductTy copyImpl(CopyArgs args){
		auto r = new ProductTy(params.map!(p=>p.copy(args)).array, cod.copy(args), isSquare, isTuple, annotation, isClassical_);
		if(args.preserveSemantic) {
			r.dom = dom;
		}
		return r;
	}
	/+private+/ @property ITupleTy tdom()in{ // TODO: make private
		assert(isTuple);
		assert(dom);
	}do{
		auto r=dom.isTupleTy;
		assert(!!r);
		return r;
	}
	override string toString(){
		auto c=cod ? cod.toString() : "<missing codomain>";
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
		if(cod && !cod.hasAnyFreeVar(names)){
			string d;
			string addp(bool const_,Expression a,string del="()"){
				auto paramKind=getParamKind(const_);
				if(cast(ProductTy)a) return del[0]~(paramKind?paramKind~"(":"")~a.toString()~(paramKind?")":"")~del[1];
				if(a.isTupleTy()) return (paramKind?paramKind~"(":"")~a.toString()~(paramKind?")":"");
				return paramKind~a.toString();
			}
			d=params.empty?cod.toString():params.map!((p){
				auto paramKind=getParamKind(p.isConst);
				auto pty = p.vtype ? p.vtype : p.dtype;
				auto ptup = pty.isTupleTy();
				return (ptup && ptup.length > 1) ? "("~paramKind~pty.toString()~")" : addp(p.isConst, pty);
			}).join(" × ");
			if(isTuple && params.length == 1) {
				d="("~d~")¹";
			}
			static if(language==silq) auto arrow=(isClassical_?"!":"")~"→";
			else enum arrow="→";
			if(isSquare) d=del[0]~d~del[1];
			r=d~" "~arrow~(annotation?annotationToString(annotation):"")~" "~c;
		}else{
			string args;
			args=params.map!((p){
				auto paramKind=getParamKind(p.isConst);
				auto pty = p.vtype ? p.vtype : p.dtype;
				return paramKind~(p.name ? p.name.toString() : "_")~":"~pty.toString();
			}).join(",");
			static if(language==silq) auto pi=(isClassical_?"!":"")~"∏";
			else enum pi="Π";
			r=pi~del[0]~args~del[1]~annotationToString(annotation)~". "~c;
		}
		return r;
	}
	override bool isConstant(){ return dom.isConstant() && cod.isConstant(); }
	override bool isTotal(){ return dom.isTotal() && cod.isTotal(); }
	@property size_t nargs(){
		return params.length;
	}
	Expression argTy(size_t i){
		auto ty = params[i].vtype;
		assert(ty.isSemEvaluated());
		return ty;
	}
	bool argConst(size_t i){
		return params[i].isConst;
	}
	bool argConstForReverse(size_t i){
		if(argConst(i)) return true;
		auto ty = argTy(i);
		return ty.isClassical() && !ty.mayBeQuantum();
	}
	bool argConstForSubtyping(size_t i){
		return argConst(i) || argTy(i).isClassical;
	}
	override int freeVarsImpl(scope int delegate(Identifier) dg){
		if(dom) {
			if(auto r=dom.freeVarsImpl(dg)) return r;
		} else {
			assert(!isSemCompleted());
		}
		return cod.freeVarsImpl(v=>names.canFind(v.id)?0:dg(v));
	}
	private ProductTy relabel(Id oname,Id nname)in{
		assert(names.canFind(oname));
		assert(!hasFreeVar(nname));
		assert(!names.canFind(nname));
	}out(r){
		if(oname&&oname!=nname){
			assert(r.names.canFind(nname));
			assert(!r.names.canFind(oname));
		}
	}do{
		if(!oname||oname==nname) return this;
		import std.algorithm;
		auto i=names.countUntil(oname);
		assert(i!=-1);
		auto nnames=names.dup;
		nnames[i]=nname;
		auto nvar=varTy(nname,argTy(i));
		return productTy(isConst,nnames,dom,cod.substitute(oname,nvar),isSquare,isTuple,annotation,isClassical_);
	}
	private ProductTy relabelAway(Id oname)in{
		assert(names.canFind(oname));
	}out(r){
		if(!!oname) assert(!r.names.canFind(oname));
	}do{
		if(!oname) return this;
		auto nname=oname;
		while(names.canFind(nname)||hasFreeVar(nname)) nname=nname.apos;
		return relabel(oname,nname);
	}
	private Id freshName(Id base,Expression block){
		auto nn=base;
		if(!nn) nn=Id.intern("x");
		while(hasFreeVar(nn)||block.hasFreeVar(nn)) nn=nn.apos;
		return nn;
	}
	Id[] freshNames(Expression block){
		auto nnames=names.dup;
		foreach(i,ref nn;nnames){
			if(!nn) nn=Id.intern("x");
			while(hasFreeVar(nn)||block.hasFreeVar(nn)||nnames[0..i].canFind(nn)) nn=nn.apos;
		}
		return nnames;
	}
	ProductTy relabelAll(Id[] nnames)out(r){
		assert(nnames.length==names.length);
		foreach(n;nnames) assert(!hasFreeVar(n));
	}do{
		if(nnames==names) return this;
		Expression[Id] subst;
		foreach(i;0..names.length) subst[names[i]]=varTy(nnames[i],argTy(i));
		return productTy(isConst,nnames,dom,cod.substitute(subst),isSquare,isTuple,annotation,isClassical_);
	}
	override ProductTy substituteImpl(Expression[Id] subst){
		foreach(n;names){
			if(!n) continue;
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
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
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
		r=r.relabelAll(iota(names.length).map!(i=>names[i]?names[i]:r.names[i]).array);
		Expression[Id] nsubst;
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
		Expression[Id] subst;
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
			tgarg.setSemCompleted();
			garg=tgarg;
		}else garg=gargs[0];
		cod=cast(ProductTy)tryApply(garg,true);
		if(!cod) return null;
		return cod.tryApply(arg,false);
	}
	Expression tryApply(Expression arg,bool isSquare){
		assert(arg.isSemCompleted());
		if(isSquare != this.isSquare) return null;
		if(!isSubtype(arg.type,dom)) return null;
		Expression[Id] subst;
		if(isTuple){
			auto targTy=arg.type.isTupleTy();
			assert(!!tdom);
			foreach(i,n;names){
				auto exp=new IndexExp(arg,LiteralExp.makeInteger(i));
				exp.type=targTy[i];
				exp.setSemCompleted();
				subst[n]=exp.eval();
			}
		}else{
			assert(names.length==1);
			subst[names[0]]=arg.eval();
		}
		return cod.substitute(subst);
	}
	override bool opEquals(Object o){
		if(o is this) return true;
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
		return iota(nargs).map!(i=>argConstForReverse(i));
	}
	private auto isConstForSubtyping(){
		return iota(nargs).map!(i=>argConstForSubtyping(i));
	}

	bool isConstCompatible(ProductTy rhs){
		assert(isTuple == rhs.isTuple);
		assert(nargs == rhs.nargs);
		return iota(nargs).all!(i =>
			argConst(i) == rhs.argConst(i) ||
			argTy(i).isClassical || rhs.argTy(i).isClassical
		);
	}

	override bool isSubtypeImpl(Expression rhs){
		auto r=cast(ProductTy)rhs;
		if(!r) return false;
		if(isTuple&&!r.dom.isTupleTy()) return false;
		r=r.setTuple(isTuple);
		if(!r) return false;
		if(isSquare!=r.isSquare||nargs!=r.nargs||!isConstCompatible(r))
			return false;
		if(annotation<r.annotation||!isClassical_&&r.isClassical_)
			return false;
		auto name=freshName(Id(),r);
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
		auto nannotation=meet?max(annotation,r.annotation):min(annotation,r.annotation);
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
			vars.setSemCompleted();
			auto lCod=tryApply(vars,isSquare);
			auto rCod=r.tryApply(vars,isSquare);
			assert(lCod&&rCod);
			auto ncod=combineTypes(lCod,rCod,meet);
			if(!ncod) return null;
			return productTy(nIsConst,names,ndom,ncod,isSquare,isTuple,nannotation,nisClassical);
		}else{
			Expression lCod,rCod;
			if(names[0]!=Id()||r.names[0]!=Id()){
				auto name=names[0]==r.names[0]?names[0]:freshName(Id(),r);
				auto var=varTy(name,ndom);
				lCod=tryApply(var,isSquare);
				rCod=r.tryApply(var,isSquare);
			}else{
				lCod=cod;
				rCod=r.cod;
			}
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
		Id[] nnames;
		bool[] nIsConst;
		if(tuple){
			auto tpl=dom.isTupleTy();
			assert(!!tpl);
			assert(!isTuple&&names.length==1);
			nnames=iota(tpl.length).map!(i=>Id.intern(names[0].str~lowNum(i))).array;
			assert(isConst.length==1);
			nIsConst=isConst[0].repeat(tpl.length).array;
		}else{
			if(!isConst.empty&&!isConst.all!(x=>x==isConst.front))
				return null;
			nnames=[Id.intern("t")];
			nIsConst=[isConst.empty?false:isConst.front];
		}
		foreach(i,ref nn;nnames) while(hasFreeVar(nn)) nn=nn.apos;
		Expression narg;
		if(tuple){
			auto tpl=dom.isTupleTy();
			assert(!!tpl);
			assert(!isTuple&&names.length==1);
			auto vars=new TupleExp(iota(nnames.length).map!(i=>cast(Expression)varTy(nnames[i],tpl[i])).array);
			vars.type=dom;
			vars.setSemCompleted();
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
		static if(language==silq) {
			if(classicalTy) return classicalTy;
			if(isClassical_) return classicalTy=this;
			return classicalTy=productTy(isConst, names, dom, cod, isSquare, isTuple, annotation, true);
		} else {
			return this;
		}
	}
	override int componentsImpl(scope int delegate(Expression) e){
		return 0; // TODO: ok?
	}
	override Expression evalImpl(){
		assert(isTypeTy(type));
		auto ndom=dom;
		auto ncod=cod.eval();
		return productTy(isConst,names,ndom,ncod,isSquare,isTuple,annotation,isClassical_);
	}
}

ProductTy productTy(bool[] isConst,Id[] names,Expression dom,Expression cod,bool isSquare,bool isTuple,Annotation annotation,bool isClassical)in{
	assert(dom && dom.isSemEvaluated(), format("function domain not analyzed: %s", dom));
	assert(cod && cod.isSemEvaluated());
	if(isTuple){
		auto tdom=dom.isTupleTy();
		assert(tdom&&names.length==tdom.length&&isConst.length==tdom.length);
	}else assert(names.length==1&&isConst.length==1);
}do{
	return memoize!((bool[] isConst,Id[] names,Expression dom,Expression cod,bool isSquare,bool isTuple,Annotation annotation,bool isClassical){
		Expression[] types;
		if(isTuple) {
			auto tdom = dom.isTupleTy;
			assert(tdom);
			types = iota(tdom.length).map!(i => tdom[i]).array;
		} else {
			types = [dom];
		}
		assert(types.length == names.length);
		auto params = new Parameter[names.length];
		Expression[Id] subst;
		foreach(i, name; names) {
			Identifier id;
			if(name) {
				id = varTy(name, types[i]);
				if(name) subst[name] = id;
			}
			auto p = new Parameter(isConst[i], id, types[i]);
			params[i] = p;
			p.vtype = p.dtype;
			p.setSemEvaluated();
		}
		cod = cod.substitute(subst);
		auto r = new ProductTy(params, cod, isSquare, isTuple, annotation, isClassical);
		r.dom = dom;
		r.type = typeOfProductTy(isConst, names, dom, cod, isSquare, isTuple, annotation, isClassical);
		r.setSemEvaluated();
		return r;
	})(isConst, names, dom, cod, isSquare, isTuple, annotation, isClassical);
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
	return productTy(isConst,iota(nargs).map!(_=>Id()).array,dom,cod,isSquare,isTuple,annotation,isClassical);
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

Expression typeOfVariadicTy(Expression next, bool isClassical)in{
	assert(next&&next.type,text(next));
	if(auto tpl=cast(TupleTy)next.type)
		assert(tpl.types.all!(t=>isType(t)||isQNumeric(t)));
	else{
		auto et=elementType(next.type);
		assert(isType(et)||isQNumeric(et));
	}
}do{
	if(auto tpl=cast(TupleTy)next.type){
		Expression r=utypeTy;
		foreach(t;tpl.types)
			r=joinTypes(r,t);
		return isClassical ? r.getClassicalTy() : r;
	}
	auto enext=elementType(next.type);
	return isClassical ? enext.getClassicalTy() : enext;
}

class VariadicTy: Type{
	Expression next;
	bool isClassical_;
	override ITupleTy isTupleTy(){
		auto r=eval();
		if(cast(VariadicTy)r) return null;
		return r.isTupleTy();
	}
	this(Expression next,bool isClassical_){
		this.next=next;
		this.isClassical_=isClassical_;
	}
	override VariadicTy copyImpl(CopyArgs args){
		return new VariadicTy(next.copy(args), isClassical_);
	}
	override string toString(){
		auto ns="("~next.toString()~")";
		import std.uni:isAlpha;
		return (isClassical_?"!":"")~(ns[0].isAlpha?"∏ ":"∏")~ns;
	}
	override bool isConstant(){ return next.isConstant(); }
	override bool isTotal(){ return next.isTotal(); }
	override int freeVarsImpl(scope int delegate(Identifier) dg){
		return next.freeVarsImpl(dg);
	}
	override Expression substituteImpl(Expression[Id] subst){
		return variadicTy(next.substitute(subst),isClassical_);
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		if(auto vt=cast(VariadicTy)rhs)
			return next.unifyImpl(vt.next,subst,meet);
		// if(auto vt=cast(VectorTy)rhs) return next.unifyImpl(vector(vt.next.num,vt.next.type),subst,meet); // TODO
		// if(auto at=cast(ArrayTy)rhs) // TODO
		if(auto tt=rhs.isTupleTy()){
			auto types=iota(tt.length).map!(i=>tt[i]).array;
			auto tpl=new TupleExp(types);
			tpl.type=tupleTy(tpl.e.map!(e=>e.type).array);
			tpl.setSemCompleted();
			return next.unifyImpl(tpl,subst,meet);
		}
		return false;
	}
	override Expression evalImpl(){
		assert(isTypeTy(type));
		auto ne=next.eval();
		bool hasElements=false;
		Expression[] elements;
		if(auto vec=cast(VectorExp)ne){
			hasElements=true;
			elements=vec.e;
		}
		if(auto tpl=cast(TupleExp)ne){
			hasElements=true;
			elements=tpl.e;
		}
		if(hasElements){
			auto tt=tupleTy(elements);
			if(isClassical_) return tt.getClassical;
			return tt;
		}
		if(ne is next) return this;
		return variadicTy(ne,isClassical_);
	}
	override bool opEquals(Object o){
		if(o is this) return true;
		if(auto r=cast(VariadicTy)o)
			return next==r.next&&isClassical_==r.isClassical;
		return false;
	}
	override bool isSubtypeImpl(Expression r){
		if(auto vt=cast(VariadicTy)r)
			return next==vt.next && isClassical(this)>=isClassical(vt); // TODO: improve
		// if(auto vt=cast(VectorTy)rhs) ... // TODO
		// if(auto at=cast(ArrayTy)rhs) ... // TODO
		if(auto tt=r.isTupleTy()){
			auto tpl=new TupleExp(iota(tt.length).map!(i=>tt[i]).array);
			tpl.type=tupleTy(iota(tt.length).map!(i=>tt[i].type).array);
			tpl.setSemCompleted();
			return next==tpl; // TODO: improve
		}
		return false;
	}
	override Expression combineTypesImpl(Expression r,bool meet){
		return this==r?this:null; // TODO
	}
	override Expression getClassical(){
		if(isClassical_) return this;
		return variadicTy(next, true);
	}
	override Expression getQuantum(){
		return null; // TODO
	}
	override bool mayBeClassical(){ return true; } // TODO
	override bool mayBeQuantum(){ return true; } // TODO
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(next);
	}
}

Expression variadicTy(Expression next,bool isClassical)in{
	assert(next&&next.isSemEvaluated());
	if(auto tpl=cast(TupleTy)next.type)
		assert(tpl.types.all!(t=>isType(t)||isQNumeric(t)));
	else assert(isType(elementType(next.type))||isQNumeric(elementType(next.type)));
}do{
	if(auto ve=cast(VectorExp)next){
		next=new TupleExp(ve.e);
		next.type=tupleTy(ve.e.map!(e=>e.type).array);
		next.setSemCompleted();
		next=next.eval();
	}
	return memoize!((Expression next,bool isClassical){
		auto r = new VariadicTy(next, isClassical);
		r.type = typeOfVariadicTy(next, isClassical);
		r.setSemCompleted();
		assert(!r.isClassical_ || r.type.isClassical);
		return r;
	})(next,isClassical).eval();
}

Identifier varTy(Id name,Expression type,bool classical=false)in{
	assert(name&&type);
}do{
	return memoize!((Id name,Expression type,bool classical){
		auto r=new Identifier(name);
		static if(language==silq) r.classical=classical;
		r.type=type;
		r.setSemEvaluated();
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
					if(pt.names.canFind(id.id)) continue;
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
bool hasFreeIdentifier(Expression self,Id name){
	foreach(id;self.freeIdentifiers) if(id.id==name) return true;
	return false;
}


static if(language==silq){
	private enum TypeType {
		etype,
		utype,
		ctype,
		qtype,
		mtype,
	}
	private immutable TypeType[5][5] typeJoin = [
		[TypeType.etype, TypeType.utype, TypeType.ctype, TypeType.qtype, TypeType.mtype],
		[TypeType.utype, TypeType.utype, TypeType.ctype, TypeType.qtype, TypeType.mtype],
		[TypeType.ctype, TypeType.ctype, TypeType.ctype, TypeType.mtype, TypeType.mtype],
		[TypeType.qtype, TypeType.qtype, TypeType.mtype, TypeType.qtype, TypeType.mtype],
		[TypeType.mtype, TypeType.mtype, TypeType.mtype, TypeType.mtype, TypeType.mtype],
	];
	private immutable TypeType[5][5] typeMeet = [
		[TypeType.etype, TypeType.etype, TypeType.etype, TypeType.etype, TypeType.etype],
		[TypeType.etype, TypeType.utype, TypeType.utype, TypeType.utype, TypeType.utype],
		[TypeType.etype, TypeType.utype, TypeType.ctype, TypeType.utype, TypeType.ctype],
		[TypeType.etype, TypeType.utype, TypeType.utype, TypeType.qtype, TypeType.qtype],
		[TypeType.etype, TypeType.utype, TypeType.ctype, TypeType.qtype, TypeType.mtype],
	];
}

class TypeTy: Type{
	static if(language==silq){
		private TypeType tyty;
		private this(TypeType tyty){
			assert(theTypeTys[tyty] is null, "types are singletons");
			this.tyty = tyty;
			// TODO: types capturing quantum values?
			this.type=(tyty == TypeType.ctype ? this : ctypeTy());
			setSemEvaluated();
		}
		override string toString(){
			final switch(tyty) {
				case TypeType.etype: return "etype";
				case TypeType.utype: return "utype";
				case TypeType.ctype: return "ctype";
				case TypeType.qtype: return "qtype";
				case TypeType.mtype: return "*";
			}
		}
		override bool isSubtypeImpl(Expression r){
			assert(r !is this);
			auto ty=cast(TypeTy)r;
			if(!ty) return false;
			return typeJoin[this.tyty][ty.tyty] == ty.tyty;
		}
		override Expression combineTypesImpl(Expression r,bool meet){
			assert(r !is this);
			auto ty=cast(TypeTy)r;
			if(!ty) return null;
			return typeTyImpl(meet ? typeMeet[this.tyty][ty.tyty] : typeJoin[this.tyty][ty.tyty]);
		}
	} else {
		private this() {
			this.type=this;
			super();
		}
		override string toString(){
			return "*";
		}
		override bool isSubtypeImpl(Expression r){
			assert(r !is this);
			return false;
		}
		override Expression combineTypesImpl(Expression r,bool meet){
			assert(r !is this);
			return null;
		}
	}
	override TypeTy copyImpl(CopyArgs args){
		return this;
	}
	override bool opEquals(Object o){
		return o is this;
	}
	override Expression evalImpl(){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}


static if(language==silq){
	private TypeTy[5] theTypeTys;
	private TypeTy typeTyImpl(TypeType tyty) {
		return theTypeTys[tyty] ? theTypeTys[tyty] : (theTypeTys[tyty] = new TypeTy(tyty));
	}
	TypeTy etypeTy(){ return typeTyImpl(TypeType.etype); }
	TypeTy utypeTy(){ return typeTyImpl(TypeType.utype); }
	TypeTy ctypeTy(){ return typeTyImpl(TypeType.ctype); }
	TypeTy qtypeTy(){ return typeTyImpl(TypeType.qtype); }
	TypeTy typeTy(){ return typeTyImpl(TypeType.mtype); }
}else{
	private TypeTy theTypeTy;
	TypeTy typeTy(){ return theTypeTy?theTypeTy:(theTypeTy=new TypeTy()); }
	alias etypeTy=typeTy;
	alias utypeTy=typeTy;
	alias ctypeTy=typeTy;
	alias qtypeTy=typeTy;
}

bool isTypeTy(Expression e){ return isSubtype(e,typeTy); }
bool isType(Expression e){ return e&&isTypeTy(e.type); }

bool isEmptyTy(Expression e){ return isSubtype(e,etypeTy); }
bool isEmpty(Expression e){ return e&&isEmptyTy(e.type); }

bool isUnitTy(Expression e){ return isSubtype(e,utypeTy); }
bool isUnit(Expression e){ return e&&isUnitTy(e.type); }

bool isClassicalTy(Expression e){ return isSubtype(e,ctypeTy); }
bool isClassical(Expression e){ return e&&isClassicalTy(e.type); }

bool isQuantumTy(Expression e){
	static if(language==silq) return isSubtype(e,qtypeTy);
	else return false;
}
bool isQuantum(Expression e){ return e&&isQuantumTy(e.type); }

Expression getClassicalTy(Expression e)in{ // typeof(!x) for x:e
	assert(isType(e)||isQNumeric(e));
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
	this(){
		this.type=ctypeTy;
		setSemEvaluated();
	}
	override QNumericTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		return "qnumeric";
	}
	override bool opEquals(Object o){
		return !!cast(QNumericTy)o;
	}
	override Expression evalImpl(){ return this; }
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
	if(e.any!isEmpty) return etypeTy;
	static if(language==silq){
		if(e.any!isQNumeric) return qnumericTy;
	}
	if(e.all!isUnit) return utypeTy;
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
	if(isEmpty(e)) return utypeTy;
	if(isQNumeric(e)) return qnumericTy;
	if(isClassical(e)) return ctypeTy;
	return typeTy;
}

Expression typeOfVectorTy(Expression e,Expression num)in{
	assert(isType(e)||isQNumeric(e));
	assert(num&&isSubtype(num.type,ℕt(true)));
}do{
	if(isQNumeric(e)) return qnumericTy;
	auto nume=num.eval();
	if(isZero(nume)) return utypeTy;
	if(isEmpty(e)){
		if(isNonzero(nume)) return etypeTy;
		return utypeTy;
	}
	return e.type;
}

Expression typeOfStringTy(bool classical){ return classical?ctypeTy:typeTy; }

Expression typeOfProductTy(bool[] isConst,Id[] names,Expression dom,Expression cod,bool isSquare,bool isTuple,Annotation annotation,bool isClassical){
	return isClassical?ctypeTy:typeTy;
}
