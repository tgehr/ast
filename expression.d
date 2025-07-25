// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.expression;

import std.array, std.algorithm, std.range, std.conv, std.string, std.exception;

import ast.lexer, ast.parser, ast.scope_, ast.type, ast.declaration, util;
import util.maybe;
import util.tuple: Q=Tuple, q=tuple;
import astopt;

enum SemState{
	initial,
	started,
	passive,
	completed,
	evaluated,
	error,
}

abstract class Node{
	// debug auto cccc=0;
	Location loc;
	abstract @property string kind();

	// semantic information
	SemState sstate;

	final bool isSemStarted() const {
		return sstate >= SemState.started;
	}
	final bool isSemFinal() const {
		return sstate >= SemState.completed;
	}
	final bool isSemCompleted() const {
		return sstate >= SemState.completed && sstate < SemState.error;
	}
	final bool isSemEvaluated() const {
		return sstate == SemState.evaluated;
	}
	final bool isSemError() const {
		return sstate == SemState.error;
	}
	void setSemForceError() {
		sstate = SemState.error;
	}
	void setSemForceCompleted() {
		assert(!isSemError());
		sstate = SemState.completed;
	}
	void setSemError() {
		if(isSemError()) return;
		assert(!isSemFinal(), "expression marked as error after being analyzed");
		sstate = SemState.error;
	}
	void setSemCompleted() {
		if(isSemFinal()) return;
		// assert(!isSemFinal(), "expression already analyzed");
		sstate = SemState.completed;
	}
	void setSemEvaluated() {
		if(isSemEvaluated()) return;
		setSemCompleted();
		assert(sstate == SemState.completed);
		sstate = SemState.evaluated;
	}
}


abstract class Expression: Node{
	Expression type;
	int brackets=0;

	override void setSemCompleted() {
		if(!isSemError() && type !is this) {
			assert(type, format("completed semantic analysis of expression without type: %s %s", typeid(this).name, this));
			assert(type.isSemCompleted(), format("type not analyzed: %s", this.type));
			assert(type.isSemEvaluated(), format("type not evaluated: %s", this.type));
		}
		super.setSemCompleted();
	}

	struct CopyArgs{
		bool preserveSemantic=false;
		bool preserveMeanings=false;
	}
	abstract Expression copyImpl(CopyArgs args);
	final T copy(this T)(CopyArgs args=CopyArgs.init){
		assert(!isSemCompleted() || type.isSemEvaluated());
		auto self=cast(T)this;
		auto r=self.copyImpl(args);
		assert(!!r);
		if(r is this){
			assert(isSemEvaluated());
			return r;
		}
		assert(!r.isSemEvaluated());
		r.loc=loc;
		if(args.preserveSemantic){
			r.sstate = isSemEvaluated() ? SemState.completed : sstate;
			r.type = type;
			r.constLookup = constLookup;
		}
		r.brackets=brackets;
		r.byRef=byRef;
		r.implicitDup=implicitDup;
		return r;
	}

	override string toString(){return _brk("{}()");}
	protected string _brk(string s){return std.array.replicate("(",brackets)~(implicitDup?"dup(":"")~s~(implicitDup?")":"")~std.array.replicate(")",brackets);}

	override @property string kind(){return "expression";}
	bool isCompound(){ return false; }
	bool isConstant(){ return false; }
	bool isTotal(){ return false; }

	Maybe!ℤ asIntegerConstant(bool eval=false) {
		if(!eval) return none!(ℤ);
		if(type && (isEmpty(type) || !isSubtype(type, ℤt(true)))) return none!(ℤ);
		auto ev = this.eval();
		return ev.asIntegerConstant(false);
	}
	Maybe!(Q!(ℤ, ℤ, int, int)) asRationalConstant() {
		return none!(Q!(ℤ, ℤ, int, int));
	}
	Maybe!string asStringConstant() {
		return none!string;
	}

	final Expression eval(){
		if(isSemEvaluated()) return this;
		assert(!isSemError(), format("eval on invalid expression: %s", this));
		assert(isSemCompleted(), format("eval on unanalyzed expression: %s", this));
		auto r=evalImpl();
		if(r !is this) {
			if(!r.type) r.type=type;
			else if(r is this) return r;
			else assert(isSubtype(r.type,type), format("evaluation changed type from %s to %s; expression %s evaluated to %s", type, r.type, this, r));
			if(!r.loc.line) r.loc=loc;
		}
		r.setSemEvaluated();
		return r;
	}
	abstract Expression evalImpl();

	final Expression substitute(Id name,Expression exp){
		return substitute([name:exp]);
	}
	final Expression substitute(Expression[Id] subst){
		assert(isSemCompleted());
		auto r=substituteImpl(subst);
		if(r !is this) {
			assert(type !is this);
			assert(!r.type || r.type.isSemEvaluated(), format("eval %s -> %s, unevaluated type %s", this, r, r.type));
			if(!r.type) r.type = type.substitute(subst);
			r.setSemCompleted();
		}
		return r.eval();
	}
	abstract Expression substituteImpl(Expression[Id] subst); // TODO: name might be free in the _types_ of subexpressions

	final bool unify(Expression rhs,ref Expression[Id] subst, bool meet){
		return unifyImpl(rhs,subst,meet) || eval().unifyImpl(rhs.eval(),subst,meet);
	}
	abstract bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet);

	abstract int freeVarsImpl(scope int delegate(Identifier) dg);
	static struct FreeVars{
		Expression self;
		int opApply(scope int delegate(Identifier) dg)in{
			assert(!!self);
		}do{
			if(auto r=self.freeVarsImpl(dg)) return r;
			if(self.type && self.type !is self)
				foreach(v;self.type.freeVars())
					if(auto r=dg(v)) return r;
			return 0;
		}
	}
	final FreeVars freeVars()in{
		assert(!!this);
	}do{
		return FreeVars(this);
	}
	final bool hasFreeVar(Id id)in{
		assert(!!this);
	}do{
		foreach(var;freeVars){
			if(var.id == id)
				return true;
		}
		return false;
	}
	final bool hasFreeVar(string name){
		return hasFreeVar(Id.intern(name));
	}
	final bool hasAnyFreeVar(R)(R r){
		foreach(var;freeVars){
			if(r.canFind(var.id))
				return true;
		}
		return false;
	}
	abstract int componentsImpl(scope int delegate(Expression) dg);
	static struct Components{
		Expression self;
		bool ignoreTypes;
		int opApply(scope int delegate(Expression) dg)in{
			assert(!!self);
		}do{
			if(auto r=self.componentsImpl(dg)) return r;
			return 0;
		}
	}
	final Components components()in{
		assert(!!this);
	}do{
		return Components(this,false);
	}
	final int subexpressionsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(this)) return r;
		foreach(x;components) if(auto r=x.subexpressionsImpl(dg)) return r;
		return 0;
	}
	static struct Subexpressions{
		Expression self;
		int opApply(scope int delegate(Expression) dg)in{
			assert(!!self);
		}do{
			if(auto r=self.subexpressionsImpl(dg)) return r;
			return 0;
		}
	}
	final Subexpressions subexpressions()in{
		assert(!!this);
	}do{
		return Subexpressions(this);
	}
	bool isSubtypeImpl(Expression rhs){
		return this == rhs;
	}
	Expression combineTypesImpl(Expression rhs,bool meet){
		if(this == rhs) return this;
		return null;
	}

	ITupleTy isTupleTy(){
		return null;
	}
	Expression getClassical(){
		if(isClassical(this)) return this;
		return null;
	}
	Expression getQuantum(){
		if(isQuantum(this)) return this;
		return null;
	}
	bool mayBeClassical(){ return isClassical(this); }
	bool mayBeQuantum(){ return isQuantum(this); }

	Annotation getAnnotation(){
		return Annotation.none;
	}
	static if(language==silq){
		final bool isQfree(){ return getAnnotation()>=Annotation.qfree; }
		final bool isMfree(){ return getAnnotation()>=Annotation.mfree; }
	}else static if(language==psi){
		final bool isPure(){ return getAnnotation()>=Annotation.pure_; }
	}
	final bool isDeterministic(){ return getAnnotation()>=deterministic; }

	// semantic information
	bool constLookup=true;
	void setConstLookup(bool constLookup){ this.constLookup=constLookup; }
	bool byRef=false;
	bool implicitDup=false;
}

mixin template VariableFree(){
	override int freeVarsImpl(scope int delegate(Identifier)){ return 0; }
	override Expression substituteImpl(Expression[Id] subst){ return this; }
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		return combineTypes(this,rhs,meet)!is null;
	}
}

enum TypeAnnotationType{
	annotation,
	conversion,
	coercion,
	punning,
}

class TypeAnnotationExp: Expression{
	Expression e,t;
	TypeAnnotationType annotationType;
	this(Expression e, Expression t, TypeAnnotationType annotationType){
		this.e=e; this.t=t;
		this.annotationType=annotationType;
	}
	override TypeAnnotationExp copyImpl(CopyArgs args){
		return new TypeAnnotationExp(e.copy(args),t.copy(args),annotationType);
	}
	override @property string kind(){ return e.kind; }
	override string toString(){
		static immutable op=[": "," as "," coerce "," pun "];
		static assert(TypeAnnotationType.max==TypeAnnotationType.punning);
		return _brk(e.toString()~op[annotationType]~(type?type.toString():t.toString()));
	}
	override bool isConstant(){
		return e.isConstant() && (type ? type.isConstant() : t.isConstant());
	}
	override bool isTotal(){
		return annotationType<TypeAnnotationType.coercion && e.isTotal() && (type ? type : t).isTotal();
	}
	override Maybe!ℤ asIntegerConstant(bool eval=false) {
		if (annotationType >= TypeAnnotationType.coercion || !type || !isSubtype(type, ℤt(true)))
			return none!ℤ();
		return this.e.asIntegerConstant(eval);
	}
	override int freeVarsImpl(scope int delegate(Identifier) dg){
		if(auto r=e.freeVarsImpl(dg)) return r;
		return (type?type:t).freeVarsImpl(dg);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(e)) return r;
		return dg(type?type:t);
	}
	override TypeAnnotationExp substituteImpl(Expression[Id] subst){
		auto ne=e.substitute(subst);
		auto nt=t.substitute(subst);
		if(ne is e && nt is t) return this;
		auto r=new TypeAnnotationExp(ne, nt, annotationType);
		r.loc=loc;
		r.type=nt.eval();
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		return e.unify(rhs,subst,meet);
	}
	override bool opEquals(Object o){
		if(o is this) return true;
		auto tae=cast(TypeAnnotationExp)o;
		if(!tae) return false;
		return e==tae.e&&t==tae.t&&annotationType==tae.annotationType;
	}
	override Annotation getAnnotation(){
		return e.getAnnotation();
	}
	override Expression evalImpl(){
		auto ne = e.eval();
		if(annotationType == TypeAnnotationType.annotation || ne.type == type) {
			return ne;
		}
		if(type == ℕt(true)) {
			// `(a - b) coerce !N`  ->  `a sub b`
			auto se = cast(SubExp)ne;
			if(se && se.type == ℤt(true)) {
				return new NSubExp(se.e1, se.e2);
			}
		}
		if(ne is e && type is t) return this;
		return new TypeAnnotationExp(ne, type, annotationType);
	}
	// semantic information
	override void setConstLookup(bool constLookup){
		e.setConstLookup(constLookup);
		super.setConstLookup(constLookup);
	}
}

// workaround for the bug:
UnaryExp!(Tok!"&") isAddressExp(Expression self){return cast(UnaryExp!(Tok!"&"))self;}

class ErrorExp: Expression{
	this(){}//{setSemError();}
	override string toString(){return _brk("__error");}
	override ErrorExp copyImpl(CopyArgs args){
		return new ErrorExp();
	}

	override Expression evalImpl(){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}

class LiteralExp: Expression{
	Token lit; // TODO: add literal expressions with dedicated types
	this(Token lit){ // TODO: suitable contract
		this.lit=lit;
	}
	static LiteralExp makeInteger(T)(T i)if(text(T.init)=="0"){
		Token tok;
		tok.type=Tok!"0";
		tok.str=text(i);
		auto r=new LiteralExp(tok);
		r.type=i>=0?(i<=1?Bool(true):ℕt(true)):ℤt(true);
		r.setSemEvaluated();
		return r;
	}
	static LiteralExp makeString(string s, Location loc=Location.init){
		Token tok;
		tok.type=Tok!"``";
		tok.str=s;
		auto r=new LiteralExp(tok);
		r.type=stringTy();
		r.loc=loc;
		r.setSemEvaluated();
		return r;
	}
	static LiteralExp makeBoolean(bool b){
		auto r=makeInteger(b?1:0);
		r.type=Bool(true);
		return r;
	}
	override LiteralExp copyImpl(CopyArgs args){
		auto r=new LiteralExp(lit);
		r.type=type;
		return r;
	}
	override string toString(){
		return _brk(lit.toString());
	}
	override bool isConstant(){
		assert(type);
		return type.isConstant();
	}
	override bool isTotal(){
		assert(type);
		return type.isTotal();
	}

	override Maybe!ℤ asIntegerConstant(bool eval=false) {
		if(lit.type!=Tok!"0") return none!(ℤ);
		return just(ℤ(lit.str));
	}
	// returns (x, y, b, n) where the value is x/y * b**n; y > 0, b > 0
	override Maybe!(Q!(ℤ, ℤ, int, int)) asRationalConstant() {
		if(lit.type == Tok!"0") return just(q(ℤ(lit.str), ℤ(1), 1, 0));
		if(lit.type != Tok!".0") return none!(Q!(ℤ, ℤ, int, int));

		int base = 10;
		int exp = 0;
		string numPart = lit.str;
		auto e = lit.str.find("e");
		if(e.length > 0) {
			numPart = lit.str[0..(e.ptr - lit.str.ptr)];
			exp = e[1..$].to!int(); // TODO overflow
		}

		string intPart = numPart, fracPart = "";
		auto dot = numPart.find(".");
		if(dot.length > 0) {
			intPart = lit.str[0..(dot.ptr - numPart.ptr)];
			fracPart = dot[1..$];
		}
		exp -= fracPart.length;

		return just(q(ℤ(intPart ~ fracPart), ℤ(1), base, exp));
	}
	override Maybe!string asStringConstant() {
		if(lit.type != Tok!"``") return none!string;
		return just(lit.str);
	}

	override bool opEquals(Object o){
		if(o is this) return true;
		auto r=cast(LiteralExp)o;
		if(!r) return false;
		if(lit.type!=r.lit.type) return false;
		switch(lit.type){
			case Tok!"0":
				return lit.str==r.lit.str;
			default:
				return this is r;
		}
	}

	override Annotation getAnnotation(){ return pure_; }
	override Expression evalImpl(){
		return this;
	}
	override int componentsImpl(scope int delegate(Expression) dg){ return 0; }
	mixin VariableFree;
}

bool isZero(Expression e, bool eval=false){
	assert(e.isSemFinal());
	if(!e.type) return false;
	assert(isNumericTy(e.type)||isEmpty(e.type));
	if(auto v = e.asIntegerConstant(eval))
		return v.get() == 0;
	return false;
}
bool isOne(Expression e, bool eval=false){
	assert(e.isSemFinal());
	if(!e.type) return false;
	assert(isNumericTy(e.type)||isEmpty(e.type));
	if(auto v = e.asIntegerConstant(eval))
		return v.get() == 1;
	return false;
}
bool isNonzero(Expression e, bool eval=false){
	assert(e.isSemFinal());
	if(!e.type) return false;
	assert(isNumericTy(e.type)||isEmpty(e.type));
	if(auto v = e.asIntegerConstant(eval))
		return v.get() != 0;
	return false;
}
bool isPositive(Expression e, bool eval=false){
	assert(e.isSemFinal());
	if(!e.type) return false;
	assert(isNumericTy(e.type)||isEmpty(e.type));
	if(auto v = e.asIntegerConstant(eval))
		return v.get() > 0;
	return false;
}
bool isFalse(Expression e, bool eval=false){
	assert(e.isSemFinal());
	if(!e.type) return false;
	assert(isNumericTy(e.type) == NumericType.Bool||isEmpty(e.type));
	return isZero(e, eval);
}
bool isTrue(Expression e, bool eval=false){
	assert(e.isSemFinal());
	if(!e.type) return false;
	assert(isNumericTy(e.type) == NumericType.Bool||isEmpty(e.type));
	return isOne(e, eval);
}

struct Id {
	static __gshared Id[string] interned;
	size_t raw = 0;

	@property
	size_t length() const pure @trusted nothrow {
		pragma(inline, true);
		if(!raw) return 0;
		return *cast(immutable(size_t)*)(raw - size_t.sizeof);
	}

	@property
	immutable(char)* ptr() const pure @trusted nothrow {
		pragma(inline, true);
		return cast(immutable(char)*)raw;
	}

	@property
	string str() const pure @trusted nothrow {
		pragma(inline, true);
		if(!raw) return null;
		size_t len = *cast(immutable(size_t)*)(raw - size_t.sizeof);
		return (cast(immutable(char)*)raw)[0..len];
	}

	template s(string v) {
		__gshared static immutable Id s;
		shared static this() {
			s = intern(v);
		}
	}

	static Id intern(string s) @trusted {
		// TODO make thread-safe?
		import core.stdc.stdlib: malloc;
		import core.stdc.string: memcpy;
		size_t len = s.length;
		if(len == 0) return Id();
		if(auto p = s in interned) {
			assert((*p).str == s);
			return *p;
		}
		auto mem = malloc(size_t.sizeof + len);
		assert(mem);
		*cast(size_t*)mem = len;
		auto p = cast(char*)mem + size_t.sizeof;
		memcpy(p, s.ptr, len);
		auto id = Id(cast(size_t)p);
		s = (cast(immutable(char)*)p)[0..len];
		interned[s] = id;
		return id;
	}

	bool opCast(T: bool)() const pure @safe nothrow {
		return !!raw;
	}

	bool opEquals(Id other) const pure @safe nothrow {
		return raw == other.raw;
	}

	ulong toHash() const pure @safe nothrow {
		return hashOf(raw);
	}

	string toString() const pure @safe nothrow {
		return str;
	}

	Id apos() @safe {
		assert(!!raw);
		return Id.intern(str ~ "'");
	}
}

class Identifier: Expression{
	Id id;
	@property string name(){return id.str;}
	@property auto ptr(){return id.ptr;}
	@property auto length(){return id.length;}
	this(Id id){
		this.id=id;
	}
	this(string name){
		this(Id.intern(name));
	}
	override Identifier copyImpl(CopyArgs args){
		Identifier r;
		bool resetName(){
			if(!meaning||!meaning.name||!meaning.name.name.length) return false;
			if(args.preserveSemantic||args.preserveMeanings) return false;
			return true;
		}
		if(resetName())
			r=new Identifier(meaning.name.id); // TODO: this is a hack
		else r=new Identifier(id);
		if(args.preserveSemantic){
			r.meaning=meaning;
			r.scope_=scope_;
			r.calledDirectly=calledDirectly;
			r.indexedDirectly=indexedDirectly;
			static if(language==silq){
				r.outerWanted=outerWanted;
				r.classical=classical;
			}
		}else{
			if(args.preserveMeanings){
				r.meaning=meaning;
			}
			static if(language==silq){
				r.outerWanted=outerWanted;
				r.classical=classical;
			}
		}
		return r;
	}
	override string toString(){
		static if(language==silq) return _brk((classical?"!":"")~name);
		else return _brk(name);
	}
	override @property string kind(){return "identifier";}

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		return dg(this);
	}
	override int componentsImpl(scope int delegate(Expression) dg){ return 0; }
	override Expression substituteImpl(Expression[Id] subst){
		assert(constLookup || implicitDup, format("consume in eval() expression: %s", this));
		if(id in subst){
			auto result=subst[id];
			assert(result.isSemCompleted());
			static if(language==silq){
				if(classical) {
					return result.eval().getClassical();
				}
			}
			if(constLookup!=result.constLookup && !type.isClassical() || implicitDup && !result.implicitDup){
				Expression.CopyArgs cargs={preserveSemantic: true};
				result=result.copy(cargs); // TODO: avoid multiple copies in same substitute call?
				if(constLookup != result.constLookup&& !type.isClassical()) result.setConstLookup(constLookup);
				if(implicitDup) result.implicitDup=true;
			}
			assert(constLookup == result.constLookup || type.isClassical(), "bad setConstLookup");
			return result;
		}
		return this;
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		if(this==rhs){
			if(id !in subst) return true;
			if(subst[id]&&subst[id]!=this) return false;
			subst[id]=this;
			return true;
		}
		if(id !in subst) return false;
		if(subst[id]==this) return false;
		static if(language==silq){
			if(isType(this)&&isType(rhs))
				if(rhs.isClassical<classical) return false;
		}
		if(subst[id]){
			if(!subst[id].unify(rhs,subst,meet))
				return false;
			if((isType(subst[id])||isQNumeric(subst[id]))&&(isType(rhs)||isQNumeric(rhs)))
				if(auto cmb=combineTypes(subst[id],rhs,meet)) // TODO: good?
					subst[id]=cmb;
			return true;
		}
		if(rhs.hasFreeVar(id)) return false; // TODO: fixpoint types
		subst[id]=rhs;
		return true;
	}
	override bool opEquals(Object o){
		if(o is this) return true;
		if(auto r=cast(Identifier)o){
			if(id==r.id && isClassical(this)==isClassical(r) && meaning==r.meaning) {
				if(meaning) {
					assert(type == r.type);
					return true;
				}
				// In product types we have `Identifier`s without a `meaning`. Compare their types instead.
				return type == r.type;
			}
		}
		return false;
	}
	override bool isSubtypeImpl(Expression rhs){
		if(auto r=cast(Identifier)rhs){
			if(id==r.id && (isClassical(this)||!isClassical(r)) && meaning==r.meaning)
				return true;
		}
		return false;
	}
	override Expression combineTypesImpl(Expression rhs, bool meet){
		if(auto r=cast(Identifier)rhs){
			if(id==r.id && meaning==r.meaning){
				if(!isClassical(this)^meet) return this;
				if(!isClassical(r)^meet) return rhs;
				return this;
			}
		}
		return null;
	}
	override Expression getClassical(){
		assert(isSemEvaluated());
		static if(language==silq){
			if(auto r=super.getClassical()) return r;
			assert(isType(this)||isQNumeric(this));
			if(classical) return this;
			if(!meaning) return varTy(id,ctypeTy,true);
			auto r=new Identifier(id);
			r.classical=true;
			r.type=getClassicalTy(type);
			r.meaning=meaning;
			r.scope_=scope_;
			r.constLookup=constLookup;
			r.implicitDup=implicitDup;
			r.setSemEvaluated();
			return r;
		}else return this;
	}
	override Expression getQuantum(){
		assert(isSemEvaluated());
		static if(language==silq){
			assert(isType(this)||isQNumeric(this));
			if(isQuantum(this)) return this;
			if(meaning){
				import ast.semantic_:typeForDecl;
				auto prev=typeForDecl(meaning);
				if(isQuantumTy(prev)){
					auto r=new Identifier(id);
					r.classical=false;
					r.meaning=meaning;
					r.scope_=scope_;
					r.constLookup=constLookup;
					r.implicitDup=implicitDup;
					r.type=r.typeFromMeaning;
					assert(isQuantumTy(r.type));
					r.setSemEvaluated();
					return r;
				}
			}
			return null;
		}else return null;
	}
	override bool mayBeClassical(){
		return isType(this); // could be substituted with unit type
	}
	override bool mayBeQuantum(){
		return isType(this); // could be substituted with unit type
	}

	final Expression typeFromMeaning(Declaration meaning){
		if(!meaning) return null;
		import ast.semantic_:typeForDecl;
		auto r=typeForDecl(meaning);
		if((isType(r)||isQNumeric(r))&&classical) return getClassicalTy(r);
		return r;
	}
	final Expression typeFromMeaning(){
		return typeFromMeaning(meaning);
	}

	override Annotation getAnnotation(){ return pure_; }

	override Expression evalImpl(){
		if(auto init=getInitializer()) {
			return init;
		}
		return this;
	}
	override bool isConstant(){
		if(auto init=getInitializer())
			return init.isConstant();
		if(auto fd=cast(FunctionDef)meaning){
			if(!fd.isNested){
				assert(!fd.capturedDecls);
				return true;
			}
		}
		return super.isConstant();
	}
	override bool isTotal(){
		if(auto init=getInitializer())
			return init.isTotal();
		return true;
	}
	Expression getInitializer(){
		auto vd=cast(VarDecl)meaning;
		if(!vd) return null;
		assert(vd.isSemFinal());
		auto init=vd.initializer;
		if(vd.isSemError()||!init) return null;
		if(cast(TopScope)vd.scope_ || isTypeTy(vd.vtype) || isQNumeric(vd.vtype)){
			init = init.eval();
			return classical?init.getClassical():init;
		} else {
			return null;
		}
	}
	// semantic information:
	override void setConstLookup(bool constLookup){
		if(this.constLookup==constLookup) return;
		implicitDup=true;
		this.constLookup=false;
	}
	Declaration meaning;
	bool lazyCapture=false;
	Scope scope_;
	bool calledDirectly=false;
	bool indexedDirectly=false;
	static if(language==silq){
		bool outerWanted=true; // (use user friendly type of result of adapted reverse result)
		bool classical=false;
	}
	else enum classical=false;
	Identifier[] recaptures;
}

class PlaceholderExp: Expression{
	Identifier ident;
	this(Identifier ident){ this.ident = ident; }
	override PlaceholderExp copyImpl(CopyArgs args){
		return new PlaceholderExp(ident.copy(args));
	}
	override string toString(){ return _brk("?"); }
	override @property string kind(){ return "placeholder"; }

	override Expression evalImpl(){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){ return 0; }
}

class WildcardExp: Expression{
	this(){}
	override WildcardExp copyImpl(CopyArgs args){
		return new WildcardExp();
	}
	override string toString(){ return _brk("_"); }
	override @property string kind(){ return "wildcard"; }

	override Expression evalImpl(){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){ return 0; }
}

class TypeofExp: Expression{
	Expression e;
	this(Expression e){ this.e=e; }
	override TypeofExp copyImpl(CopyArgs args){
		return new TypeofExp(e.copy(args));
	}
	override string toString(){ return _brk("typeof("~e.toString~")"); }
	override @property string kind(){ return "typeof"; }

	override Expression evalImpl(){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){ return dg(e); }
}

abstract class AUnaryExp: Expression{
	Expression e;
	this(Expression next){e = next;}
}

class UnaryExp(TokenType op): AUnaryExp{
	this(Expression next){ super(next); }
	override UnaryExp!op copyImpl(CopyArgs args){
		return new UnaryExp!op(e.copy(args));
	}
	override string toString(){
		import std.uni;
		return _brk(TokChars!op~(TokChars!op[$-1].isAlpha()?" ":"")~e.toString());
	}
	static if(op==Tok!"&"){
		override @property string kind(){
			return "address";
		}
		//override UnaryExp!(Tok!"&") isAddressExp(){return this;}
	}
	override bool isConstant(){ return e.isConstant(); }
	override bool isTotal(){ return e.isTotal(); }

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		return e.freeVarsImpl(dg);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(e);
	}
	override UnaryExp substituteImpl(Expression[Id] subst){
		auto ne=e.substitute(subst);
		if(ne==e) return this;
		auto r=new UnaryExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		auto ue=cast(typeof(this))rhs;
		if(!ue) return false;
		return e.unify(ue.e,subst,meet);
	}
	override bool opEquals(Object o){
		if(o is this) return true;
		auto ue=cast(UnaryExp!op)o;
		return ue&&e==ue.e;
	}

	override Annotation getAnnotation(){ return e.getAnnotation(); }

	override Expression evalImpl(){
		auto ne=e.eval();
		if(isNumericTy(type)) {
			static if(op==Tok!"-"){
				if(auto v=ne.asIntegerConstant()){
					return LiteralExp.makeInteger(-v.get());
				}
			}
		}
		if(ne is e) return this;
		return new UnaryExp!op(ne);
	}
}
class PostfixExp(TokenType op): Expression{
	Expression e;
	this(Expression next){e = next;}
	override PostfixExp!op copyImpl(CopyArgs args){
		return new PostfixExp!op(e.copy(args));
	}
	override string toString(){return _brk(e.toString()~TokChars!op);}

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		return e.freeVarsImpl(dg);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(e);
	}
	override PostfixExp substituteImpl(Expression[Id] subst){
		auto ne=e.substitute(subst);
		if(ne==e) return this;
		auto r=new PostfixExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		auto pe=cast(PostfixExp)rhs;
		if(!pe) return false;
		return e.unify(pe.e,subst,meet);
	}

	override Expression evalImpl(){
		auto ne=e.eval();
		if(ne is e) return this;
		return new PostfixExp!op(ne);
	}
}

class IndexExp: Expression{ //e[a]
	Expression e;
	Expression a;
	bool isArraySyntax=false; // e[] vs e[()]
	this(Expression exp, Expression arg){e=exp; a=arg;}
	override IndexExp copyImpl(CopyArgs args){
		auto r=new IndexExp(e.copy(args),a.copy(args));
		r.isArraySyntax=isArraySyntax;
		return r;
	}
	override string toString(){
		return _brk(e.toString()~a.tupleToString(true));
	}
	override Expression evalImpl(){
		auto ne=e.eval();
		auto na=a.eval();
		Expression[] exprs;
		if(auto tpl=cast(TupleExp)ne) exprs=tpl.e;
		if(auto vec=cast(VectorExp)ne) exprs=vec.e;
		if(exprs.length){
			if(auto v=na.asIntegerConstant()){
				auto idx=v.get();
				if(0<=idx&&idx<exprs.length) return exprs[cast(size_t)idx].eval();
			}
		}
		if(ne is e && na is a) return this;
		auto r=new IndexExp(ne,na);
		r.isArraySyntax=isArraySyntax;
		return r;
	}
	override int freeVarsImpl(scope int delegate(Identifier) dg){
		if(auto r=e.freeVarsImpl(dg)) return r;
		if(auto r=a.freeVarsImpl(dg)) return r;
		return 0;
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(e)) return r;
		if(auto r=dg(a)) return r;
		return 0;
	}
	override IndexExp substituteImpl(Expression[Id] subst){
		auto ne=e.substitute(subst);
		auto na=a.substitute(subst);
		if(ne==e&&na==a) return this;
		auto r=new IndexExp(ne,na);
		r.isArraySyntax=isArraySyntax;
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		auto idx=cast(IndexExp)rhs;
		if(!idx) return false;
		return e.unify(idx.e,subst,meet)&&a.unify(idx.a,subst,meet);
	}
	override bool opEquals(Object rhs){
		if(rhs is this) return true;
		auto idx=cast(IndexExp)rhs;
		return idx&&idx.e==e&&idx.a==a;
	}

	override Annotation getAnnotation(){ return min(e.getAnnotation(), a.getAnnotation()); }
}

class SliceExp: Expression{
	Expression e;
	Expression l,r;
	this(Expression exp, Expression left,Expression right){e=exp; l=left; r=right; }
	override SliceExp copyImpl(CopyArgs args){
		return new SliceExp(e.copy(args),l.copy(args),r.copy(args));
	}
	override string toString(){
		return _brk(e.toString()~'['~l.toString()~".."~r.toString()~']');
	}
	override Expression evalImpl(){
		auto ne=e.eval(), nl=l.eval(), nr=r.eval();
		Expression[] exprs;
		auto tpl=cast(TupleExp)ne, vec=cast(VectorExp)ne;
		if(tpl) exprs=tpl.e;
		if(vec) exprs=vec.e;
		if(tpl||vec){
			if(auto lv=nl.asIntegerConstant()){
				if(auto rv=nr.asIntegerConstant()){
					auto lid=lv.get(), rid=rv.get();
					if(cast(size_t)lid==0 && cast(size_t)rid==exprs.length) return e;
					if(0<=lid&&lid<=rid&&rid<=exprs.length){
						auto rexprs=exprs[cast(size_t)lid..cast(size_t)rid];
						if(tpl){
							auto res=new TupleExp(rexprs);
							res.loc=loc;
							return res;
						}
						if(vec){
							auto res=new VectorExp(rexprs);
							res.loc=loc;
							return res;
						}
					}
				}
			}
		}
		if(ne is e && nl is l && nr is r) return this;
		return new SliceExp(ne,nl,nr);
	}
	override int freeVarsImpl(scope int delegate(Identifier) dg){
		if(auto x=e.freeVarsImpl(dg)) return x;
		if(auto x=l.freeVarsImpl(dg)) return x;
		if(auto x=r.freeVarsImpl(dg)) return x;
		return 0;
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto x=dg(e)) return x;
		if(auto x=dg(l)) return x;
		if(auto x=dg(r)) return x;
		return 0;
	}
	override SliceExp substituteImpl(Expression[Id] subst){
		auto ne=e.substitute(subst);
		auto nl=l.substitute(subst);
		auto nr=r.substitute(subst);
		if(ne is e && nl is l && nr is r) return this;
		auto res=new SliceExp(ne,nl,nr);
		res.loc=loc;
		return res;
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		auto sl=cast(SliceExp)rhs;
		return e.unify(sl.e,subst,meet)&&l.unify(sl.l,subst,meet)&&r.unify(sl.r,subst,meet);
	}
	override bool opEquals(Object rhs){
		if(rhs is this) return true;
		auto sl=cast(SliceExp)rhs;
		return e == sl.e && l == sl.l && r == sl.r;
	}

	override Annotation getAnnotation(){ return min(e.getAnnotation(), l.getAnnotation(), r.getAnnotation()); }
}

string tupleToString(Expression e,bool isSquare){
	auto d=isSquare?"[]":"()";
	bool isTuple=!!cast(TupleExp)e;
	auto str=e.toString();
	if(isTuple||e.brackets){
		assert(str[0]=='(' && str[$-1]==')');
		str=str[1..$-1];
	}
	return d[0]~str~d[1];
}

class CallExp: Expression{
	Expression e;
	Expression arg;
	bool isSquare;
	static if(language==silq) bool isClassical_;
	else enum isClassical_=true;
	this(Expression exp, Expression arg, bool isSquare, bool isClassical_)in{
		assert(exp&&arg);
	}do{
		e=exp; this.arg=arg; this.isSquare=isSquare;
		static if(language==silq) this.isClassical_=isClassical_;
	}
	override CallExp copyImpl(CopyArgs args){
		auto r=new CallExp(e.copy(args),arg.copy(args),isSquare,isClassical_);
		static if(language==silq) r.checkReverse=checkReverse;
		return r;
	}
	override string toString(){
		static if(language==silq) return _brk((isClassical_?"!":"")~e.toString()~arg.tupleToString(isSquare));
		else return _brk(e.toString()~arg.tupleToString(isSquare));
	}
	override int freeVarsImpl(scope int delegate(Identifier) dg){
		if(auto r=e.freeVarsImpl(dg)) return r;
		return arg.freeVarsImpl(dg);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(e)) return r;
		return dg(arg);
	}
	override CallExp substituteImpl(Expression[Id] subst){
		auto ne=e.substitute(subst);
		auto narg=arg.substitute(subst);
		if(ne==e&&narg==arg) return this;
		auto r=new CallExp(ne,narg,isSquare,isClassical_);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		auto ce=cast(CallExp)rhs;
		if(!ce) return false;
		return e.unify(ce.e,subst,meet)&&arg.unify(ce.arg,subst,meet);
	}
	override bool opEquals(Object rhs){
		if(rhs is this) return true;
		auto ce=cast(CallExp)rhs;
		if(!ce) return false;
		return e==ce.e&&arg==ce.arg&&isSquare==ce.isSquare&&isClassical_==ce.isClassical_;
	}
	override bool isSubtypeImpl(Expression rhs){
		if(this == rhs) return true;
		auto rcall = cast(CallExp)rhs;
		if(rcall && isType(this) && isType(rhs) && e==rcall.e && isSquare==rcall.isSquare){
			if(!isClassical_ && rcall.isClassical_) return false;
			if(auto id=cast(Identifier)e){
				if(id.meaning){
					if(auto dat=cast(DatDecl)id.meaning){
						auto rid=cast(Identifier)rcall.e;
						assert(rid && rid.meaning == dat);
						bool check(Variance variance,Expression t1,Expression t2){
							final switch(variance){
								case Variance.invariant_: return t1==t2;
								case Variance.covariant: return isSubtype(t1,t2);
								case Variance.contravariant: return isSubtype(t2,t1);
							}
						}
						if(!dat.isTuple){
							assert(dat.params.length==1);
							return check(dat.params[0].variance,arg,rcall.arg);
						}
						assert(dat.isTuple);
						auto tup=arg.isTupleTy(), rtup=rcall.arg.isTupleTy();
						if(tup && rtup && tup.length==dat.params.length && tup.length==rtup.length){ // TODO: assert this?
							return iota(tup.length).all!(i=>check(dat.params[i].variance,tup[i],rtup[i]));
						}
					}
				}
			}
		}
		return super.isSubtypeImpl(rhs);
	}
	override Expression combineTypesImpl(Expression rhs, bool meet){
		if(this == rhs) return this;
		auto rcall = cast(CallExp)rhs;
		if(rcall && isType(type) && isType(rhs) && e==rcall.e && isSquare==rcall.isSquare){
			if(e==rcall.e&&arg==rcall.arg){
				if(isClassical_ && !rcall.isClassical_){
					return meet?this:rcall;
				}else{
					assert(rcall.isClassical_ && !isClassical_);
					return !meet?this:rcall;
				}
			}
			if(auto id=cast(Identifier)e){
				if(id.meaning){
					if(auto dat=cast(DatDecl)id.meaning){
						auto rid=cast(Identifier)rcall.e;
						assert(rid && rid.meaning == dat);
						Expression combine(Variance variance,Expression t1,Expression t2){
							final switch(variance){
								case Variance.invariant_: return t1==t2 ? t1 : null;
								case Variance.covariant: return combineTypes(t1,t2,meet);
								case Variance.contravariant: return combineTypes(t1,t2,!meet);
							}
						}
						import ast.semantic_: ExpSemContext, callSemantic; // TODO: get rid of this?
						if(!dat.isTuple){
							assert(dat.params.length==1);
							assert(arg != rcall.arg); // (checked at start of function)
							auto combined=combine(dat.params[0].variance,arg,rcall.arg);
							if(!combined) return null;
							return callSemantic(new CallExp(e,combined,isSquare,isClassical_), ExpSemContext.forType(null));
						}
						assert(dat.isTuple);
						auto tup=arg.isTupleTy(), rtup=rcall.arg.isTupleTy();
						if(tup && rtup && tup.length==dat.params.length && tup.length==rtup.length){ // TODO: assert this?
							auto combined=iota(tup.length).map!(i=>combine(dat.params[i].variance,tup[i],rtup[i])).array;
							if(combined.any!(x=>x is null)) return null;
							auto rarg=new TupleExp(combined);
							return callSemantic(new CallExp(e,rarg,isSquare,isClassical_), ExpSemContext.forType(null));
						}
					}
				}
			}
		}
		return super.combineTypesImpl(rhs,meet);
	}
	override Expression getClassical(){
		assert(isSemEvaluated());
		static if(language==silq){
			assert(isType(this), format("call not a type: %s", this));
			if(auto r=super.getClassical()) return r;
			auto r=new CallExp(e,arg,isSquare,true);
			r.type=getClassicalTy(type);
			r.setSemEvaluated();
			return r;
		}else return this;
	}
	override Expression getQuantum(){
		assert(isSemEvaluated());
		static if(language==silq){
			assert(isType(this), format("call not a type: %s", this));
			if(isFixedIntTy(this)){ // TODO: generalize
				auto r=new CallExp(e,arg,isSquare,false);
				r.type=qtypeTy;
				r.setSemEvaluated();
				return r;
			}
			return null;
		}else return null;
	}
	override bool mayBeClassical(){
		return super.mayBeClassical()||isType(this); // may evaluate to unit type
	}
	override bool mayBeQuantum(){
		return super.mayBeQuantum()||isType(this); // may evaluate to unit type
	}

	override Annotation getAnnotation(){
		auto fty=cast(FunTy)e.type;
		if(!fty) return Annotation.none;
		return min(e.getAnnotation(),fty.annotation,arg.getAnnotation());
	}

	final private Expression isDup(){
		import ast.semantic_:isPreludeSymbol;
		static if(language==silq) {
			if(isSquare || isClassical_) return null;
			auto ce2=cast(CallExp)e;
			if(!ce2) return null;
			if(!ce2.isSquare || ce2.isClassical_) return null;
			auto id=cast(Identifier)ce2.e;
			if(!id) return null;
			if(isPreludeSymbol(id)!="dup") return null;
			return arg;
		} else {
			return null;
		}
	}

	override bool isConstant(){
		if(type.isClassical()) {
			if(auto e = isDup()) {
				return e.isConstant();
			}
		}
		import ast.type:isFixedIntTy;
		if(auto ft=isFixedIntTy(this))
			return ft.bits.isConstant();
		return super.isConstant();
	}

	override Expression evalImpl(){
		auto ne=e.eval(), narg=arg.eval();
		CallExp r;
		if(ne is e && narg is arg) r=this;
		else r=new CallExp(ne,narg,isSquare,isClassical_);
		// TODO: partially evaluate arbitrary functions
		if(type.isClassical() || constLookup) {
			if(auto sub=r.isDup()) return sub.eval(); // TODO: ok?
		}
		return r;
	}
	// semantic information
	static if(language==silq){
		bool checkReverse=true; // (calls to reverse in the frontend implementation of reverse are more liberal)
	}
}

abstract class ABinaryExp: Expression{
	Expression e1,e2;
	this(Expression left, Expression right){e1=left; e2=right;}
	override bool isConstant(){
		return e1.isConstant() && e2.isConstant();
	}
	override int freeVarsImpl(scope int delegate(Identifier) dg){
		if(auto r=e1.freeVarsImpl(dg)) return r;
		if(auto r=e2.freeVarsImpl(dg)) return r;
		return 0;
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(e1)) return r;
		if(auto r=dg(e2)) return r;
		return 0;
	}
	override Annotation getAnnotation(){
		return min(e1.getAnnotation(), e2.getAnnotation());
	}
}

abstract class ALogicExp: ABinaryExp{
	this(Expression left,Expression right){super(left,right);}

	// semantic information
	BlockScope blscope_;
	BlockScope forgetScope;
}

abstract class AAssignExp: ABinaryExp{
	this(Expression left,Expression right){super(left,right);}

	// semantic information
	static struct Replacement{
		Declaration previous;
		Declaration new_;
	}
	Replacement[] replacements;
}

private bool isLogicToken(TokenType op){ return op==Tok!"&&"||op==Tok!"||"; }
template BinaryExpParent(TokenType op)if(isLogicToken(op)){ alias BinaryExpParent = ALogicExp; }
private bool isAssignToken(TokenType op){ return TokenTypeToString(op).endsWith("←"); }
template BinaryExpParent(TokenType op)if(isAssignToken(op)){ alias BinaryExpParent = AAssignExp; }
template BinaryExpParent(TokenType op)if(!isAssignToken(op)&&!isLogicToken(op)){ alias BinaryExpParent = ABinaryExp; }
class BinaryExp(TokenType op): BinaryExpParent!op{
	static if(op==Tok!"→"){
		Annotation annotation;
		bool isLifted;
		this(Expression left, Expression right,Annotation annotation,bool isLifted){
			super(left,right); this.annotation=annotation; this.isLifted=isLifted;
		}
		override BinaryExp!op copyImpl(CopyArgs args){
			return new BinaryExp!op(e1.copy(args),e2.copy(args),annotation,isLifted);
		}
	}else{
		this(Expression left, Expression right){super(left,right);}
		override BinaryExp!op copyImpl(CopyArgs args){
			return new BinaryExp!op(e1.copy(args),e2.copy(args));
		}
	}
	override string toString(){
		return _brk(e1.toString() ~ " "~TokChars!op~" "~e2.toString());
	}
	override bool isTotal(){
		static if(op==Tok!"sub"||op==Tok!"sub←"){
			return false;
		}else{
			static if(op==Tok!"/"||op==Tok!"div"||op==Tok!"%"||op==Tok!"/←"||op==Tok!"div←"||op==Tok!"%←"){
				if(!isNonzero(e2, true))
					return false;
			}else static if(op!=Tok!":="&&op!=Tok!"←"&&op!=Tok!"="&&op!=Tok!"≠"&&op!=Tok!"<"&&op!=Tok!"≤"&&op!=Tok!">"&&op!=Tok!"≥"){
				if(isNumericTy(type) >= NumericType.ℝ){
					// floats can overflow and we disallow inf/nan
					// TODO: ℝ,ℂ not necessarily implemented using floats
					return false;
				}
			}
			return e1.isTotal()&&e2.isTotal();
		}
	}
	//override string toString(){return e1.toString() ~ " "~ e2.toString~TokChars!op;} // RPN
	static if(op==Tok!":="){
		override @property string kind(){ return "variable declaration"; }
		override void setSemError(){
			foreach(decl;&varDecls)
				if(decl) decl.setSemError();
			super.setSemError();
		}

		int varDecls(scope int delegate(VarDecl) dg){
			if(auto id=cast(Identifier)e1){
				auto decl=cast(VarDecl)id.meaning;
				return dg(decl);
			}
			if(auto tpl1=cast(TupleExp)e1){
				foreach(e;tpl1.e){
					auto id=cast(Identifier)e;
					if(!id) continue;
					auto decl=cast(VarDecl)id.meaning;
					if(auto r=dg(decl)) return r;
				}
				return 0;
			}
			if(auto ce=cast(CallExp)e1){
				auto ft=cast(ProductTy)ce.e.type;
				if(!ft||ft.isSquare!=ce.isSquare)
					return 0;
				if(auto id=cast(Identifier)ce.arg){
					if(iota(ft.nargs).all!(i=>!ft.isConstForReverse[i])){
						auto decl=cast(VarDecl)id.meaning;
						return dg(decl);
					}
					return 0;
				}
				if(auto tpl=cast(TupleExp)ce.arg){
					if(!ft.isTuple||ft.nargs==tpl.length){
						auto movedIndices=iota(tpl.length).filter!(i=>!ft.isConstForReverse[ft.isTuple?i:0]);
						foreach(i;movedIndices){
							auto id=cast(Identifier)tpl.e[i];
							if(!id) continue;
							auto decl=cast(VarDecl)id.meaning;
							if(auto r=dg(decl)) return r;
						}
					}
					return 0;
				}
			}
			if(auto ce=cast(CatExp)e1){
				import ast.semantic_:unwrap;
				if(auto id1=cast(Identifier)unwrap(ce.e1))
					if(auto r=dg(cast(VarDecl)id1.meaning))
					   return r;
				if(auto id2=cast(Identifier)unwrap(ce.e2))
					if(auto r=dg(cast(VarDecl)id2.meaning))
					   return r;
			}
			return 0;
		}
	}
	override BinaryExp!op substituteImpl(Expression[Id] subst){
		auto ne1=e1.substitute(subst);
		auto ne2=e2.substitute(subst);
		if(ne1==e1&&ne2==e2) return this;
		static if(op==Tok!"→"){
			auto r=new BinaryExp!op(ne1,ne2,annotation,isLifted);
		}else{
			auto r=new BinaryExp!op(ne1,ne2);
		}
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		auto be=cast(typeof(this))rhs;
		if(!be) return false;
		return e1.unify(be.e1,subst,meet)&&e2.unify(be.e2,subst,meet);
	}

	override Expression evalImpl(){
		import ast.consteval;

		auto ne1 = e1.eval(), ne2 = e2.eval();
		static if(op == Tok!"~"){
			auto ok1=false,ok2=false;
			Expression[] es1=[],es2=[];
			if(auto tpl1=cast(TupleExp)e1){ ok1=true; es1=tpl1.e; }
			if(auto vec1=cast(VectorExp)e1){ ok1=true; es1=vec1.e; }
			if(auto tpl2=cast(TupleExp)e2){ ok2=true; es2=tpl2.e; }
			if(auto vec2=cast(VectorExp)e2){ ok2=true; es2=vec2.e; }
			if(ok1 && ok2) return new TupleExp(es1 ~ es2);
		} else static if(util.among(op, Tok!"+", Tok!"-", Tok!"sub", Tok!"·", Tok!"^", Tok!"=", Tok!"≠")){
			if(isNumericTy(e1.type) && isNumericTy(e2.type)) {
				assert(isNumericTy(type));
				auto v1 = ne1.asIntegerConstant(), v2 = ne2.asIntegerConstant();
				Expression e = evalNumericBinop!op(loc, ne1, v1, ne2, v2);
				if(e) {
					assert(e.type);
					assert(isNumericTy(e.type));
					if(!isSubtype(e.type, type)) {
						e = new TypeAnnotationExp(e, type, TypeAnnotationType.coercion);
						e.type = type;
						e.loc = loc;
						e.setSemCompleted();
						e = e.eval();
					}
					return e;
				}
			}
		}
		if(ne1 is e1 && ne2 is e1) return this;
		static if(op == Tok!"→") {
			return new BinaryExp!op(ne1, ne2, annotation, isLifted);
		} else {
			return new BinaryExp!op(ne1, ne2);
		}
	}

	override bool opEquals(Object o){
		if(o is this) return true;
		auto be=cast(BinaryExp!op)o;
		return be && e1==be.e1&&e2==be.e2;
	}
	// semantic information
	static if(op==Tok!":="){
		bool isSwap=false;
		AAssignExp.Replacement[] replacements;
	}
	static if(isAssignToken(op)&&op!=Tok!"←"){
		Expression operation;
	}
}

class FieldExp: Expression{
	Expression e;
	Identifier f;

	this(Expression e,Identifier f){ this.e=e; this.f=f; }

	override FieldExp copyImpl(CopyArgs args){
		return new FieldExp(e.copy(args),f.copy(args));
	}

	override string toString(){
		return _brk(e.toString()~"."~f.toString());
	}

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		return e.freeVarsImpl(dg);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(e);
	}
	override FieldExp substituteImpl(Expression[Id] subst){
		auto ne=e.substitute(subst);
		if(ne==e) return this;
		auto r=new FieldExp(ne,f);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		auto fe=cast(FieldExp)rhs;
		if(!fe||f!=fe.f) return false;
		return e.unify(fe.e,subst,meet);
	}
	override bool opEquals(Object o){
		if(o is this) return true;
		auto fe=cast(FieldExp)o;
		if(!fe||f!=fe.f) return false;
		return e==fe.e;
	}

	override Annotation getAnnotation(){
		return e.getAnnotation();
	}

	override Expression evalImpl(){
		auto ne = e.eval();
		if(ne is e) return this;
		return new FieldExp(ne,f);
	}
}

class IteExp: Expression{
	Expression cond;
	CompoundExp then, othw;
	this(Expression cond, CompoundExp then, CompoundExp othw){
		this.cond=cond; this.then=then; this.othw=othw;
	}
	override IteExp copyImpl(CopyArgs args){
		return new IteExp(cond.copy(args),then.copy(args),othw?othw.copy(args):null);
	}
	override string toString(){return _brk("if "~cond.toString() ~ " " ~ then.toString() ~ (othw&&othw.s.length?" else " ~ (othw.s.length==1&&cast(IteExp)othw.s[0]?othw.s[0].toString():othw.toString()):""));}
	override bool isCompound(){ return true; }

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		if(auto r=cond.freeVarsImpl(dg)) return r;
		if(auto r=then.freeVarsImpl(dg)) return r;
		if(othw) if(auto r=othw.freeVarsImpl(dg)) return r;
		return 0;
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(cond)) return r;
		if(auto r=dg(then)) return r;
		if(othw) if(auto r=othw.subexpressionsImpl(dg)) return r;
		return 0;
	}
	override IteExp substituteImpl(Expression[Id] subst){
		auto ncond=cond.substitute(subst);
		auto nthen=cast(CompoundExp)then.substitute(subst);
		auto nothw=othw?cast(CompoundExp)othw.substitute(subst):null;
		assert(!!nthen && !!nothw==!!othw);
		if(ncond==cond&&nthen==then&&nothw==othw) return this;
		auto r=new IteExp(ncond,nthen,nothw);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		auto ite=cast(IteExp)rhs;
		if(!ite) return false;
		return cond.unify(ite.cond,subst,meet)&&then.unify(ite.then,subst,meet)
			&&(!othw&&!ite.othw||othw&&ite.othw&&othw.unify(ite.othw,subst,meet));
	}
	override bool opEquals(Object o){
		if(o is this) return true;
		auto ite=cast(IteExp)o;
		if(!ite) return false;
		return cond==ite.cond&&then==ite.then
			&&(!othw&&!ite.othw||othw&&ite.othw&&othw==ite.othw);
	}
	override Expression getClassical(){
		static if(language==silq){
			assert(isType(this)&&cond.type&&cond.type.isClassical());
			if(auto r=super.getClassical()) return r;
			assert(then&&then.s.length==1);
			auto nthen=new CompoundExp([then.s[0].getClassical()]);
			nthen.type=then.s[0].type;
			nthen.setSemCompleted();
			assert(othw&&othw.s.length==1);
			auto nothw=new CompoundExp([othw.s[0].getClassical()]);
			nothw.type=othw.s[0].type;
			nothw.setSemCompleted();
			auto r=new IteExp(cond,nthen,nothw);
			r.type=getClassicalTy(type);
			r.setSemCompleted();
			return r.eval();
		}else return this;
	}
	override bool mayBeClassical(){
		if(!cond.type||!cond.type.isClassical()) return true; // TODO: what to do here?
		assert(then&&then.s.length==1);
		assert(othw&&othw.s.length==1);
		return then.s[0].mayBeClassical()||othw.s[0].mayBeClassical();
	}
	override bool mayBeQuantum(){
		if(!cond.type||!cond.type.isClassical()) return true; // TODO: what to do here?
		assert(then&&then.s.length==1);
		assert(othw&&othw.s.length==1);
		return then.s[0].mayBeQuantum()||othw.s[0].mayBeQuantum();
	}
	override Annotation getAnnotation(){
		return min(cond.getAnnotation(), then.getAnnotation(), othw.getAnnotation());
	}
	override Expression evalImpl(){
		auto ncond=cond.eval(),nthen=cast(CompoundExp)then.eval(),nothw=cast(CompoundExp)othw.eval();
		assert(nthen&&nothw); // TODO: check statically
		if(ncond is cond && nthen is then && nothw is othw) return this;
		auto r=new IteExp(ncond,nthen,nothw);
		r.type=type;
		return r;
	}
	// semantic information
	override void setConstLookup(bool constLookup){
		then.setConstLookup(constLookup);
		othw.setConstLookup(constLookup);
		super.setConstLookup(constLookup);
	}
}

class WithExp: Expression{
	CompoundExp trans;
	CompoundExp bdy;
	this(CompoundExp trans, CompoundExp bdy, bool isIndices=false){
		this.trans=trans;
		this.bdy=bdy;
		this.isIndices=isIndices;
	}
	override WithExp copyImpl(CopyArgs args){
		auto r=new WithExp(trans.copy(args),bdy.copy(args),isIndices);
		if(isIndices&&itrans) r.itrans=itrans.copy(args);
		return r;
	}
	override string toString(){ return _brk("with "~trans.toString()~" do "~bdy.toString()); }
	override @property string kind(){ return "with"; }
	override bool isCompound(){ return true; }

	override Expression evalImpl(){ return this; }
	mixin VariableFree; // TODO
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(trans)) return r;
		return dg(bdy);
	}
	// semantic information
	CompoundExp itrans; // inverse transform
	bool isIndices=false;
	Declaration aggregate(bool old)in{
		assert(isIndices);
		assert(old?!!trans:!!itrans);
	}do{
		Declaration meaning;
		foreach(e;(old?trans:itrans).s){
			import ast.semantic_:unwrap,getIdFromIndex;
			auto de=cast(DefineExp)e;
			assert(!!de);
			auto idx=cast(IndexExp)unwrap(old?de.e2:de.e1);
			assert(idx&&idx.byRef);
			auto id=getIdFromIndex(idx);
			assert(id);
			if(!id.meaning) return null;
			if(!meaning) meaning=id.meaning;
			else assert(meaning is id.meaning);
		}
		return meaning;
	}
}

class RepeatExp: Expression{
	Expression num;
	CompoundExp bdy;
	this(Expression num, CompoundExp bdy){
		this.num=num; this.bdy=bdy;
	}
	override RepeatExp copyImpl(CopyArgs args){
		return new RepeatExp(num.copy(args),bdy.copy(args));
	}
	override string toString(){ return _brk("repeat "~num.toString()~" "~bdy.toString()); }
	override @property string kind(){ return "repeat loop"; }
	override bool isCompound(){ return true; }

	override Expression evalImpl(){ return this; }
	mixin VariableFree; // TODO
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(num)) return r;
		return dg(bdy);
	}
}

class ForExp: Expression{
	Identifier var;
	bool leftExclusive;
	Expression left;
	Expression step;
	bool rightExclusive;
	Expression right;
	CompoundExp bdy;
	this(Identifier var,bool leftExclusive,Expression left,Expression step,bool rightExclusive,Expression right,CompoundExp bdy){
		this.var=var;
		this.leftExclusive=leftExclusive; this.left=left;
		this.step=step;
		this.rightExclusive=rightExclusive; this.right=right;
		this.bdy=bdy;
	}
	override ForExp copyImpl(CopyArgs args){
		auto r=new ForExp(var.copy(args),leftExclusive,left.copy(args),step?step.copy(args):null,rightExclusive,right.copy(args),bdy.copy(args));
		if(args.preserveSemantic){
			enforce(!fescope_&&!loopVar,"TODO");
		}
		return r;
	}
	override string toString(){ return _brk("for "~var.toString()~" in "~
	                                        (leftExclusive?"(":"[")~left.toString()~".."~(step?step.toString()~"..":"")~right.toString()~
	                                        (rightExclusive?")":"]")~bdy.toString()); }
	override @property string kind(){ return "for loop"; }
	override bool isCompound(){ return true; }

	// semantic information
	BlockScope fescope_;
	VarDecl loopVar;

	override Expression evalImpl(){ return this; }
	mixin VariableFree; // TODO
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0; // TODO: ok?
	}
}

class WhileExp: Expression{
	Expression cond;
	CompoundExp bdy;
	this(Expression cond,CompoundExp bdy){
		this.cond=cond;
		this.bdy=bdy;
	}
	override WhileExp copyImpl(CopyArgs args){
		return new WhileExp(cond.copy(args),bdy.copy(args));
	}
	override string toString(){ return _brk("while "~cond.toString()~bdy.toString()); }
	override @property string kind(){ return "while loop"; }
	override bool isCompound(){ return true; }

	override Expression evalImpl(){ return this; }
	mixin VariableFree; // TODO
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(cond)) return r;
		return dg(bdy);
	}
}

class CompoundExp: Expression{
	Expression[] s;
	this(Expression[] ss){s=ss;}
	override CompoundExp copyImpl(CopyArgs args){
		return new CompoundExp(s.map!(e=>e.copy(args)).array);
	}

	override string toString(){return "{\n"~indent(join(map!(a=>a.toString()~(a.isCompound()?"":";"))(s),"\n"))~"\n}";}
	string toStringFunctionDef(){
		if(s.length==1)
			if(auto ret=cast(ReturnExp)s[0]){
				if(auto le=cast(LambdaExp)ret.e)
					return le.toString;
				return " ⇒ "~ret.e.toString();
			}
		return toString();
	}
	override bool isCompound(){ return true; }

	// semantic information
	BlockScope blscope_;

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		foreach(x;s) if(auto r=x.freeVarsImpl(dg)) return r;
		return 0;
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		foreach(x;s) if(auto r=dg(x)) return r;
		return 0;
	}
	override Expression substituteImpl(Expression[Id] subst){
		auto ns=s.dup;
		foreach(ref x;ns) x=x.substitute(subst);
		if(ns==s) return this;
		auto r=new CompoundExp(ns);
		r.loc=loc;
		return r;

	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		auto ce=cast(CompoundExp)rhs;
		if(!ce) return false;
		if(s.length!=ce.s.length) return false;
		return iota(s.length).all!(i=>s[i].unify(ce.s[i],subst,meet));
	}
	override bool opEquals(Object o){
		if(o is this) return true;
		auto ce=cast(CompoundExp)o;
		if(!ce) return false;
		if(s.length!=ce.s.length) return false;
		return iota(s.length).all!(i=>s[i]==ce.s[i]);
	}
	override Annotation getAnnotation(){ return reduce!min(Annotation.max, s.map!(x=>x.getAnnotation())); }
	override CompoundExp evalImpl(){
		auto ns = s.map!(s=>s.eval()).array;
		if(iota(s.length).all!(i => ns[i] is s[i])) return this;
		return new CompoundExp(ns);
	}
}

class ComponentReplaceExp: CompoundExp{
	Expression reads;
	Expression statement;
	Expression writes;
	this(Expression reads,Expression statement,Expression writes){
		this.reads=reads;
		this.statement=statement;
		this.writes=writes;
		Expression[] s;
		if(reads) s~=reads;
		s~=statement;
		if(writes) s~=writes;
		super(s);
	}
}

class TupleExp: Expression{
	Expression[] e;
	this(Expression[] e){
		this.e=e;
	}
	override TupleExp copyImpl(CopyArgs args){
		return new TupleExp(e.map!(e=>e.copy(args)).array);
	}
	override string toString(){ return _brk("("~e.map!(to!string).join(",")~(e.length==1?",":"")~")"); }
	override bool isConstant(){ return e.all!(x=>x.isConstant()); }
	override bool isTotal(){ return e.all!(x=>x.isTotal()); }
	final @property size_t length(){ return e.length; }

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		foreach(x;e) if(auto r=x.freeVarsImpl(dg)) return r;
		return 0;
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		foreach(x;e) if(auto r=dg(x)) return r;
		return 0;
	}
	override TupleExp substituteImpl(Expression[Id] subst){
		auto ne=e.dup;
		foreach(ref x;ne) x=x.substitute(subst);
		if(ne==e) return this;
		auto r=new TupleExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		auto te=cast(TupleExp)rhs;
		if(!te||e.length!=te.e.length) return false;
		return all!(i=>e[i].unify(te.e[i],subst,meet))(iota(e.length));
	}
	override bool opEquals(Object o){
		if(o is this) return true;
		auto tpl=cast(TupleExp)o;
		return tpl&&e==tpl.e;
	}
	override Annotation getAnnotation(){
		return reduce!min(pure_, e.map!(x=>x.getAnnotation()));
	}
	override Expression evalImpl(){
		auto ne = e.map!(e=>e.eval()).array;
		if(iota(e.length).all!(i => ne[i] is e[i])) return this;
		return new TupleExp(ne);
	}
	// semantic information
	override void setConstLookup(bool constLookup){
		foreach(x;e) x.setConstLookup(constLookup);
		super.setConstLookup(constLookup);
	}
}

class LambdaExp: Expression{
	FunctionDef orig;
	FunctionDef fd;
	this(FunctionDef orig){
		this(orig,orig.copy());
	}
	this(FunctionDef orig,FunctionDef fd){
		this.orig=orig;
		this.fd=fd;
	}
	override LambdaExp copyImpl(CopyArgs args){
		return new LambdaExp(orig);
	}
	override string toString(){
		string d=fd.isSquare?"[]":"()";
		return _brk(d[0]~join(map!(to!string)(fd.params),",")~d[1]~(fd.annotation?text(fd.annotation):"")~(fd.body_?fd.body_.toStringFunctionDef():";"));
	}

	mixin VariableFree; // TODO!
	override int componentsImpl(scope int delegate(Expression) dg){
		foreach(decl,ids;fd.captures){
			foreach(c;ids)
				if(auto r=dg(c))
					return r;
		}
		return 0;
	}
	override Expression evalImpl(){ return this; } // TODO: partially evaluate lambdas?
	override Annotation getAnnotation(){ return pure_; }
}

class VectorExp: Expression{
	Expression[] e;
	this(Expression[] e){
		this.e=e;
	}
	override VectorExp copyImpl(CopyArgs args){
		return new VectorExp(e.map!(e=>e.copy(args)).array);
	}
	override string toString(){ return _brk("["~e.map!(to!string).join(",")~"]");}
	override bool isConstant(){ return e.all!(x=>x.isConstant()); }
	override bool isTotal(){ return e.all!(x=>x.isTotal()); }

	override bool opEquals(Object o){
		if(o is this) return true;
		auto r=cast(VectorExp)o;
		return r&&e==r.e;
	}

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		foreach(x;e) if(auto r=x.freeVarsImpl(dg)) return r;
		return 0;
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		foreach(x;e) if(auto r=dg(x)) return r;
		return 0;
	}
	override VectorExp substituteImpl(Expression[Id] subst){
		auto ne=e.dup;
		foreach(ref x;ne) x=x.substitute(subst);
		if(ne==e) return this;
		auto r=new VectorExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		auto ae=cast(VectorExp)rhs;
		if(!ae||e.length!=ae.e.length) return false;
		return all!(i=>e[i].unify(ae.e[i],subst,meet))(iota(e.length));
	}
	override Annotation getAnnotation(){ return reduce!min(pure_,e.map!(x=>x.getAnnotation())); }
	override Expression evalImpl(){
		auto ne = e.map!(e=>e.eval()).array;
		if(iota(e.length).all!(i => ne[i] is e[i])) return this;
		return new VectorExp(ne);
	}
	// semantic information
	override void setConstLookup(bool constLookup){
		foreach(x;e) x.setConstLookup(constLookup);
		super.setConstLookup(constLookup);
	}
}

class ReturnExp: Expression{
	Expression e;
	this(Expression e){
		this.e=e;
	}
	override ReturnExp copyImpl(CopyArgs args){
		auto r=new ReturnExp(e.copy(args));
		r.expected=expected;
		return r;
	}
	override string toString(){ return "return"~(e?" "~e.toString():""); }
	override @property string kind(){ return "return statement"; }

	string expected;

	override Expression evalImpl(){
		auto ne=e.eval();
		if(ne is e) return this;
		return new ReturnExp(e);
	}
	mixin VariableFree; // TODO!
	override int componentsImpl(scope int delegate(Expression) dg){ return dg(e); }

	// semantic information:
	Declaration[] forgottenVars;
}

class AssertExp: Expression{
	Expression e;
	this(Expression e){
		this.e=e;
	}
	override AssertExp copyImpl(CopyArgs args){
		return new AssertExp(e.copy(args));
	}
	override string toString(){ return _brk("assert("~e.toString()~")"); }

	override bool isConstant(){
		return e.isConstant()&&isTrue(e);
	}
	override bool isTotal(){
		return e.isTotal()&&isTrue(e);
	}

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		return e.freeVarsImpl(dg);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(e);
	}
	override AssertExp substituteImpl(Expression[Id] subst){
		auto ne=e.substitute(subst);
		if(ne==e) return this;
		auto r=new AssertExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[Id] subst,bool meet){
		auto ae=cast(AssertExp)rhs;
		if(!ae) return false;
		return e.unify(ae.e,subst,meet);
	}
	override bool opEquals(Object o){
		if(o is this) return true;
		auto ae=cast(AssertExp)o;
		return ae&&e==ae.e;
	}

	override Annotation getAnnotation(){ return e.getAnnotation(); }

	override Expression evalImpl(){
		auto ne = e.eval();
		if(ne is e) return this;
		return new AssertExp(e);
	}
}

class ObserveExp: Expression{
	Expression e;
	this(Expression e){
		this.e=e;
	}
	override ObserveExp copyImpl(CopyArgs args){
		return new ObserveExp(e.copy(args));
	}
	override string toString(){ return _brk("observe("~e.toString()~")"); }

	override Expression evalImpl(){
		auto ne=e.eval();
		if(ne is e) return this;
		return new ObserveExp(e);
	}
	mixin VariableFree; // TODO
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(e);
	}
}

class CObserveExp: Expression{
	Expression var;
	Expression val;
	this(Expression var,Expression val){
		this.var=var; this.val=val;
	}
	override CObserveExp copyImpl(CopyArgs args){
		return new CObserveExp(var.copy(args),val.copy(args));
	}
	override string toString(){ return _brk("cobserve("~var.toString()~","~val.toString()~")"); }

	override Expression evalImpl(){
		auto nval=val.eval();
		if(nval is val) return this;
		return new CObserveExp(var,val);
	}
	mixin VariableFree; // TODO
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(var)) return r;
		return dg(val);
	}
}

class ForgetExp: Expression{
	Expression var;
	Expression val;
	this(Expression var,Expression val){
		this.var=var;
		this.val=val;
	}
	override ForgetExp copyImpl(CopyArgs args){
		return new ForgetExp(var.copy(args),val?val.copy(args):null);
	}
	override string toString(){ return _brk("forget("~var.toString()~(val?"="~val.toString():"")~")"); }

	override Expression evalImpl(){
		auto nval=val.eval();
		if(nval is val) return this;
		return new ForgetExp(var,nval);
	}
	mixin VariableFree; // TODO
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(var)) return r;
		if(!val) return 0;
		return dg(val);
	}
}

alias CommaExp=BinaryExp!(Tok!",");
alias AssignExp=BinaryExp!(Tok!"←");
alias DefineExp=BinaryExp!(Tok!":=");
alias OrAssignExp=BinaryExp!(Tok!"||←");
alias AndAssignExp=BinaryExp!(Tok!"&&←");
alias AddAssignExp=BinaryExp!(Tok!"+←");
alias SubAssignExp=BinaryExp!(Tok!"-←");
alias NSubAssignExp=BinaryExp!(Tok!"sub←");
alias MulAssignExp=BinaryExp!(Tok!"·←");
alias DivAssignExp=BinaryExp!(Tok!"/←");
alias IDivAssignExp=BinaryExp!(Tok!"div←");
alias ModAssignExp=BinaryExp!(Tok!"%←");
alias PowAssignExp=BinaryExp!(Tok!"^←");
alias CatAssignExp=BinaryExp!(Tok!"~←");
alias BitOrAssignExp=BinaryExp!(Tok!"∨←");
alias BitXorAssignExp=BinaryExp!(Tok!"⊕←");
alias BitAndAssignExp=BinaryExp!(Tok!"∧←");
alias AddExp=BinaryExp!(Tok!"+");
alias SubExp=BinaryExp!(Tok!"-");
alias NSubExp=BinaryExp!(Tok!"sub");
alias MulExp=BinaryExp!(Tok!"·");
alias DivExp=BinaryExp!(Tok!"/");
alias IDivExp=BinaryExp!(Tok!"div");
alias ModExp=BinaryExp!(Tok!"%");
alias PowExp=BinaryExp!(Tok!"^");
alias CatExp=BinaryExp!(Tok!"~");
alias BitOrExp=BinaryExp!(Tok!"∨");
alias BitXorExp=BinaryExp!(Tok!"⊕");
alias BitAndExp=BinaryExp!(Tok!"∧");
alias UMinusExp=UnaryExp!(Tok!"-");
alias UNotExp=UnaryExp!(Tok!"¬");
alias UBitNotExp=UnaryExp!(Tok!"~");
alias LtExp=BinaryExp!(Tok!"<");
alias LeExp=BinaryExp!(Tok!"≤");
alias GtExp=BinaryExp!(Tok!">");
alias GeExp=BinaryExp!(Tok!"≥");
alias EqExp=BinaryExp!(Tok!"=");
alias NeqExp=BinaryExp!(Tok!"≠");
alias OrExp=BinaryExp!(Tok!"||");
alias AndExp=BinaryExp!(Tok!"&&");
alias Exp=Expression;


private noreturn unknownDeclError(T...)(Expression s,auto ref T args){
	assert(0,text("unknown declaration: ",s?typeid(s):null," ",s));
}
auto dispatchDecl(alias f,alias default_=unknownDeclError,T...)(Expression d,auto ref T args){
	import core.lifetime:forward;
	// TODO: implement without cast cascade
	if(auto fd=cast(FunctionDef)d) return f(fd,forward!args);
	if(auto dd=cast(DatDecl)d) return f(dd,forward!args);

	if(auto de=cast(DefineExp)d) return f(de,forward!args);
	if(auto ce=cast(CommaExp)d) return f(ce,forward!args);

	if(auto imp=cast(ImportExp)d) return f(imp,forward!args);
	return default_(d,args);
}


private noreturn unknownStmError(T...)(Expression s,auto ref T args){
	assert(0,text("unknown statement: ",s?typeid(s):null," ",s));
}
auto dispatchStm(alias f,alias default_=unknownStmError,bool unanalyzed=false,T...)(Expression s,auto ref T args){
	import core.lifetime:forward;
	// TODO: implement without cast cascade
	if(auto ce=cast(CallExp)s) return f(ce,forward!args);
	static if(unanalyzed) if(auto idx=cast(IndexExp)s) return f(idx,forward!args);
	if(auto tae=cast(TypeAnnotationExp)s) return f(tae,forward!args);
	if(auto ce=cast(CompoundExp)s) return f(ce,forward!args);
	if(auto ite=cast(IteExp)s) return f(ite,forward!args);
	static if(language==silq){
		if(auto with_=cast(WithExp)s) return f(with_,forward!args);
	}
	if(auto ret=cast(ReturnExp)s) return f(ret,forward!args);
	if(auto fd=cast(FunctionDef)s) return f(fd,forward!args);

	static if(language==psi){
		if(auto dd=cast(DatDecl)s) return f(dd,forward!args);
	}

	if(auto ce=cast(CommaExp)s) return f(ce,forward!args);
	// TODO: supertypes for define and assign?

	if(auto fe=cast(ForExp)s) return f(fe,forward!args);
	if(auto we=cast(WhileExp)s) return f(we,forward!args);
	if(auto re=cast(RepeatExp)s) return f(re,forward!args);

	if(auto oe=cast(ObserveExp)s) return f(oe,forward!args);
	if(auto oe=cast(CObserveExp)s) return f(oe,forward!args);

	if(auto ae=cast(AssertExp)s) return f(ae,forward!args);

	if(auto fe=cast(ForgetExp)s) return f(fe,forward!args);

	return default_(s,args);
}

// TODO: type dispatch


private noreturn unknownExpError(T...)(Expression e,auto ref T args){
	assert(0,text("unknown expression: ",e?typeid(e):null," ",e));
}
auto dispatchExp(alias f,alias default_=unknownExpError,bool unanalyzed=false,T...)(Expression e,auto ref T args){
	import core.lifetime:forward;
	// TODO: implement without cast cascade
	if(auto ite=cast(IteExp)e) return f(ite,forward!args);
	if(auto ae=cast(AssertExp)e) return f(ae,forward!args);
	if(auto le=cast(LiteralExp)e) return f(le,forward!args);
	if(auto le=cast(LambdaExp)e) return f(le,forward!args);
	if(auto ce=cast(CallExp)e) return f(ce,forward!args);
	static if(language==psi) if(auto pl=cast(PlaceholderExp)e) return f(pl,forward!args);
	if(auto fe=cast(ForgetExp)e) return f(fe,forward!args);
	if(auto id=cast(Identifier)e) return f(id,forward!args);
	if(auto fe=cast(FieldExp)e) return f(fe,forward!args);
	if(auto idx=cast(IndexExp)e) return f(idx,forward!args);
	if(auto sl=cast(SliceExp)e) return f(sl,forward!args);
	if(auto tpl=cast(TupleExp)e) return f(tpl,forward!args);
	if(auto vec=cast(VectorExp)e) return f(vec,forward!args);

	if(auto tae=cast(TypeAnnotationExp)e) return f(tae,forward!args);

	if(auto ume=cast(UMinusExp)e) return f(ume,forward!args);
	if(auto une=cast(UNotExp)e) return f(une,forward!args);
	if(auto ubne=cast(UBitNotExp)e) return f(ubne,forward!args);

	if(auto ae=cast(AddExp)e) return f(ae,forward!args);
	if(auto se=cast(SubExp)e) return f(se,forward!args);
	if(auto nse=cast(NSubExp)e) return f(nse,forward!args);
	if(auto me=cast(MulExp)e) return f(me,forward!args);
	if(auto de=cast(DivExp)e) return f(de,forward!args);
	if(auto ide=cast(IDivExp)e) return f(ide,forward!args);
	if(auto me=cast(ModExp)e) return f(me,forward!args);
	if(auto pe=cast(PowExp)e) return f(pe,forward!args);
	if(auto boe=cast(BitOrExp)e) return f(boe,forward!args);
	if(auto bxe=cast(BitXorExp)e) return f(bxe,forward!args);
	if(auto bae=cast(BitAndExp)e) return f(bae,forward!args);

	if(auto ae=cast(AndExp)e) return f(ae,forward!args);
	if(auto oe=cast(OrExp)e) return f(oe,forward!args);

	if(auto le=cast(LtExp)e) return f(le,forward!args);
	if(auto le=cast(LeExp)e) return f(le,forward!args);
	if(auto ge=cast(GtExp)e) return f(ge,forward!args);
	if(auto ge=cast(GeExp)e) return f(ge,forward!args);
	if(auto eq=cast(EqExp)e) return f(eq,forward!args);
	if(auto ne=cast(NeqExp)e) return f(ne,forward!args);

	if(auto ce=cast(CatExp)e) return f(ce,forward!args);

	if(auto fa=cast(ClassicalTy)e) return f(fa,forward!args);
	if(auto fa=cast(ProductTy)e) return f(fa,forward!args);
	if(auto ty=cast(ArrayTy)e) return f(ty,forward!args);
	if(auto ty=cast(TupleTy)e) return f(ty,forward!args);
	if(auto ty=cast(VectorTy)e) return f(ty,forward!args);
	if(auto va=cast(VariadicTy)e) return f(va,forward!args);
	if(auto va=cast(TypeTy)e) return f(va,forward!args);
	if(auto va=cast(QNumericTy)e) return f(va,forward!args);
	if(auto va=cast(BottomTy)e) return f(va,forward!args);
	if(auto va=cast(NumericTy)e) return f(va,forward!args);
	if(auto va=cast(StringTy)e) return f(va,forward!args);

	static if(unanalyzed){
		// expression types that only occur in unanalyzed expressions
		if(auto we=cast(WildcardExp)e) return f(we,forward!args);
		if(auto ty=cast(TypeofExp)e) return f(ty,forward!args);
		if(auto pr=cast(BinaryExp!(Tok!"×"))e) return f(pr,forward!args);
		if(auto ex=cast(BinaryExp!(Tok!"→"))e) return f(ex,forward!args);
	}

	return default_(e,forward!args);
}
