// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.expression;

import std.array, std.algorithm, std.range, std.conv, std.string, std.exception;
import std.meta: AliasSeq;

import ast.lexer, ast.parser, ast.scope_, ast.type, ast.declaration, util;
import util.maybe;
import util: MapX, SetX, MapSX;
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
		struct Rename{
			Declaration decl;
			Id nid;
		}
		Rename* rename;
		// optional remapping of analyzed-tree references (see ast.substitute.rescopeTwin)
		Declaration delegate(Declaration) mapDecl;
		Scope delegate(Scope) mapScope;
		Expression delegate(Expression, ref CopyArgs) mapExp;
		void delegate(Expression,Expression) postCopy;
	}
	abstract Expression copyImpl(CopyArgs args);
	final T copy(this T)(CopyArgs args=CopyArgs.init){
		if(args.mapExp) if(auto r=cast(T)args.mapExp(this,args)) return r;
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
		if(args.postCopy) args.postCopy(this,r);
		return r;
	}

	enum int prNone=-1;
	enum int prInf=int.max;
	@property int lprec(){ return prInf; }
	@property int rprec(){ return prInf; }
	override string toString(){ return _brk("{}()"); }
	string toStringImpl(int cl,int cr){ return toString(); }
	protected string _brk(string s,int cl=prNone,int cr=prNone){
		auto br=brackets;
		if(!implicitDup&&(lprec<=cl||rprec<cr)) br=max(br,1);
		return std.array.replicate("(",br)~(implicitDup?"dup(":"")~s~(implicitDup?")":"")~std.array.replicate(")",br);
	}

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
	Maybe!(Q!(ℤ, ℤ, int, int)) asImaginaryRationalConstant() {
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
		MapSX!(Id,Expression) subst;
		subst[name]=exp;
		return substitute(subst);
	}
	final Expression substitute(MapSX!(Id,Expression) subst,TypeTransition* tt=null){
		assert(isSemCompleted());
		auto r=substituteImpl(subst,tt);
		if(r !is this) {
			assert(type !is this);
			assert(!r.type || r.type.isSemEvaluated(), format("eval %s -> %s, unevaluated type %s", this, r, r.type));
			if(!r.type) r.type = type.substitute(subst,tt);
			r.setSemCompleted();
		}
		return r.eval();
	}
	abstract Expression substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt); // TODO: name might be free in the _types_ of subexpressions

	static struct UnificationResult{
		Expression lowerBound=null;
		Expression upperBound=null;
		Expression bound(bool meet){
			if(meet) return upperBound;
			return lowerBound;
		}
		void add(Expression e,bool meet){
			add(UnificationResult(e,meet));
		}
		void relax(Expression e,bool meet){
			if(meet){
				if(upperBound) upperBound=joinTypes(upperBound,e);
			}else{
				if(lowerBound) lowerBound=meetTypes(lowerBound,e);
			}
		}
		void add(UnificationResult ur){
			if(ur.lowerBound){
				if(!lowerBound) lowerBound=ur.lowerBound;
				else lowerBound=joinTypes(lowerBound,ur.lowerBound);
			}
			if(ur.upperBound){
				if(!upperBound) upperBound=ur.upperBound;
				else upperBound=meetTypes(upperBound,ur.upperBound);
			}
		}
		this(Expression e,bool meet){
			if(meet) upperBound=e;
			else lowerBound=e;
		}
	}

	final bool unify(Expression rhs,ref MapSX!(Id,UnificationResult) subst, bool meet){
		return unifyImpl(rhs,subst,meet) || eval().unifyImpl(rhs.eval(),subst,meet) || isSubtype(rhs,this);
	}
	abstract bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet);

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
	final override bool opEquals(Object o){
		if(o is this) return true;
		auto r=cast(Expression)o;
		if(!r) return false;
		EqualityContext ctx;
		return isEqualImpl(r,ctx);
	}
	bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		return this is rhs;
	}
	bool isSubtypeImpl(Expression rhs,EqualityContext* ctx){
		return .isEqual(this,rhs,ctx);
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
	override Expression substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){ return this; }
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
		return combineTypes(this,rhs,meet)!is null;
	}
}

enum TypeAnnotationType{
	annotation,
	conversion,
	coercion,
	punning,
}

mixin template PrecedenceToString(){
	override string toString(){ return toStringImpl(prNone,prNone); }
}

class TypeAnnotationExp: Expression{
	Expression e,t;
	TypeAnnotationType annotationType;
	this(Expression e, Expression t, TypeAnnotationType annotationType){
		this.e=e; this.t=t;
		this.annotationType=annotationType;
	}
	override TypeAnnotationExp copyImpl(CopyArgs args){
		auto r=new TypeAnnotationExp(e.copy(args),t.copy(args),annotationType);
		r.fromElaboration=fromElaboration;
		if(unresolvedT) r.unresolvedT=unresolvedT.copy(args);
		return r;
	}
	override @property string kind(){ return e.kind; }
	override @property int lprec(){
		final switch(annotationType) with(TypeAnnotationType){
			case annotation: return lbp!(Tok!":");
			case conversion: return lbp!(Tok!"as");
			case coercion: return lbp!(Tok!"coerce");
			case punning: return lbp!(Tok!"pun");
		}
	}
	override @property int rprec(){
		final switch(annotationType) with(TypeAnnotationType){
			case annotation: return rbp!(Tok!":");
			case conversion: return rbp!(Tok!"as");
			case coercion: return rbp!(Tok!"coerce");
			case punning: return rbp!(Tok!"pun");
		}
	}
	mixin PrecedenceToString;
	override string toStringImpl(int cl,int cr){
		static immutable op=[": "," as "," coerce "," pun "];
		static assert(TypeAnnotationType.max==TypeAnnotationType.punning);
		auto myLbp=lprec, myRbp=rprec;
		return _brk(e.toStringImpl(cl,myLbp)~op[annotationType]~(type?type.toStringImpl(myRbp,cr):t.toStringImpl(myRbp,cr)),cl,cr);
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
	override TypeAnnotationExp substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){
		auto ne=e.substitute(subst,tt);
		auto nt=t.substitute(subst,tt);
		if(ne is e && nt is t) return this;
		auto r=new TypeAnnotationExp(ne, nt, annotationType);
		r.loc=loc;
		r.type=nt.eval();
		return r;
	}
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
		return e.unify(rhs,subst,meet);
	}
	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto tae=cast(TypeAnnotationExp)rhs;
		if(!tae) return false;
		return isEqual(e,tae.e,&ctx)&&isEqual(t,tae.t,&ctx)&&annotationType==tae.annotationType;
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
	bool fromElaboration=false;
	Expression unresolvedT=null; // type expression before wildcard resolution
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
		if(args.preserveSemantic) r.type=type;
		return r;
	}
	override string toString(){
		return _brk(lit.toString());
	}
	override bool isConstant(){
		assert(!!type);
		return type.isConstant();
	}
	override bool isTotal(){
		assert(!!type);
		return type.isTotal();
	}

	private static bool hasBasePrefix(string str){
		if(str.length<2) return false;
		if(str[0]!='0') return false;
		switch(str[1]){
			case 'b','B','o','O','x','X': return true;
			default: return false;
		}
	}
	private static ℤ parseIntegerConstant(string str)in{
		assert(!!str.length);
	}do{
		if(str[0]=='+') return parseIntegerConstant(str[1..$]);
		if(str[0]=='-') return -parseIntegerConstant(str[1..$]);
		if(hasBasePrefix(str)){
			if(str[1]=='b'||str[1]=='B'){
				ℤ r=0;
				foreach(c;str[2..$]) r=2*r+int(c=='1');
				return r;
			}
			if(str[1]=='o'||str[1]=='O'){
				ℤ r=0;
				foreach(c;str[2..$]) r=8*r+int(c-'0');
				return r;
			}
		}
		return ℤ(str);
	}

	override Maybe!ℤ asIntegerConstant(bool eval=false) {
		if(lit.type!=Tok!"0") return none!(ℤ);
		return just(parseIntegerConstant(lit.str));
	}
	// returns (x, y, b, n) where the value is x/y * b**n; y > 0, b > 0
	private static Maybe!(Q!(ℤ, ℤ, int, int)) parseRationalConstant(string str){
		if(hasBasePrefix(str)) return just(q(parseIntegerConstant(str),ℤ(1),1,0));
		int base = 10;
		int exp = 0;
		string numPart = str;
		auto e = str.find("e");
		if(auto f = str.find("E")) if(!e.length||f.ptr<e.ptr) e = f;
		if(e.length > 0) {
			numPart = str[0..(e.ptr - str.ptr)];
			auto es = e[1..$];
			long x = 0, sign = 1;
			if(es.length&&(es[0]=='+'||es[0]=='-')){ if(es[0]=='-') sign=-1; es=es[1..$]; }
			foreach(c;es) if(x<=int.max) x=10*x+(c-'0');
			x*=sign;
			exp = x<int.min?int.min:x>int.max?int.max:cast(int)x;
		}

		string intPart = numPart, fracPart = "";
		auto dot = numPart.find(".");
		if(dot.length > 0) {
			intPart = str[0..(dot.ptr - numPart.ptr)];
			fracPart = dot[1..$];
		}
		exp -= fracPart.length;

		return just(q(ℤ(intPart ~ fracPart), ℤ(1), base, exp));
	}
	override Maybe!(Q!(ℤ, ℤ, int, int)) asRationalConstant() {
		if(lit.type == Tok!"0") return just(q(parseIntegerConstant(lit.str), ℤ(1), 1, 0));
		if(lit.type != Tok!".0") return none!(Q!(ℤ, ℤ, int, int));
		return parseRationalConstant(lit.str);
	}
	// returns 0 if this is a scientific-notation literal whose value is zero, 1 if the value
	// is one, 2 if the value is a larger natural number, and -1 if the value should be typed as !ℚ
	int asNaturalScientificValue(){
		if(lit.type!=Tok!".0") return -1;
		auto str=lit.str;
		ptrdiff_t epos=-1;
		foreach(i,c;str) if(c=='e'||c=='E'){ epos=i; break; }
		if(epos<0) return -1; // no scientific notation
		long exp=0, esign=1;
		auto i=epos+1;
		if(i<str.length&&(str[i]=='+'||str[i]=='-')){ if(str[i]=='-') esign=-1; i++; }
		if(i>=str.length||str[i]<'0'||str[i]>'9') return -1; // malformed exponent
		enum long sat=1L<<40;
		for(;i<str.length;i++) if(exp<sat) exp=10*exp+(str[i]-'0');
		exp*=esign;
		auto mantissa=str[0..epos], intPart=mantissa, fracPart="";
		bool hasPeriod=false;
		foreach(j,c;mantissa){
			if(c=='.'){
				intPart=mantissa[0..j];
				hasPeriod=true;
				fracPart=mantissa[j+1..$];
				break;

			}
		}
		if(hasPeriod) return -1; // TODO: type 2.0 and 2.0e0 as !ℕ ?
		auto digits=intPart~fracPart;
		long n=exp-cast(long)fracPart.length;
		size_t lead=0;
		while(lead<digits.length&&digits[lead]=='0') lead++;
		auto s=digits[lead..$];
		if(!s.length) return 0; // zero
		size_t tz=0;
		while(tz<s.length&&s[$-1-tz]=='0') tz++;
		if(n<0&&cast(long)tz<-n) return -1; // value has fractional digits
		if(s[0..$-tz]=="1"&&n+cast(long)tz==0) return 1; // one
		return 2;
	}
	override Maybe!(Q!(ℤ, ℤ, int, int)) asImaginaryRationalConstant() {
		if(lit.type != Tok!".0i") return none!(Q!(ℤ, ℤ, int, int));
		if(!lit.str.endsWith("i"))  return none!(Q!(ℤ, ℤ, int, int));
		return parseRationalConstant(lit.str[0..$-1]);
	}
	override Maybe!string asStringConstant() {
		if(lit.type != Tok!"``") return none!string;
		return just(lit.str);
	}

	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto r=cast(LiteralExp)rhs;
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
	if(!e.type) return false;
	if(auto v = e.asIntegerConstant(eval))
		return v.get() == 0;
	return false;
}
bool isOne(Expression e, bool eval=false){
	if(!e.type) return false;
	if(auto v = e.asIntegerConstant(eval))
		return v.get() == 1;
	return false;
}
bool isNonzero(Expression e, bool eval=false){
	if(!e.type) return false;
	if(auto v = e.asIntegerConstant(eval))
		return v.get() != 0;
	return false;
}
bool isPositive(Expression e, bool eval=false){
	if(!e.type) return false;
	if(auto v = e.asIntegerConstant(eval))
		return v.get() > 0;
	return false;
}
bool isFalse(Expression e, bool eval=false){
	if(!e.type) return false;
	return isZero(e, eval);
}
bool isTrue(Expression e, bool eval=false){
	if(!e.type) return false;
	return isNonzero(e, eval);
}

struct Id {
	static __gshared MapSX!(string,Id) interned;
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
		if(auto p = interned.getPtr(s)) {
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

	size_t toHash() const pure @safe nothrow {
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

struct EqualityContext{
	private MapSX!(Declaration,Declaration) mapL, mapR;
	private static Declaration source(Declaration d){
		return d?d.canonicalSource:d;
	}
	bool isBound(Declaration d){
		return source(d) in mapL||source(d) in mapR;
	}
	bool lookup(Declaration l,Declaration r){
		l=source(l), r=source(r);
		if(l is r) return true;
		auto pl = mapL.getPtr(l);
		auto pr = mapR.getPtr(r);
		if(pl||pr) return pl&&pr&&*pl is r&&*pr is l;
		return false;
	}
	void bind(Declaration ma,Declaration mb){
		ma=source(ma), mb=source(mb);
		if(auto p = mapL.getPtr(ma)){
			if(*p is mb) return;
			mapR.remove(*p);
		}else if(auto p = mapR.getPtr(mb)){
			mapL.remove(*p);
		}
		mapL[ma]=mb;
		mapR[mb]=ma;
	}
	private bool pairBound(Expression sa,Expression sb){
		import ast.substitute: statementBoundVarsImpl;
		Declaration[] da,db;
		static void collect(Expression stmt,ref Declaration[] acc){
			statementBoundVarsImpl(stmt,(id){ if(id.meaning) acc~=id.meaning; return 0; });
			// a function definition binds the definition itself (the name
			// identifier may not carry a meaning)
			if(auto fd=cast(FunctionDef)stmt)
				if(!acc.length||acc[$-1] !is fd) acc~=fd;
		}
		collect(sa,da);
		collect(sb,db);
		if(da.length!=db.length) return false;
		foreach(i;0..da.length) bind(da[i],db[i]);
		return true;
	}

	private bool functionDefEquals(FunctionDef a,FunctionDef b){
		if(a.isTuple!=b.isTuple||a.isSquare!=b.isSquare) return false;
		if(a.params.length!=b.params.length) return false;
		foreach(i;0..a.params.length){
			auto pa=a.params[i],pb=b.params[i];
			if(pa.isConst!=pb.isConst) return false;
			if((pa.dtype is null)!=(pb.dtype is null)) return false;
			if(pa.dtype&&!pa.dtype.isEqualImpl(pb.dtype,this)) return false;
			if((pa.vtype is null)!=(pb.vtype is null)) return false;
			if(pa.vtype&&!pa.vtype.isEqualImpl(pb.vtype,this)) return false;
			bind(pa,pb);
		}
		if((a.rret is null)!=(b.rret is null)) return false;
		if(a.rret&&!a.rret.isEqualImpl(b.rret,this)) return false;
		if((a.ret is null)!=(b.ret is null)) return false;
		if(a.ret&&!a.ret.isEqualImpl(b.ret,this)) return false;
		if((a.body_ is null)!=(b.body_ is null)) return false;
		if(a.body_&&!a.body_.isEqualImpl(b.body_,this)) return false;
		return true;
	}

	private bool stmtEquals(Expression a,Expression b){
		if(a is b) return true;
		if(auto fa=cast(FunctionDef)a){
			auto fb=cast(FunctionDef)b;
			if(!fb) return false;
			return functionDefEquals(fa,fb);
		}
		if(cast(FunctionDef)b) return false;
		return a.isEqualImpl(b,this);
	}

	bool stmtsEquals(Expression[] sa,Expression[] sb){
		static Expression[] flatten(Expression[] ss){
			Expression[] r;
			foreach(s;ss){
				if(cast(ForgetExp)s) continue; // TODO: get rid of this
				if(auto ce=cast(CompoundExp)s)
					if(!cast(ComponentReplaceExp)s){
						r~=flatten(ce.s);
						continue;
					}
				r~=s;
			}
			return r;
		}
		auto fa=flatten(sa), fb=flatten(sb);
		if(fa.length!=fb.length) return false;
		foreach(i;0..fa.length){
			if(!pairBound(fa[i],fb[i])) return false;
			if(!stmtEquals(fa[i],fb[i])) return false;
		}
		return true;
	}
}

bool isEqual(Expression a,Expression b,EqualityContext* ctx){
	if(a is b) return true;
	if(!a||!b) return false;
	if(ctx) return a.isEqualImpl(b,*ctx);
	EqualityContext fresh;
	return a.isEqualImpl(b,fresh);
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
			static if(language==silq){
				r.outerWanted=outerWanted;
				r.classical=classical;
			}
			if(args.mapDecl){
				auto oldmeaning=r.meaning;
				r.meaning=args.mapDecl(r.meaning);
				// a template use may deliberately display an id different
				// from its meaning's name; preserve that relationship
				if(r.meaning&&r.meaning.name&&oldmeaning&&oldmeaning.name&&id==oldmeaning.name.id)
					r.id=r.meaning.name.id;
			}
			if(args.mapScope) r.scope_=args.mapScope(r.scope_);
		}else{
			if(args.preserveMeanings){
				r.meaning=meaning;
				r.scope_=scope_; // TODO: make unnecessary
			}
			static if(language==silq){
				r.outerWanted=outerWanted;
				r.classical=classical;
			}
		}
		if(args.rename){
			if(meaning && args.rename.decl.canonicalSource is meaning.canonicalSource){
				r.id=args.rename.nid;
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
	override Expression substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){
		if(id !in subst) return this;
		if(tt&&tt.localRoot&&meaning&&meaning.scope_&&meaning.scope_.isNestedIn(tt.localRoot)&&!cast(FunctionDef)meaning) return this;
		assert(constLookup || implicitDup, format("consume in eval() expression: %s", this));
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
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
		if(id !in subst) return meet?isSubtype(this,rhs):isSubtype(rhs,this);
		if(this==rhs){
			if(subst[id].bound(meet)&&subst[id].bound(meet)!=this) return false;
			subst[id].add(this,meet);
			return true;
		}
		if(subst[id].bound(meet)==this) return false;
		static if(language==silq){
			if(isType(this)&&isType(rhs))
				if(rhs.isClassical<classical) return false;
		}
		void addSubst(Expression r){
			if(isType(r)){
				if(type==qtypeTy){
					if(auto q=r.getQuantum())
						r=q;
				}else if(type==ctypeTy){
					if(auto c=r.getClassical())
						r=c;
				}
			}
			auto ur=UnificationResult(r,meet);
			if(classical){
				if(isType(r)){
					if(auto q=r.getQuantum())
						ur.relax(q,meet);
					if(auto c=r.getClassical())
						ur.relax(c,meet);
				}
			}
			subst[id].add(ur);
		}
		if(subst[id].bound(meet)){
			if(!subst[id].bound(meet).unify(rhs,subst,meet)) return false;
			if((isType(subst[id].bound(meet))||isQNumeric(subst[id].bound(meet)))&&(isType(rhs)||isQNumeric(rhs)))
				if(auto cmb=combineTypes(subst[id].bound(meet),rhs,meet)){ // TODO: good?
					addSubst(cmb);
				}
			return true;
		}
		if(rhs.hasFreeVar(id)) return false; // TODO: fixpoint types
		addSubst(rhs);
		return true;
	}
	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		if(auto r=cast(Identifier)rhs){
			if(meaning&&r.meaning&&(ctx.isBound(meaning)||ctx.isBound(r.meaning)||meaning.canonicalSource is r.meaning.canonicalSource)){
				// at least one of the identifiers is bound within the
				// expressions currently being compared (or the meanings
				// descend from a common canonical source): they are equal
				// iff their meanings are paired up (alpha-equivalence)
				return ctx.lookup(meaning,r.meaning)&&isEqual(type,r.type,&ctx);
			}
			if(id==r.id && isClassical(this)==isClassical(r) && meaning==r.meaning) {
				if(meaning) {
					assert(isEqual(type,r.type,&ctx));
					return true;
				}
				return isEqual(type,r.type,&ctx);
			}
		}
		return false;
	}
	override bool isSubtypeImpl(Expression rhs,EqualityContext* ctx){
		if(auto r=cast(Identifier)rhs){
			if(ctx&&meaning&&r.meaning&&(ctx.isBound(meaning)||ctx.isBound(r.meaning)))
				return ctx.lookup(meaning,r.meaning);
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
		if(auto dd=cast(DatDecl)meaning){
			if(!dd.isNested){
				assert(!dd.capturedDecls);
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
		if(byRef) return null; // TODO: why is this suddenly needed?
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
	bool consumedDuringBorrow=false;
	bool lazyCapture=false;
	Scope scope_;
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
	override @property int rprec(){ return nbp; } // prefix operator: operand parsed with min binding power nbp
	mixin PrecedenceToString;
	override string toStringImpl(int cl,int cr){
		import std.uni;
		enum oc=TokChars!op;
		auto inner=e.toStringImpl(nbp,cr);
		static if(oc[$-1].isAlpha) inner=" "~inner;
		else if(inner.length&&inner[0]==oc[$-1]) inner="("~inner~")";
		return _brk(oc~inner,cl,cr);
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
	override UnaryExp substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){
		auto ne=e.substitute(subst,tt);
		if(ne is e) return this;
		auto r=new UnaryExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
		auto ue=cast(typeof(this))rhs;
		if(!ue) return false;
		return e.unify(ue.e,subst,meet);
	}
	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto ue=cast(UnaryExp!op)rhs;
		return ue&&isEqual(e,ue.e,&ctx);
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
	mixin PrecedenceToString;
	override string toStringImpl(int cl,int cr){return _brk(e.toStringImpl(cl,lbp!op)~TokChars!op,cl,cr);}

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		return e.freeVarsImpl(dg);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(e);
	}
	override PostfixExp substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){
		auto ne=e.substitute(subst,tt);
		if(ne is e) return this;
		auto r=new PostfixExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
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
	static if(language==silq) bool isClassical_=false;
	else enum isClassical_=true;
	this(Expression exp, Expression arg){e=exp; a=arg;}
	override IndexExp copyImpl(CopyArgs args){
		auto r=new IndexExp(e.copy(args),a.copy(args));
		r.isArraySyntax=isArraySyntax;
		r.isClassical_=isClassical_;
		return r;
	}
	mixin PrecedenceToString;
	override string toStringImpl(int cl,int cr){
		static if(language==silq) return _brk((isClassical_?"!":"")~e.toStringImpl(cl,lbp!(Tok!"["))~a.tupleToString(true),cl,cr);
		else return _brk(e.toStringImpl(cl,lbp!(Tok!"["))~a.tupleToString(true),cl,cr);
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
	override IndexExp substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){
		auto ne=e.substitute(subst,tt);
		auto na=a.substitute(subst,tt);
		if(ne is e&&na is a) return this;
		auto r=new IndexExp(ne,na);
		r.isArraySyntax=isArraySyntax;
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
		auto idx=cast(IndexExp)rhs;
		if(!idx) return false;
		// TODO: improve
		return e.unify(idx.e,subst,meet)&&a.unify(idx.a,subst,meet);
	}
	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto idx=cast(IndexExp)rhs;
		return idx&&isEqual(idx.e,e,&ctx)&&isEqual(idx.a,a,&ctx)&&idx.isClassical_==isClassical_;
	}
	override bool isSubtypeImpl(Expression rhs,EqualityContext* ctx){
		if(isEqual(this,rhs,ctx)) return true;
		// TODO: improve
		return false;
	}
	override Expression combineTypesImpl(Expression rhs, bool meet){
		if(this == rhs) return this;
		// TODO: improve
		return null;
	}
	override Expression getClassical(){
		assert(isSemEvaluated());
		static if(language==silq){
			assert(isType(this), format("index not a type: %s", this));
			if(auto r=super.getClassical()) return r;
			auto r=new IndexExp(e,a);
			r.isClassical_=isClassical_;
			r.type=getClassicalTy(type);
			r.setSemEvaluated();
			return r;
		}else return this;
	}
	override Expression getQuantum(){
		assert(isSemEvaluated());
		static if(language==silq){
			assert(isType(this), format("index not a type: %s", this));
			// TODO
			return null;
		}else return null;
	}
	override bool mayBeClassical(){
		return super.mayBeClassical()||isType(this); // may evaluate to unit type
	}
	override bool mayBeQuantum(){
		return super.mayBeQuantum()||isType(this); // may evaluate to unit type
	}

	override Annotation getAnnotation(){ return min(e.getAnnotation(), a.getAnnotation()); }

	override Expression evalImpl(){
		auto ne=e.eval();
		auto na=a.eval();
		Expression[] exprs;
		if(auto tpl=cast(TupleExp)ne) exprs=tpl.e;
		if(auto vec=cast(VectorExp)ne) exprs=vec.e;
		if(exprs.length){
			if(auto v=na.asIntegerConstant()){
				auto idx=v.get();
				if(0<=idx&&idx<exprs.length){
					auto r=exprs[cast(size_t)idx].eval();
					static if(language==silq){
						if(isClassical_)
							r=r.getClassical();
					}
					return r;
				}
			}
		}
		if(ne is e && na is a) return this;
		auto r=new IndexExp(ne,na);
		r.isArraySyntax=isArraySyntax;
		r.isClassical_=isClassical_;
		return r;
	}

	AAssignExp.Replacement[] replacements;
}

class SliceExp: Expression{
	Expression e;
	Expression l,r;
	this(Expression exp, Expression left,Expression right){e=exp; l=left; r=right; }
	override SliceExp copyImpl(CopyArgs args){
		return new SliceExp(e.copy(args),l.copy(args),r.copy(args));
	}
	mixin PrecedenceToString;
	override string toStringImpl(int cl,int cr){
		return _brk(e.toStringImpl(cl,lbp!(Tok!"["))~'['~l.toString()~".."~r.toString()~']',cl,cr);
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
	override SliceExp substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){
		auto ne=e.substitute(subst,tt);
		auto nl=l.substitute(subst,tt);
		auto nr=r.substitute(subst,tt);
		if(ne is e && nl is l && nr is r) return this;
		auto res=new SliceExp(ne,nl,nr);
		res.loc=loc;
		return res;
	}
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
		auto sl=cast(SliceExp)rhs;
		return e.unify(sl.e,subst,meet)&&l.unify(sl.l,subst,meet)&&r.unify(sl.r,subst,meet);
	}
	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto sl=cast(SliceExp)rhs;
		if(!sl) return false;
		return isEqual(e,sl.e,&ctx) && isEqual(l,sl.l,&ctx) && isEqual(r,sl.r,&ctx);
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
	mixin PrecedenceToString;
	override string toStringImpl(int cl,int cr){
		static if(language==silq) return _brk((isClassical_?"!":"")~e.toStringImpl(cl,lbp!(Tok!"("))~arg.tupleToString(isSquare),cl,cr);
		else return _brk(e.toStringImpl(cl,lbp!(Tok!"("))~arg.tupleToString(isSquare),cl,cr);
	}
	override int freeVarsImpl(scope int delegate(Identifier) dg){
		if(auto r=e.freeVarsImpl(dg)) return r;
		return arg.freeVarsImpl(dg);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(e)) return r;
		return dg(arg);
	}
	override CallExp substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){
		auto ne=e.substitute(subst,tt);
		auto narg=arg.substitute(subst,tt);
		if(ne is e&&narg is arg) return this;
		auto r=new CallExp(ne,narg,isSquare,isClassical_);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
		auto ce=cast(CallExp)rhs;
		if(!ce) return false;
		auto zmod1=isℤmodTy(this),zmod2=isℤmodTy(this); // TODO: generalize
		if(zmod1&&zmod2&&zmod1.isStar<=zmod2.isStar){
			return arg.unify(ce.arg,subst,meet);
		}
		return e.unify(ce.e,subst,meet)&&arg.unify(ce.arg,subst,meet);
	}
	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto ce=cast(CallExp)rhs;
		if(!ce) return false;
		return isEqual(e,ce.e,&ctx)&&isEqual(arg,ce.arg,&ctx)&&isSquare==ce.isSquare&&isClassical_==ce.isClassical_;
	}
	override bool isSubtypeImpl(Expression rhs,EqualityContext* ctx){
		if(isEqual(this,rhs,ctx)) return true;
		if(auto rcall = cast(CallExp)rhs){
			if(!isClassical_ && rcall.isClassical_) return false;
			if(isType(this) && isType(rhs) && isSquare==rcall.isSquare){
				if(e.isEqual(rcall.e,ctx)){
					if(auto id=cast(Identifier)e){
						if(id.meaning){
							if(auto dat=cast(DatDecl)id.meaning){
								auto rid=cast(Identifier)rcall.e;
								assert(rid && rid.meaning == dat);
								bool check(Variance variance,Expression t1,Expression t2){
									final switch(variance){
										case Variance.invariant_: return t1.isEqual(t2,ctx);
										case Variance.covariant: return isSubtype(t1,t2,ctx);
										case Variance.contravariant: return isSubtype(t2,t1,ctx);
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
				auto zmod1=isℤmodTy(this),zmod2=isℤmodTy(rcall);
				if(zmod1&&zmod2&&zmod1.N==zmod2.N){
					return zmod1.isStar>=zmod2.isStar;
				}
			}
		}
		return super.isSubtypeImpl(rhs,ctx);
	}
	override Expression combineTypesImpl(Expression rhs, bool meet){
		if(this == rhs) return this;
		if(auto rcall = cast(CallExp)rhs){
			if(isType(type) && isType(rhs) && isSquare==rcall.isSquare){
				if(e==rcall.e){
					if(arg==rcall.arg){
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
				auto zmod1=isℤmodTy(this),zmod2=isℤmodTy(rcall);
				if(zmod1&&zmod2&&zmod1.isStar!=zmod2.isStar&&zmod1.N==zmod2.N){
					auto id=cast(Identifier)this.e;
					assert(!!id);
					import ast.semantic_:getℤmodTy;
					return getℤmodTy(zmod1.N,false,zmod1.isClassical&&zmod2.isClassical,loc,id.scope_);
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
			if(isFixedIntTy(this)||isℤmodTy(this)){ // TODO: generalize
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
		if(isSemEvaluated){
			import ast.type:isFixedIntTy;
			if(auto ft=isFixedIntTy(this))
				return ft.bits.isConstant();
			import ast.type:isℤmodTy;
			if(auto zmt=isℤmodTy(this))
				return zmt.N.isConstant();
		}
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
	Declaration newFunctionVar=null; // `once` → `spent` replacement
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
	mixin PrecedenceToString;
	override @property int lprec(){ return lbp!op; }
	override @property int rprec(){ return rbp!op; }
	static if(op==Tok!"→"){
		CaptureAnnotation captureAnnotation;
		Annotation annotation;
		bool isLifted;
		this(Expression left, Expression right,CaptureAnnotation captureAnnotation, Annotation annotation,bool isLifted){
			super(left,right); this.captureAnnotation=captureAnnotation; this.annotation=annotation; this.isLifted=isLifted;
		}
		override BinaryExp!op copyImpl(CopyArgs args){
			return new BinaryExp!op(e1.copy(args),e2.copy(args),captureAnnotation,annotation,isLifted);
		}
		override string toStringImpl(int cl,int cr){
			return _brk(e1.toStringImpl(cl,lbp!op) ~ " "~captureAnnotationToString(captureAnnotation)~TokChars!op~annotationToString(annotation)~" "~e2.toStringImpl(rbp!op,cr),cl,cr);
		}
	}else{
		this(Expression left, Expression right){super(left,right);}
		override BinaryExp!op copyImpl(CopyArgs args){
			return new BinaryExp!op(e1.copy(args),e2.copy(args));
		}
		override string toStringImpl(int cl,int cr){
			return _brk(e1.toStringImpl(cl,lbp!op) ~ " "~TokChars!op~" "~e2.toStringImpl(rbp!op,cr),cl,cr);
		}
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
			import ast.semantic_:unwrap;
			auto e1u=unwrap(e1);
			if(auto id=cast(Identifier)e1u){
				auto decl=cast(VarDecl)id.meaning;
				return dg(decl);
			}
			if(auto tpl1=cast(TupleExp)e1u){
				foreach(e;tpl1.e){
					auto id=cast(Identifier)e;
					if(!id) continue;
					auto decl=cast(VarDecl)id.meaning;
					if(auto r=dg(decl)) return r;
				}
				return 0;
			}
			if(auto ce=cast(CallExp)e1u){
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
			if(auto ce=cast(CatExp)e1u){
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
	override BinaryExp!op substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){
		auto ne1=e1.substitute(subst,tt);
		auto ne2=e2.substitute(subst,tt);
		if(ne1 is e1&&ne2 is e2) return this;
		static if(op==Tok!"→"){
			auto r=new BinaryExp!op(ne1,ne2,captureAnnotation,annotation,isLifted);
		}else{
			auto r=new BinaryExp!op(ne1,ne2);
		}
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
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
		if(ne1 is e1 && ne2 is e2) return this;
		static if(op == Tok!"→") {
			return new BinaryExp!op(ne1, ne2, captureAnnotation, annotation, isLifted);
		} else {
			return new BinaryExp!op(ne1, ne2);
		}
	}

	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto be=cast(BinaryExp!op)rhs;
		return be && isEqual(e1,be.e1,&ctx)&&isEqual(e2,be.e2,&ctx);
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

	mixin PrecedenceToString;
	override string toStringImpl(int cl,int cr){
		return _brk(e.toStringImpl(cl,lbp!(Tok!"."))~"."~f.toString(),cl,cr);
	}

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		return e.freeVarsImpl(dg);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(e);
	}
	override FieldExp substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){
		auto ne=e.substitute(subst,tt);
		if(ne is e) return this;
		auto r=new FieldExp(ne,f);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
		auto fe=cast(FieldExp)rhs;
		if(!fe||f!=fe.f) return false;
		return e.unify(fe.e,subst,meet);
	}
	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto fe=cast(FieldExp)rhs;
		if(!fe||!isEqual(f,fe.f,&ctx)) return false;
		return isEqual(e,fe.e,&ctx);
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
	override string toString(){
		bool othwForgets=othw&&othw.blscope_&&(othw.blscope_.forgottenVars.length||othw.blscope_.forgottenVarsOnEntry.length);
		return _brk("if "~cond.toString() ~ " " ~ then.toString() ~ (othw&&othw.s.length||othwForgets?" else " ~ (!othwForgets&&othw.s.length==1&&cast(IteExp)othw.s[0]?othw.s[0].toString():othw.toString()):""));
	}
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
	override IteExp substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){
		import ast.substitute: ttTransitionIte;
		if(tt) return cast(IteExp)ttTransitionIte(this,subst,tt);
		auto ncond=cond.substitute(subst,tt);
		auto nthen=cast(CompoundExp)then.substitute(subst,tt);
		auto nothw=othw?cast(CompoundExp)othw.substitute(subst,tt):null;
		assert(!!nthen && !!nothw==!!othw);
		if(ncond is cond&&nthen is then&&nothw is othw) return this;
		auto r=new IteExp(ncond,nthen,nothw);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
		auto ite=cast(IteExp)rhs;
		if(!ite) return false;
		return cond.unify(ite.cond,subst,meet)&&then.unify(ite.then,subst,meet)
			&&(!othw&&!ite.othw||othw&&ite.othw&&othw.unify(ite.othw,subst,meet));
	}
	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto ite=cast(IteExp)rhs;
		if(!ite) return false;
		return isEqual(cond,ite.cond,&ctx)&&isEqual(then,ite.then,&ctx)
			&&isEqual(othw,ite.othw,&ctx);
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
	override string toString(){ return _brk("with "~trans.toString()~" do "~bdy.toString()~(itrans?" /+"~itrans.toString()~"+/":"")); }
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
			assert(!!de,text(this," ",e," ",typeid(e)));
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

struct ForRange{
	bool leftExclusive;
	Expression left;
	Expression step;
	bool rightExclusive;
	Expression right;
	Location loc()in{ // TODO: store full extent?
		assert(!!this);
	}do{
		return left.loc.to(right.loc);
	}
	bool opCast(T:bool)(){ return left&&right; }

	string toString()in{
		assert(!!this);
	}do{
		return (leftExclusive?"(":"[")~left.toString()~".."~(step?step.toString()~"..":"")~right.toString()~(rightExclusive?")":"]");
	}

	ForRange copy(Expression.CopyArgs args)in{
		assert(!!this);
	}do{
		return ForRange(leftExclusive,left.copy(args),step?step.copy(args):null,rightExclusive,right.copy(args));
	}

	ForRange copyReversed(){
		auto nleftExclusive=rightExclusive;
		auto nleft=right.copy();
		auto nrightExclusive=leftExclusive;
		auto nright=left.copy();
		auto ostep=step?step.copy():null;
		if(!ostep){
			import ast.reverse:constantExp; // TODO: move?
			ostep=constantExp(1);
			ostep.loc=left.loc.to(right.loc);
		}
		auto nstep=new UMinusExp(ostep);
		nstep.loc=ostep.loc;
		return ForRange(nleftExclusive,nleft,nstep,nrightExclusive,nright);
	}

	bool isTotal()in{
		assert(!!this);
	}do{
		return left.isTotal()&&(!step||step.isTotal)&&right.isTotal();
	}

	int componentsImpl(scope int delegate(Expression) dg)in{
		assert(!!this);
	}do{
		if(auto r=dg(left)) return r;
		if(step) if(auto r=dg(step)) return r;
		if(auto r=dg(right)) return r;
		return 0;
	}

	ForRange eval()in{
		assert(!!this);
	}do{
		auto left=this.left.eval();
		auto step=this.step?this.step.eval():this.step;
		auto right=this.right.eval();
		return ForRange(leftExclusive,left,step,rightExclusive,right);
	}
	Annotation getAnnotation(){
		auto r=left.getAnnotation();
		if(step) r=min(r,step.getAnnotation());
		r=min(r,right.getAnnotation());
		return r;
	}

	// semantic information
	Expression elementType(){
		auto r=joinTypes(left.type, right.type);
		if(r==ℤt(true)){
			if(isSubtype(left.type,ℕt(true))&&(!step||isSubtype(step.type,ℕt(true))))
				return ℕt(true);
			if(isSubtype(right.type,ℕt(true))&&step){
				if(auto val=step.asIntegerConstant(true)){
					if(val.get()<0)
						return ℕt(true);
				}
			}
		}
		return r;
	}
}

struct ForContainer{
	Expression e;
	Location loc()in{
		assert(!!this);
	}do{
		return e.loc;
	}
	bool opCast(T:bool)(){ return !!e; }

	string toString()in{
		assert(!!this);
	}do{
		return e.toString();
	}

	ForContainer copy(Expression.CopyArgs args)in{
		assert(!!this);
	}do{
		return ForContainer(e.copy(args));
	}

	ForContainer copyReversed()in{
		assert(!!this);
	}do{
		// TODO
		return ForContainer.init;
	}

	bool isTotal()in{
		assert(!!this);
	}do{
		return e.isTotal();
	}

	int componentsImpl(scope int delegate(Expression) dg)in{
		assert(!!this);
	}do{
		return dg(e);
	}

	ForContainer eval()in{
		assert(!!this);
	}do{
		return ForContainer(e.eval());
	}
	Annotation getAnnotation(){
		return e.getAnnotation();
	}

	// semantic information
	Expression elementType(){
		if(auto vec=cast(VectorTy)e.type)
			return vec.next;
		if(auto arr=cast(ArrayTy)e.type)
			return arr.next;
		if(auto tpl=cast(TupleTy)e.type){
			Expression ety=bottom;
			foreach(ty;tpl.types)
				ety=joinTypes(ety,ty);
			return ety;
		}
		return null;
	}
}

struct ForAggregate{
	ForRange range;
	ForContainer container;
	this(ForRange range){ this.range=range; }
	this(ForContainer container){ this.container=container; }
	ForRange isRange(){ return range; }
	ForContainer isContainer(){ return container; }
	bool opCast(T:bool)(){ return range||container; }

	Location loc()=>fwd!"loc"();

	private auto fwd(string method,T...)(auto ref T args)in{
		assert(!!this);
	}do{
		import core.lifetime:forward;
		if(range){
			return __traits(getMember,range,method)(forward!args);
		}else{
			assert(!!container);
			return __traits(getMember,container,method)(forward!args);
		}
	}
	private auto fwdWrap(string method,T...)(auto ref T args)in{
		assert(!!this);
	}do{
		import core.lifetime:forward;
		if(range){
			return ForAggregate(__traits(getMember,range,method)(forward!args));
		}else{
			return ForAggregate(__traits(getMember,container,method)(forward!args));
		}
	}

	string toString()=>fwd!"toString"();

	ForAggregate copy(Expression.CopyArgs args)=>fwdWrap!"copy"(args);
	ForAggregate copyReversed()=>fwdWrap!"copyReversed"();

	bool isTotal()=>fwd!"isTotal";
	int componentsImpl(scope int delegate(Expression) dg)=>fwd!"componentsImpl"(dg);
	ForAggregate eval()=>fwdWrap!"eval"();
	Annotation getAnnotation()=>fwd!"getAnnotation"();

	// semantic information
	Expression elementType()=>fwd!"elementType"();
}

class ForExp: Expression{
	Identifier var;
	Expression pattern;
	ForAggregate aggr;
	CompoundExp bdy;
	this(Identifier var,Expression pattern,ForAggregate aggr,CompoundExp bdy){
		this.var=var;
		this.pattern=pattern;
		this.aggr=aggr;
		this.bdy=bdy;
	}
	override ForExp copyImpl(CopyArgs args){
		auto r=new ForExp(var?var.copy(args):null,pattern?pattern.copy(args):null,aggr.copy(args),bdy.copy(args));
		if(args.preserveSemantic){
			enforce(!fescope_&&!loopVar,"TODO");
		}
		return r;
	}
	final string toStringNoBody(){
		return "for "~(pattern?pattern.toString():var?var.toString():"_")~" in "~aggr.toString();
	}
	override string toString(){ return _brk(toStringNoBody()~bdy.toString()); }
	override @property string kind(){ return "for loop"; }
	override bool isCompound(){ return true; }

	override bool isTotal(){ return aggr.isTotal()&&bdy.isTotal(); }

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
		auto r=new CompoundExp(s.map!(e=>e.copy(args)).array);
		if(args.mapScope) r.blscope_=cast(BlockScope)args.mapScope(blscope_);
		return r;
	}

	override string toString(){
		Expression[] flat;
		void rec(Expression[] s){
			foreach(e;s){
				if(auto ce=cast(CompoundExp)e){
					if(!ce.blscope_){
						rec(ce.s);
						continue;
					}
				}
				flat~=e;
			}
		}
		rec(s);
		return "{"~(blscope_&&blscope_.forgottenVarsOnEntry.length?text(" /+",blscope_.forgottenVarsOnEntry,"+/"):"")~"\n"~indent(join(map!(a=>a.toString()~(a.isCompound()?"":";"))(flat),"\n"))~"\n}"~(blscope_&&blscope_.forgottenVars.length?text(" /+",blscope_.forgottenVars,"+/"):"");
	}
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
	override Expression substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){
		auto ns=s.dup;
		bool chg=false;
		foreach(i,ref x;ns){ x=x.substitute(subst,tt); if(x !is s[i]) chg=true; }
		if(!chg) return this;
		auto r=new CompoundExp(ns);
		r.loc=loc;
		return r;

	}
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
		auto ce=cast(CompoundExp)rhs;
		if(!ce) return false;
		if(s.length!=ce.s.length) return false;
		return iota(s.length).all!(i=>s[i].unify(ce.s[i],subst,meet));
	}
	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto ce=cast(CompoundExp)rhs;
		if(!ce) return false;
		// compare up to alpha-equivalence: pair up the declarations bound by
		// corresponding statements, then compare under the pairing
		return ctx.stmtsEquals(s,ce.s);
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
	override @property string kind(){ return "tuple expression"; }
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
	override TupleExp substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){
		auto ne=e.dup;
		bool chg=false;
		foreach(i,ref x;ne){ x=x.substitute(subst,tt); if(x !is e[i]) chg=true; }
		if(!chg) return this;
		auto r=new TupleExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
		auto te=cast(TupleExp)rhs;
		if(!te||e.length!=te.e.length) return false;
		return all!(i=>e[i].unify(te.e[i],subst,meet))(iota(e.length));
	}
	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto tpl=cast(TupleExp)rhs;
		if(!tpl||e.length!=tpl.e.length) return false;
		return all!(i=>isEqual(e[i],tpl.e[i],&ctx))(iota(e.length));
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

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		import ast.substitute:functionDefFreeVarsImpl;
		return functionDefFreeVarsImpl(fd,dg);
	}
	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto r=cast(LambdaExp)rhs;
		if(!r) return false;
		// compare the definitions structurally (up to alpha-equivalence)
		return ctx.functionDefEquals(fd,r.fd);
	}
	override Expression substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){
		import ast.substitute:substituteFunctionDefExp;
		auto nfd=cast(FunctionDef)substituteFunctionDefExp(fd,subst,false,tt);
		if(nfd is fd) return this;
		auto r=new LambdaExp(orig,nfd);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
		return this is rhs; // TODO
	}
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

class LetExp: Expression{
	CompoundExp s;
	Expression e;
	this(CompoundExp s,Expression e){
		this.s=s;
		this.e=e;
	}
	override LetExp copyImpl(CopyArgs args){
		auto ns=s.copy(args), ne=e.copy(args);
		if(args.preserveMeanings){
			MapSX!(Declaration,Declaration) bound;
			FunctionDef[] defs;
			void pair(Expression src,Expression cpy){
				if(auto sfd=cast(FunctionDef)src){
					if(auto cfd=cast(FunctionDef)cpy){ bound[sfd]=cfd; defs~=cfd; }
					return;
				}
				if(auto svd=cast(VarDecl)src){
					if(auto cvd=cast(VarDecl)cpy) bound[svd]=cvd;
					return;
				}
				if(auto ce=cast(CommaExp)src){
					if(auto ce2=cast(CommaExp)cpy){ pair(ce.e1,ce2.e1); pair(ce.e2,ce2.e2); }
					return;
				}
				if(auto ce=cast(CompoundExp)src){
					if(auto ce2=cast(CompoundExp)cpy)
						foreach(i,x;ce.s) if(i<ce2.s.length) pair(x,ce2.s[i]);
					return;
				}
			}
			foreach(i,stmt;s.s) if(i<ns.s.length) pair(stmt,ns.s[i]);
			if(bound.length){
				int rebind(Identifier id){
					if(auto p = bound.getPtr(id.meaning)) id.meaning=*p;
					return 0;
				}
				import ast.substitute: statementFreeVarsImpl, computeCapturesFromBody;
				foreach(stmt;ns.s) statementFreeVarsImpl(stmt,&rebind);
				ne.freeVarsImpl(&rebind);
				foreach(fd;defs) computeCapturesFromBody(fd);
			}
		}
		return new LetExp(ns,ne);
	}
	Expression isForward(bool allowForgets=false){
		if(s.blscope_) return null;
		if(allowForgets?s.s.length==0||s.s.length>2:s.s.length!=1) return null;
		auto de=cast(DefineExp)s.s[0];
		if(!de) return null;
		auto id=cast(Identifier)e;
		if(!id||id.implicitDup) return null;
		auto dId=cast(Identifier)de.e1;
		if(!dId||dId.implicitDup) return null;
		if(id.id!=dId.id) return null;
		if(s.s.length>=2){
			assert(allowForgets);
			if(!s.s[1..$].all!((cs){
				auto fe=cast(ForgetExp)cs;
				if(!fe) return false;
				if(!!fe.val) return false;
				return true;
			}))
				return null;
		}
		return de.e2;
	}
	override string toString(){
		//if(auto fwd=isForward()) return fwd.toString()~"/+*+/";
		if(s.s.length==1) return _brk(text("let ",s.s[0]," in ",e));
		return _brk(text("let",s," in ",e));
	}

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		import ast.substitute:blockFreeVarsImpl;
		return blockFreeVarsImpl(s.s,e,dg);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto fwd=isForward(true)){
			if(auto r=dg(fwd)) return r;
			foreach(cs;s.s[1..$])
				if(auto r=dg(cs))
					return r;
			return 0;
		}else{
			foreach(cs;s.components)
				if(auto r=dg(cs))
					return r; // TODO: improve
			return dg(e);
		}
	}
	override Expression substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){
		import ast.substitute: ttTransitionLet;
		if(tt) return ttTransitionLet(this,subst,tt);
		MapSX!(Id,Expression) active;
		foreach(k,v;subst) if(freeVarsImpl((id)=>id.id==k?1:0)) active[k]=v;
		if(!active.length) return this;
		SetX!Id taken;
		foreach(k,v;subst) taken[k]=[];
		freeVarsImpl((id){ taken[id.id]=[]; return 0; });
		import ast.substitute:collectBoundNamesImpl,BlockSubst,substituteBlockCompound,substituteLValue;
		foreach(stmt;s.s) collectBoundNamesImpl(stmt,taken);
		MapSX!(Declaration,Declaration) declMap;
		auto ctx=BlockSubst(active,MapSX!(Id,Id).init,&taken,&declMap,false);
		auto ns=substituteBlockCompound(s,ctx);
		auto ne=substituteLValue(e,ctx);
		if(ns is s&&ne is e&&!ctx.changed) return this;
		auto r=new LetExp(ns,ne);
		r.loc=loc;
		return r;
	}
	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto r=cast(LetExp)rhs;
		if(!r) return false;
		if(!ctx.stmtsEquals(s.s,r.s.s)) return false;
		return isEqual(e,r.e,&ctx);
	}
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
		return this is rhs; // TODO
	}
	override Expression evalImpl(){
		if(auto fwd=isForward()) return fwd;
		Expression[] flat;
		bool flatten(Expression[] ss){
			foreach(x;ss){
				if(auto ce=cast(CompoundExp)x){
					if(ce.blscope_) return false;
					if(!flatten(ce.s)) return false;
					continue;
				}
				flat~=x;
			}
			return true;
		}
		if(!flatten(s.s)) return this;
		alias stmts=flat;
		foreach(stmt;stmts){
			auto de=cast(DefineExp)stmt;
			if(!de) return this;
			if(!cast(Identifier)de.e1) return this;
			if(!de.e2.type||!de.e2.type.isClassical()) return this;
			if(de.e2.getAnnotation()<pure_) return this;
			if(!de.e2.isSemCompleted()||de.e2.isSemError()) return this;
		}
		SetX!Id bound;
		foreach(stmt;stmts) bound[(cast(Identifier)(cast(DefineExp)stmt).e1).id]=[];
		if(type){
			bool bad=false;
			type.freeVarsImpl((id){ if(id.id in bound){ bad=true; return 1; } return 0; });
			if(bad) return this;
		}
		bool okUses(Expression x){
			bool ok=true;
			x.freeVarsImpl((id){
				if(id.id in bound&&!(id.constLookup||id.implicitDup)){ ok=false; return 1; }
				return 0;
			});
			return ok;
		}
		foreach(stmt;stmts) if(!okUses((cast(DefineExp)stmt).e2)) return this;
		if(!okUses(e)) return this;
		MapSX!(Id,Expression) cur;
		foreach(stmt;stmts){
			auto de=cast(DefineExp)stmt;
			auto id=cast(Identifier)de.e1;
			auto rhs=cur.length?de.e2.substitute(cur):de.e2.eval();
			cur[id.id]=rhs;
		}
		return cur.length?e.substitute(cur):e.eval();
	}
	override Annotation getAnnotation(){ return min(s.getAnnotation(),e.getAnnotation()); }
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
	override @property string kind(){ return "vector expression"; }
	override bool isConstant(){ return e.all!(x=>x.isConstant()); }
	override bool isTotal(){ return e.all!(x=>x.isTotal()); }

	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto r=cast(VectorExp)rhs;
		if(!r||e.length!=r.e.length) return false;
		return all!(i=>isEqual(e[i],r.e[i],&ctx))(iota(e.length));
	}

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		foreach(x;e) if(auto r=x.freeVarsImpl(dg)) return r;
		return 0;
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		foreach(x;e) if(auto r=dg(x)) return r;
		return 0;
	}
	override VectorExp substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){
		auto ne=e.dup;
		bool chg=false;
		foreach(i,ref x;ne){ x=x.substitute(subst,tt); if(x !is e[i]) chg=true; }
		if(!chg) return this;
		auto r=new VectorExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
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

class VectorForExp: Expression{
	ForExp fe;
	this(ForExp fe)in{
		assert(fe.bdy&&fe.bdy.s.length==1);
	}do{
		this.fe=fe;
	}
	override VectorForExp copyImpl(CopyArgs args){
		if(args.preserveSemantic) enforce(!fd&&!len,"TODO");
		return new VectorForExp(fe.copy(args));
	}
	override string toString(){ return _brk("["~fe.bdy.s[0].toString()~" "~fe.toStringNoBody()~"]"); }
	override @property string kind(){ return "vector comprehension"; }
	override bool isConstant(){ return false; } // TODO?
	override bool isTotal(){ return fe.isTotal(); }

	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto vfe=cast(VectorForExp)rhs;
		if(!vfe) return false;
		return isEqual(fe,vfe.fe,&ctx);
	}

	// semantic information
	FunctionDef fd; // synthesized function mapping one element of the aggregate to one element of the result
	Expression len; // length of the result, `null` if the aggregate is an array of unknown length

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		if(auto r=fe.aggr.componentsImpl(e=>e.freeVarsImpl(dg))) return r;
		if(fd){
			import ast.substitute:functionDefFreeVarsImpl;
			return functionDefFreeVarsImpl(fd,dg);
		}
		SetX!Id bound;
		if(fe.var) bound[fe.var.id]=[];
		import ast.substitute:defineLhsBoundVarsImpl;
		if(fe.pattern) fe.pattern.defineLhsBoundVarsImpl((id){ bound[id.id]=[]; return 0; });
		return fe.bdy.s[0].freeVarsImpl((id){ return id.id in bound?0:dg(id); });
	}
	override Expression substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){ return this; } // TODO
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
		return combineTypes(this,rhs,meet)!is null; // TODO
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		if(fd){ // analyzed: like a lambda applied to the aggregate
			foreach(decl,ids;fd.captures){
				foreach(c;ids)
					if(auto r=dg(c))
						return r;
			}
			return fe.aggr.componentsImpl(dg);
		}
		if(auto r=dg(fe.bdy.s[0])) return r;
		return fe.aggr.componentsImpl(dg);
	}
	override Expression evalImpl(){
		if(fd) return this;
		auto naggr=fe.aggr.eval();
		auto ns=fe.bdy.s[0].eval();
		if(naggr is fe.aggr&&ns is fe.bdy.s[0])
			return this;
		auto nbdy=new CompoundExp([ns]);
		nbdy.loc=fe.bdy.loc;
		nbdy.type=fe.bdy.type;
		nbdy.setSemEvaluated();
		auto nfe=new ForExp(fe.var,fe.pattern,naggr,nbdy);
		nfe.loc=nfe.loc;
		nfe.type=fe.type;
		nfe.setSemEvaluated();
		return new VectorForExp(nfe);
	}
	override Annotation getAnnotation(){
		auto r=fe.aggr.getAnnotation();
		if(fd){
			import ast.semantic_:typeForDecl;
			if(auto ft=cast(FunTy)typeForDecl(fd)){
				return min(r,ft.annotation);
			}
		}
		return min(fe.bdy.s[0].getAnnotation(),r);
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
		if(args.mapDecl) r.forgottenVars=forgottenVars.map!(d=>args.mapDecl(d)).array;
		return r;
	}
	override string toString(){ return "return"~(e?" "~e.toString():"")~(forgottenVars.length?text(" /+",forgottenVars,"+/"):""); }
	override @property string kind(){ return "return statement"; }
	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto r=cast(ReturnExp)rhs;
		if(!r) return false;
		return isEqual(e,r.e,&ctx);
	}

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
	override AssertExp substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){
		auto ne=e.substitute(subst,tt);
		if(ne is e) return this;
		auto r=new AssertExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref MapSX!(Id,UnificationResult) subst,bool meet){
		auto ae=cast(AssertExp)rhs;
		if(!ae) return false;
		return e.unify(ae.e,subst,meet);
	}
	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto ae=cast(AssertExp)rhs;
		return ae&&isEqual(e,ae.e,&ctx);
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
	override bool isEqualImpl(Expression rhs,ref EqualityContext ctx){
		auto r=cast(ForgetExp)rhs;
		if(!r) return false;
		return isEqual(var,r.var,&ctx)&&isEqual(val,r.val,&ctx);
	}
	// semantic information
	bool isStatement=false; // TODO: get rid of this
}

alias CommaExp=BinaryExp!(Tok!",");
alias AssignExp=BinaryExp!(Tok!"←");
alias DefineExp=BinaryExp!(Tok!":=");
alias OrElseAssignExp=BinaryExp!(Tok!"||←");
alias AndThenAssignExp=BinaryExp!(Tok!"&&←");
alias OrAssignExp=BinaryExp!(Tok!"∨←");
alias XorAssignExp=BinaryExp!(Tok!"⊻←");
alias AndAssignExp=BinaryExp!(Tok!"∧←");
alias AddAssignExp=BinaryExp!(Tok!"+←");
alias SubAssignExp=BinaryExp!(Tok!"-←");
alias NSubAssignExp=BinaryExp!(Tok!"sub←");
alias MulAssignExp=BinaryExp!(Tok!"·←");
alias DivAssignExp=BinaryExp!(Tok!"/←");
alias IDivAssignExp=BinaryExp!(Tok!"div←");
alias ModAssignExp=BinaryExp!(Tok!"%←");
alias PowAssignExp=BinaryExp!(Tok!"^←");
alias CatAssignExp=BinaryExp!(Tok!"~←");
alias BitOrAssignExp=BinaryExp!(Tok!"|←");
alias BitXorAssignExp=BinaryExp!(Tok!"⊕←");
alias BitAndAssignExp=BinaryExp!(Tok!"&←");
alias AddExp=BinaryExp!(Tok!"+");
alias SubExp=BinaryExp!(Tok!"-");
alias NSubExp=BinaryExp!(Tok!"sub");
alias MulExp=BinaryExp!(Tok!"·");
alias DivExp=BinaryExp!(Tok!"/");
alias IDivExp=BinaryExp!(Tok!"div");
alias ModExp=BinaryExp!(Tok!"%");
alias PowExp=BinaryExp!(Tok!"^");
alias CatExp=BinaryExp!(Tok!"~");
alias BitOrExp=BinaryExp!(Tok!"|");
alias BitXorExp=BinaryExp!(Tok!"⊕");
alias BitAndExp=BinaryExp!(Tok!"&");
alias UPlusExp=UnaryExp!(Tok!"+");
alias UMinusExp=UnaryExp!(Tok!"-");
alias UNotExp=UnaryExp!(Tok!"¬");
alias UBitNotExp=UnaryExp!(Tok!"~");
alias LtExp=BinaryExp!(Tok!"<");
alias LeExp=BinaryExp!(Tok!"≤");
alias GtExp=BinaryExp!(Tok!">");
alias GeExp=BinaryExp!(Tok!"≥");
alias EqExp=BinaryExp!(Tok!"=");
alias NeqExp=BinaryExp!(Tok!"≠");
alias OrElseExp=BinaryExp!(Tok!"||");
alias AndThenExp=BinaryExp!(Tok!"&&");
alias OrExp=BinaryExp!(Tok!"∨");
alias XorExp=BinaryExp!(Tok!"⊻");
alias AndExp=BinaryExp!(Tok!"∧");
alias Exp=Expression;


template isOneOf(T,List...){
	enum isOneOf=List.length!=0&&(is(T==List[0])||isOneOf!(T,List[1..$]));
}
alias declKinds=AliasSeq!(
	FunctionDef,DatDecl,DefineExp,CommaExp,ImportExp
);
alias assignKinds=AliasSeq!(
	AssignExp,OrElseAssignExp,AndThenAssignExp,OrAssignExp,XorAssignExp,AndAssignExp,
	AddAssignExp,SubAssignExp,NSubAssignExp,MulAssignExp,DivAssignExp,IDivAssignExp,
	ModAssignExp,PowAssignExp,CatAssignExp,BitOrAssignExp,BitXorAssignExp,BitAndAssignExp
);
private alias stmKindsCommon=AliasSeq!(
	CallExp,TypeAnnotationExp,CompoundExp,IteExp,ReturnExp,FunctionDef,CommaExp,
	DefineExp,assignKinds,
	ForExp,WhileExp,RepeatExp,ObserveExp,CObserveExp,AssertExp,ForgetExp
);
static if(language==silq) alias stmKinds=AliasSeq!(stmKindsCommon,WithExp);
else static if(language==psi) alias stmKinds=AliasSeq!(stmKindsCommon,DatDecl);
else alias stmKinds=stmKindsCommon;
// statement kinds that are handled by analyzing them as expressions
alias exprStmKinds=AliasSeq!(CallExp,TypeAnnotationExp,ObserveExp,CObserveExp,AssertExp,ForgetExp);
private alias expKindsCommon=AliasSeq!(
	IteExp,AssertExp,LiteralExp,LetExp,LambdaExp,CallExp,ForgetExp,Identifier,
	FieldExp,IndexExp,SliceExp,TupleExp,VectorExp,TypeAnnotationExp,
	UPlusExp,UMinusExp,UNotExp,UBitNotExp,
	AddExp,SubExp,NSubExp,MulExp,DivExp,IDivExp,ModExp,PowExp,
	BitOrExp,BitXorExp,BitAndExp,AndThenExp,OrElseExp,OrExp,XorExp,AndExp,
	LtExp,LeExp,GtExp,GeExp,EqExp,NeqExp,CatExp,VectorForExp,
	ClassicalTy,ProductTy,ArrayTy,TupleTy,VectorTy,VariadicTy,TypeTy,
	QNumericTy,BottomTy,NumericTy,StringTy
);
static if(language==psi) alias expKinds=AliasSeq!(expKindsCommon,PlaceholderExp);
else alias expKinds=expKindsCommon;
alias unanalyzedExpKinds=AliasSeq!(
	CommaExp,WildcardExp,TypeofExp,BinaryExp!(Tok!"×"),BinaryExp!(Tok!"→")
);

private noreturn unknownDeclError(T...)(Expression s,auto ref T args){
	assert(0,text("unknown declaration: ",s?typeid(s):null," ",s));
}
auto dispatchDecl(alias f,alias default_=unknownDeclError,T...)(Expression d,auto ref T args){
	import core.lifetime:forward;
	static foreach(K;declKinds) if(auto x=cast(K)d) return f(x,forward!args);
	return default_(d,args);
}

private noreturn unknownStmError(T...)(Expression s,auto ref T args){
	assert(0,text("unknown statement: ",s?typeid(s):null," ",s));
}
auto dispatchStm(alias f,alias default_=unknownStmError,bool unanalyzed=false,T...)(Expression s,auto ref T args){
	import core.lifetime:forward;
	static if(unanalyzed) if(auto idx=cast(IndexExp)s) return f(idx,forward!args);
	static foreach(K;stmKinds) if(auto x=cast(K)s) return f(x,forward!args);
	return default_(s,args);
}

// TODO: type dispatch

private noreturn unknownExpError(T...)(Expression e,auto ref T args){
	assert(0,text("unknown expression: ",e?typeid(e):null," ",e));
}
auto dispatchExp(alias f,alias default_=unknownExpError,bool unanalyzed=false,T...)(Expression e,auto ref T args){
	import core.lifetime:forward;
	static foreach(K;expKinds) if(auto x=cast(K)e) return f(x,forward!args);
	static if(unanalyzed) static foreach(K;unanalyzedExpKinds) if(auto x=cast(K)e) return f(x,forward!args);
	return default_(e,forward!args);
}
