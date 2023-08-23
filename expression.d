// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.expression;

import std.array, std.algorithm, std.range, std.conv, std.string, std.exception;

import ast.lexer, ast.parser, ast.scope_, ast.type, ast.declaration, util;
import astopt;

enum SemState{
	initial,
	started,
	completed,
	error,
}

abstract class Node{
	// debug auto cccc=0;
	Location loc;
	abstract @property string kind();

	// semantic information
	SemState sstate;
}


abstract class Expression: Node{
	Expression type;
	int brackets=0;

	struct CopyArgs{
		bool preserveSemantic=false;
	}
	abstract Expression copyImpl(CopyArgs args);
	final T copy(this T)(CopyArgs args=CopyArgs.init){
		auto self=cast(T)this;
		auto r=self.copyImpl(args);
		assert(!!r);
		if(args.preserveSemantic){
			r.sstate=sstate;
			r.type=type;
		}
		r.brackets=brackets;
		r.loc=loc;
		r.byRef=byRef;
		return r;
	}

	override string toString(){return _brk("{}()");}
	protected string _brk(string s){return std.array.replicate("(",brackets)~s~std.array.replicate(")",brackets);}

	override @property string kind(){return "expression";}
	bool isCompound(){ return false; }
	bool isConstant(){ return false; }

	final Expression eval(){
		auto ntype=!type?null:type is this?this:type.eval();
		auto r=evalImpl(ntype);
		if(!r.type) r.type=ntype;
		else if(r is this) return r;
		else assert(r.type==ntype,text(this," ",typeid(this)," ",r," ",r.type," ",ntype));
		if(!r.loc.line) r.loc=loc;
		r.sstate=SemState.completed;
		return r;
	}
	abstract Expression evalImpl(Expression ntype);

	final Expression substitute(string name,Expression exp){
		return substitute([name:exp]);
	}
	final Expression substitute(Expression[string] subst){
		auto r=substituteImpl(subst);
		if(type&&!r.type){
			if(type == this) r.type=r;
			else r.type=type.substitute(subst);
		}
		return r;
	}
	abstract Expression substituteImpl(Expression[string] subst); // TODO: name might be free in the _types_ of subexpressions

	final bool unify(Expression rhs,ref Expression[string] subst, bool meet){
		return unifyImpl(rhs,subst,meet) || eval().unifyImpl(rhs.eval(),subst,meet);
	}
	abstract bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet);

	abstract int freeVarsImpl(scope int delegate(Identifier) dg);
	static struct FreeVars{
		Expression self;
		int opApply(scope int delegate(Identifier) dg)in{
			assert(!!self);
		}do{
			if(auto r=self.freeVarsImpl(dg)) return r;
			if(self.type != self)
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
	final bool hasFreeVar(string name)in{
		assert(!!this);
	}do{
		foreach(var;freeVars){
			if(var.name == name)
				return true;
		}
		return false;
	}
	final bool hasAnyFreeVar(R)(R r){
		foreach(var;freeVars){
			if(r.canFind(var.name))
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
	Annotation getAnnotation(){
		return Annotation.none;
	}
	static if(language==silq){
		final bool isQfree(){ return getAnnotation()>=Annotation.qfree; }
		final bool isMfree(){ return getAnnotation()>=Annotation.mfree; }
	}else static if(language==psi){
		final bool isPure(){ return getAnnotation()>=Annotation.pure_; }
	}

	// semantic information
	bool constLookup=true;
	bool byRef=false;
}

mixin template VariableFree(){
	override int freeVarsImpl(scope int delegate(Identifier)){ return 0; }
	override Expression substituteImpl(Expression[string] subst){ return this; }
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
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
		return e.isConstant();
	}
	override int freeVarsImpl(scope int delegate(Identifier) dg){
		if(auto r=e.freeVarsImpl(dg)) return r;
		return (type?type:t).freeVarsImpl(dg);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(e)) return r;
		return dg(type?type:t);
	}
	override TypeAnnotationExp substituteImpl(Expression[string] subst){
		auto ne=e.substitute(subst);
		auto nt=t.substitute(subst);
		if(ne==e&&nt==t) return this;
		auto r=new TypeAnnotationExp(ne,nt,annotationType);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		return e.unify(rhs,subst,meet);
	}
	override Annotation getAnnotation(){
		return e.getAnnotation();
	}
	override Expression evalImpl(Expression ntype){
		auto ne = e.eval(), nt = t.eval();
		if(ne == e && nt == t && ntype == type) return this;
		return new TypeAnnotationExp(ne,nt,annotationType);
	}
}

// workaround for the bug:
UnaryExp!(Tok!"&") isAddressExp(Expression self){return cast(UnaryExp!(Tok!"&"))self;}

class ErrorExp: Expression{
	this(){}//{sstate = SemState.error;}
	override string toString(){return _brk("__error");}
	override ErrorExp copyImpl(CopyArgs args){
		return new ErrorExp();
	}

	override Expression evalImpl(Expression ntype){ return this; }
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
		r.type=i>=0?ℕt(true):ℤt(true);
		r.sstate=SemState.completed;
		return r;
	}
	static LiteralExp makeString(string s, Location loc=Location.init){
		Token tok;
		tok.type=Tok!"``";
		tok.str=s;
		auto r=new LiteralExp(tok);
		r.type=stringTy();
		r.loc=loc;
		r.sstate=SemState.completed;
		return r;
	}
	bool isInteger(){
		return lit.type==Tok!"0";
	}
	bool isZero()in{
		assert(isInteger());
	}do{
		return lit.str=="0";
	}
	bool isNegative()in{
		assert(lit.type==Tok!"0");
	}do{
		return lit.str.startsWith("-");
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
	override bool isConstant(){ return true; }

	override bool opEquals(Object o){
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

	override Annotation getAnnotation(){ return deterministic; }
	override Expression evalImpl(Expression ntype){
		if(ntype == type) return this;
		return new LiteralExp(lit);
	}
	override int componentsImpl(scope int delegate(Expression) dg){ return 0; }
	mixin VariableFree;
}

class Identifier: Expression{
	string name;
	@property auto ptr(){return name.ptr;}
	@property auto length(){return name.length;}
	this(string name){
		static string[string] uniq;
		auto n=uniq.get(name,null);
		if(n !is null) this.name = n;
		else this.name = uniq[name] = name;
	}
	override Identifier copyImpl(CopyArgs args){
		Identifier r;
		if(meaning&&meaning.name&&meaning.name.name.length) r=new Identifier(meaning.name.name); // TODO: this is a hack
		else r=new Identifier(name);
		if(args.preserveSemantic){
			r.meaning=meaning;
			r.substitute=substitute;
			r.scope_=scope_;
			r.calledDirectly=calledDirectly;
			r.indexedDirectly=indexedDirectly;
			static if(language==silq){
				r.checkReverse=checkReverse;
				r.classical=classical;
			}
		}else{
			static if(language==silq){
				r.checkReverse=checkReverse;
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
	override Expression substituteImpl(Expression[string] subst){
		if(name in subst){
			static if(language==silq){
				if(classical)
					if(auto r=subst[name].getClassical())
						return r;
			}
			return subst[name];
		}
		return this;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		if(this==rhs){
			if(name !in subst) return true;
			if(subst[name]&&subst[name]!=this) return false;
			subst[name]=this;
			return true;
		}
		if(name !in subst) return false;
		if(subst[name]==this) return false;
		static if(language==silq){
			if(isType(this)&&isType(rhs))
				if(rhs.isClassical<classical) return false;
		}
		if(subst[name]){
			if(!subst[name].unify(rhs,subst,meet))
				return false;
			if(isType(subst[name])&&isType(rhs))
				if(auto cmb=combineTypes(subst[name],rhs,meet)) // TODO: good?
					subst[name]=cmb;
			return true;
		}
		if(rhs.hasFreeVar(name)) return false; // TODO: fixpoint types
		subst[name]=rhs;
		return true;
	}
	override bool opEquals(Object o){
		if(auto r=cast(Identifier)o){
			return name==r.name && classical==r.classical && meaning==r.meaning;
		}
		return false;
	}

	override Expression getClassical(){
		static if(language==silq){
			assert(isType(this)||isQNumeric(this));
			if(classical) return this;
			if(!meaning) return varTy(name,ctypeTy,true);
			auto r=new Identifier(name);
			r.classical=true;
			r.type=getClassicalTy(type);
			r.meaning=meaning;
			r.sstate=SemState.completed;
			return r;
		}else return this;
	}
	override Expression getQuantum(){
		static if(language==silq){
			assert(isType(this));
			if(isQuantum(this)) return this;
			if(meaning){
				import ast.semantic_:typeForDecl;
				auto prev=typeForDecl(meaning);
				if(isQuantumTy(prev)){
					auto r=new Identifier(name);
					r.classical=false;
					r.meaning=meaning;
					r.type=r.typeFromMeaning;
					assert(isQuantumTy(r.type));
					r.sstate=SemState.completed;
					return r;
				}
			}
			return null;
		}else return null;
	}

	final Expression typeFromMeaning(Declaration meaning){
		if(!meaning) return null;
		import ast.semantic_:typeForDecl;
		auto r=typeForDecl(meaning);
		if(isTypeTy(r)&&classical) return ctypeTy;
		return r;
	}
	final Expression typeFromMeaning(){
		return typeFromMeaning(meaning);
	}

	override Annotation getAnnotation(){ return deterministic; }

	override Expression evalImpl(Expression ntype){
		if(substitute) return getInitializer().evalImpl(ntype);
		if(ntype==type) return this;
		auto r=new Identifier(name);
		r.meaning=meaning;
		static if(language==silq){
			r.classical=classical;
		}
		return r;
	}
	override bool isConstant(){
		if(substitute){
			if(auto init=getInitializer())
				return init.isConstant();
		}
		return super.isConstant();
	}
	Expression getInitializer()in{
		assert(substitute);
	}do{
		auto vd=cast(VarDecl)meaning;
		assert(!!vd);
		return vd.initializer;
	}
	// semantic information:
	Declaration meaning;
	bool lazyCapture=false;
	bool substitute=false;
	Scope scope_;
	bool calledDirectly=false;
	bool indexedDirectly=false;
	static if(language==silq){
		bool checkReverse=true; // (calls to reverse in the frontend implementation of reverse are more liberal)
		bool classical=false;
	}
	else enum classical=true;
}

class PlaceholderExp: Expression{
	Identifier ident;
	this(Identifier ident){ this.ident = ident; }
	override PlaceholderExp copyImpl(CopyArgs args){
		return new PlaceholderExp(ident.copy(args));
	}
	override string toString(){ return _brk("?"); }
	override @property string kind(){ return "placeholder"; }

	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){ return 0; }
}


class UnaryExp(TokenType op): Expression{
	Expression e;
	this(Expression next){e = next;}
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

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		return e.freeVarsImpl(dg);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(e);
	}
	override UnaryExp substituteImpl(Expression[string] subst){
		auto ne=e.substitute(subst);
		if(ne==e) return this;
		auto r=new UnaryExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto ue=cast(typeof(this))rhs;
		if(!ue) return false;
		return e.unify(ue.e,subst,meet);
	}
	override bool opEquals(Object o){
		auto ue=cast(UnaryExp!op)o;
		return ue&&e==ue.e;
	}

	override Annotation getAnnotation(){ return e.getAnnotation(); }

	override Expression evalImpl(Expression ntype){
		auto ne=e.eval();
		static if(op==Tok!"-"){
			if(auto le=cast(LiteralExp)ne){
				if(le.lit.type==Tok!"0"){
					return LiteralExp.makeInteger(-ℤ(le.lit.str)); // TODO: replace literal exp internal representation
				}
			}
		}
		if(ne == e && ntype == type) return this;
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
	override PostfixExp substituteImpl(Expression[string] subst){
		auto ne=e.substitute(subst);
		if(ne==e) return this;
		auto r=new PostfixExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto pe=cast(PostfixExp)rhs;
		if(!pe) return false;
		return e.unify(pe.e,subst,meet);
	}

	override Expression evalImpl(Expression ntype){
		auto ne=e.eval();
		if(ne==e&&ntype==type) return this;
		return new PostfixExp!op(ne);
	}
}

class IndexExp: Expression{ //e[a...]
	Expression e;
	Expression a;
	this(Expression exp, Expression arg){e=exp; a=arg;}
	override IndexExp copyImpl(CopyArgs args){
		return new IndexExp(e.copy(args),a.copy(args));
	}
	override string toString(){
		return _brk(e.toString()~a.tupleToString(true));
	}
	override Expression evalImpl(Expression ntype){
		auto ne=e.eval();
		auto na=a.eval();
		Expression[] exprs;
		if(auto tpl=cast(TupleExp)ne) exprs=tpl.e;
		if(auto arr=cast(ArrayExp)ne) exprs=arr.e;
		if(exprs.length){
			if(auto le=cast(LiteralExp)na){
				if(le.lit.type==Tok!"0"){
					auto idx=ℤ(le.lit.str);
					if(0<=idx&&idx<exprs.length) return exprs[cast(size_t)idx].evalImpl(ntype);
				}
			}
		}
		if(ne==e && na==a && ntype == type) return this;
		return new IndexExp(ne,na);
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
	override IndexExp substituteImpl(Expression[string] subst){
		auto ne=e.substitute(subst);
		auto na=a.substitute(subst);
		if(ne==e&&na==a) return this;
		auto r=new IndexExp(ne,na);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto idx=cast(IndexExp)rhs;
		if(!idx) return false;
		return e.unify(idx.e,subst,meet)&&a.unify(idx.a,subst,meet);
	}
	override bool opEquals(Object rhs){
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
	override Expression evalImpl(Expression ntype){
		auto ne=e.eval(), nl=l.eval(), nr=r.eval();
		Expression[] exprs;
		auto tpl=cast(TupleExp)ne, arr=cast(ArrayExp)ne;
		if(tpl) exprs=tpl.e;
		if(arr) exprs=arr.e;
		if(tpl||arr){
			if(auto le=cast(LiteralExp)nl){
				if(auto re=cast(LiteralExp)nr){
					if(le.lit.type==Tok!"0"&&re.lit.type==Tok!"0"){
						auto lid=ℤ(le.lit.str), rid=ℤ(re.lit.str);
						if(cast(size_t)lid==0 && cast(size_t)rid==exprs.length) return e;
						if(0<=lid&&lid<=rid&&rid<=exprs.length){
							auto rexprs=exprs[cast(size_t)lid..cast(size_t)rid];
							if(tpl){
								auto res=new TupleExp(rexprs);
								res.loc=loc;
								return res;
							}
							if(arr){
								auto res=new ArrayExp(rexprs);
								res.loc=loc;
								return res;
							}
						}
					}
				}
			}
		}
		if(ne==e && nl==l && nr==r && ntype == type) return this;
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
	override SliceExp substituteImpl(Expression[string] subst){
		auto ne=e.substitute(subst);
		auto nl=l.substitute(subst);
		auto nr=r.substitute(subst);
		if(ne==e&&nl==l&&nr==r) return this;
		auto res=new SliceExp(ne,nl,nr);
		res.loc=loc;
		return res;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto sl=cast(SliceExp)rhs;
		return e.unify(sl.e,subst,meet)&&l.unify(sl.l,subst,meet)&&r.unify(sl.r,subst,meet);
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
		return new CallExp(e.copy(args),arg.copy(args),isSquare,isClassical_);
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
	override CallExp substituteImpl(Expression[string] subst){
		auto ne=e.substitute(subst);
		auto narg=arg.substitute(subst);
		if(ne==e&&narg==arg) return this;
		auto r=new CallExp(ne,narg,isSquare,isClassical_);
		r.loc=loc;
		if(sstate==SemState.completed){
			r.type=type.substitute(subst);
			r.sstate=SemState.completed;
		}
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto ce=cast(CallExp)rhs;
		if(!ce) return false;
		return e.unify(ce.e,subst,meet)&&arg.unify(ce.arg,subst,meet);
	}
	override bool opEquals(Object rhs){
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
						import ast.semantic_: ConstResult, InType, expSemContext, callSemantic; // TODO: get rid of this?
						if(!dat.isTuple){
							assert(dat.params.length==1);
							assert(arg != rcall.arg); // (checked at start of function)
							auto combined=combine(dat.params[0].variance,arg,rcall.arg);
							if(!combined) return null;
							return callSemantic(new CallExp(e,combined,isSquare,isClassical_),expSemContext(null,ConstResult.no,InType.yes));
						}
						assert(dat.isTuple);
						auto tup=arg.isTupleTy(), rtup=rcall.arg.isTupleTy();
						if(tup && rtup && tup.length==dat.params.length && tup.length==rtup.length){ // TODO: assert this?
							auto combined=iota(tup.length).map!(i=>combine(dat.params[i].variance,tup[i],rtup[i])).array;
							if(combined.any!(x=>x is null)) return null;
							auto rarg=new TupleExp(combined);
							return callSemantic(new CallExp(e,rarg,isSquare,isClassical_),expSemContext(null,ConstResult.no,InType.yes));
						}
					}
				}
			}
		}
		return super.combineTypesImpl(rhs,meet);
	}
	override Expression getClassical(){
		static if(language==silq){
			assert(isType(this));
			if(auto r=super.getClassical()) return r;
			auto r=new CallExp(e,arg,isSquare,true);
			r.type=getClassicalTy(type);
			r.sstate=sstate;
			return r;
		}else return this;
	}
	override Expression getQuantum(){
		static if(language==silq){
			assert(isType(this));
			if(isInt(this)||isUint(this)){ // TODO: generalize
				auto r=new CallExp(e,arg,isSquare,false);
				r.type=qtypeTy;
				r.sstate=sstate;
				return r;
			}
			return null;
		}else return null;
	}

	override Annotation getAnnotation(){
		auto fty=cast(FunTy)e.type;
		if(!fty) return Annotation.none;
		return min(fty.annotation,arg.getAnnotation());
	}

	override Expression evalImpl(Expression ntype){
		auto ne=e.eval(), narg=arg.eval();
		// TODO: partially evaluate arbitrary functions
		if(ntype.isClassical()){
			if(auto ce2=cast(CallExp)ne){
				if(auto id=cast(Identifier)ce2.e){
					if(id.name=="dup"){
						import ast.semantic_:isPreludeSymbol,PreludeSymbol;
						if(isPreludeSymbol(id.meaning)==PreludeSymbol.dup)
							return narg; // TODO: ok?
					}
				}
			}
		}
		if(ne == e && narg == arg && ntype == type) return this;
		return new CallExp(ne,narg,isSquare,isClassical_);
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

class BinaryExp(TokenType op): ABinaryExp{
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
	//override string toString(){return e1.toString() ~ " "~ e2.toString~TokChars!op;} // RPN
	static if(op==Tok!":="){
		override @property string kind(){ return "variable declaration"; }
	}
	override BinaryExp!op substituteImpl(Expression[string] subst){
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
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto be=cast(typeof(this))rhs;
		if(!be) return false;
		return e1.unify(be.e1,subst,meet)&&e2.unify(be.e2,subst,meet);
	}

	override Expression evalImpl(Expression ntype){
		static if(op!=Tok!"→"){
			auto ne1=e1.eval(), ne2=e2.eval();
			auto make(Expression exp){
				exp.type=ntype;
				exp.loc=ne1.loc.to(ne2.loc);
				exp.sstate=SemState.completed;
				return exp.evalImpl(ntype);
			}
			Expression create(Expression exp,Expression type){
				exp.type=type;
				exp.sstate=SemState.completed;
				exp.loc=ne1.loc.to(ne2.loc);
				return exp;
			}
			static if(op==Tok!"+"){
				{auto le1=cast(LiteralExp)ne1,le2=cast(LiteralExp)ne2;
				if(le1&&le2&&le1.lit.type==Tok!"0"&&le2.lit.type==Tok!"0")
					return make(LiteralExp.makeInteger(ℤ(le1.lit.str)+ℤ(le2.lit.str))); // TODO: replace literal exp internal representation
				if(le1&&le1.lit.type==Tok!"0"&&le1.lit.str=="0") return ne2.evalImpl(ntype);
				if(le2&&le2.lit.type==Tok!"0"&&le2.lit.str=="0") return ne1.evalImpl(ntype);
				if(le1&&!le2) return make(new BinaryExp!op(ne2,ne1));
				if(le2&&le2.lit.str.startsWith("-"))
					return make(new BinaryExp!(Tok!"-")(ne1,create(LiteralExp.makeInteger(-ℤ(le2.lit.str)),ℕt(true))));
				}
				static foreach(sub1;[Tok!"-",Tok!"sub"]){
					if(auto se1=cast(BinaryExp!sub1)ne1){
						static foreach(sub2;[Tok!"-",Tok!"sub"]){
							if(auto se2=cast(BinaryExp!sub2)ne2){
								auto nb0=make(new BinaryExp!op(se1.e1,se2.e2));
								auto nb1=make(new BinaryExp!sub1(nb0,se1.e2));
								auto nb2=make(new BinaryExp!sub2(nb1,se2.e2));
								return nb2.evalImpl(ntype);
							}
						}
						auto le1=cast(LiteralExp)se1.e2,le2=cast(LiteralExp)ne2;
						if(le1&&le2&&le1.lit.type==Tok!"0"&&le2.lit.type==Tok!"0"){
							auto nle=LiteralExp.makeInteger(ℤ(le1.lit.str)-ℤ(le2.lit.str)); // TODO: replace literal exp internal representation
							nle.loc=le1.loc.to(le2.loc);
							nle.type=ntype;
							nle.sstate=SemState.completed;
							return make(new BinaryExp!sub1(se1.e1,nle));
						}
						if(se1.e2==ne2) return se1.e1.evalImpl(ntype);
					}
				}
				static foreach(sub2;[Tok!"-",Tok!"sub"]){
					if(auto se2=cast(BinaryExp!sub2)ne2){
						if(se2.e2==ne1) return se2.e1.evalImpl(ntype);
					}
				}
				if(auto ae2=cast(BinaryExp!(Tok!"+"))ne2){
					auto nb0=new BinaryExp!op(ne1,ae2.e1);
					nb0.type=ntype;
					nb0.loc=nb0.e1.loc.to(nb0.e2.loc);
					nb0.sstate=SemState.completed;
					auto nb1=new BinaryExp!op(nb0,ae2.e2);
					nb1.type=ntype;
					nb1.loc=nb1.e1.loc.to(nb1.e2.loc);
					return nb1.evalImpl(ntype);
				}
				if(ne1==ne2){
					auto two=LiteralExp.makeInteger(2);
					two.loc=ne1.loc;
					return make(new BinaryExp!(Tok!"·")(two,ne2));
				}
			}else static if(op==Tok!"-"||op==Tok!"sub"){
				if(ne1==ne2){
					Token tok;
					tok.type=Tok!"0";
					tok.str="0";
					return make(new LiteralExp(tok));
				}
				{auto le1=cast(LiteralExp)ne1,le2=cast(LiteralExp)ne2;
				if(le1&&le2&&le1.lit.type==Tok!"0"&&le2.lit.type==Tok!"0"){
					auto v=ℤ(le1.lit.str)-ℤ(le2.lit.str);
					static if(op==Tok!"sub"){
						if(v>=0) return make(LiteralExp.makeInteger(v)); // TODO: replace literal exp internal representation
					}else{
						return make(LiteralExp.makeInteger(v)); // TODO: replace literal exp internal representation
					}
				}
				if(le2&&le2.lit.type==Tok!"0"&&le2.lit.str=="0") return ne1.evalImpl(ntype);
				}
				if(auto ae1=cast(BinaryExp!(Tok!"+"))ne1){
					if(ae1.e1==ne2) return ae1.e2.evalImpl(ntype);
					if(ae1.e2==ne2) return ae1.e1.evalImpl(ntype);
				}
				static foreach(sub;[Tok!"-",Tok!"sub"]){
					if(auto se1=cast(BinaryExp!sub)ne1){
						if(se1.e1==ne2) return make(new UnaryExp!(Tok!"-")(se1.e2));
						// TODO: if(se1.e2==-ne2)
					}
					if(auto se2=cast(BinaryExp!sub)ne2){
						if(se2.e1==ne1) return se2.e2.evalImpl(ntype);
						// TODO: if(se2.e2==-ne1
					}
				}
				if(auto ae2=cast(BinaryExp!(Tok!"+"))ne2){
					if(ae2.e1==ne1) return make(new UnaryExp!(Tok!"-")(ae2.e2));
					if(ae2.e2==ne1) return make(new UnaryExp!(Tok!"-")(ae2.e1));
				}
				static foreach(sub2;[Tok!"-",Tok!"sub"]){
					if(auto se2=cast(BinaryExp!sub2)ne2){
						auto nb0=new BinaryExp!op(ne1,se2.e1);
						nb0.type=ntype;
						nb0.loc=nb0.e1.loc.to(nb0.e2.loc);
						nb0.sstate=SemState.completed;
						auto nb1=new BinaryExp!(Tok!"+")(nb0,se2.e2);
						nb1.type=ntype;
						nb1.loc=nb1.e1.loc.to(nb1.e2.loc);
						return nb1.evalImpl(ntype);
					}
				}
			}else static if(op==Tok!"·"){
				{auto le1=cast(LiteralExp)ne1,le2=cast(LiteralExp)ne2;
				if(le1&&le2&&le1.lit.type==Tok!"0"&&le2.lit.type==Tok!"0")
					return make(LiteralExp.makeInteger(ℤ(le1.lit.str)*ℤ(le2.lit.str))); // TODO: replace literal exp internal representation
				if(le1&&le1.lit.type==Tok!"0"&&le1.lit.str=="0") return le1.evalImpl(ntype);
				if(le2&&le2.lit.type==Tok!"0"&&le2.lit.str=="0") return le2.evalImpl(ntype);
				if(le1&&le1.lit.type==Tok!"0"&&le1.lit.str=="1") return ne2.evalImpl(ntype);
				if(le2&&le2.lit.type==Tok!"0"&&le2.lit.str=="1") return ne1.evalImpl(ntype);
				if(le2&&!le1) return make(new BinaryExp!op(ne2,ne1));
				}
			}else static if(op==Tok!"^"){
				{auto le1=cast(LiteralExp)ne1,le2=cast(LiteralExp)ne2;
					if(le2&&le2.lit.type==Tok!"0"&&le2.lit.str=="0") return make(LiteralExp.makeInteger(1));
					if(le2&&le2.lit.type==Tok!"0"&&le2.lit.str=="1") return ne1.evalImpl(ntype);
					if(le1&&le2&&le1.lit.type==Tok!"0"&&le2.lit.type==Tok!"0" && !le2.isNegative()){
						return make(LiteralExp.makeInteger(pow(ℤ(le1.lit.str),ℤ(le2.lit.str)))); // TODO: replace literal exp internal representation
					}
				}
			}
			static if(op==Tok!"+"||op==Tok!"-"||op==Tok!"sub"){
				if(auto me1=cast(BinaryExp!(Tok!"·"))ne1){
					if(auto le1=cast(LiteralExp)me1.e1){
						if(me1.e2==ne2){
							auto one=LiteralExp.makeInteger(1);
							one.loc=le1.loc;
							auto a=new BinaryExp!op(le1,one);
							a.loc=le1.loc;
							a.type=le1.type;
							a.sstate=SemState.completed;
							return make(new BinaryExp!(Tok!"·")(a,me1.e2));
						}
						if(auto me2=cast(BinaryExp!(Tok!"·"))ne2){
							if(auto le2=cast(LiteralExp)me2.e1){
								if(me1.e2==me2.e2){
									auto a=new BinaryExp!op(le1,le2);
									a.loc=ne1.loc.to(ne2.loc);
									if(le1.type==le2.type) a.type=le1.type;
									else a.type=ntype;
									a.sstate=SemState.completed;
									return make(new BinaryExp!(Tok!"·")(a,me1.e2));
								}
							}
						}
					}
				}
				if(auto me2=cast(BinaryExp!(Tok!"·"))ne2){
					if(auto le2=cast(LiteralExp)me2.e1){
						if(me2.e2==ne1){
							auto one=LiteralExp.makeInteger(1);
							one.loc=le2.loc;
							auto a=new BinaryExp!op(one,le2);
							a.loc=le2.loc;
							a.type=le2.type;
							a.sstate=SemState.completed;
							return make(new BinaryExp!(Tok!"·")(a,ne1));
						}
					}
				}
			}
			static if(op==Tok!"="||op==Tok!"≠"){
				if(ne1==ne2) return make(LiteralExp.makeBoolean(op==Tok!"="));
				if(cast(LiteralExp)ne1&&cast(LiteralExp)ne2) return make(LiteralExp.makeBoolean(op!=Tok!"="));
				if(util.among(ne1.type,ℕt(true),ℤt(true))&&util.among(ne2.type,ℕt(true),ℤt(true))){
					if(!cast(LiteralExp)ne2){
						import ast.semantic_: subtractionType;
						auto sub=create(new BinaryExp!(Tok!"-")(ne1,ne2), subtractionType(ne1.type,ne2.type));
						auto zero=create(LiteralExp.makeInteger(0),ℕt(true));
						return make(new BinaryExp!op(sub,zero));
					}
				}
			}
			if(ne1 == e1 && ne2 == e1 && ntype == type) return this;
			auto r=new BinaryExp!op(ne1,ne2);
			r.type=ntype;
			r.loc=ne1.loc.to(ne2.loc);
			r.sstate=SemState.completed;
			return r;
		}else return this;
	}

	override bool opEquals(Object o){
		auto be=cast(BinaryExp!op)o;
		return be && e1==be.e1&&e2==be.e2;
	}
	// semantic information
	static if(op==Tok!":="){
		bool isSwap=false;
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
	override FieldExp substituteImpl(Expression[string] subst){
		auto ne=e.substitute(subst);
		if(ne==e) return this;
		auto r=new FieldExp(ne,f);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto fe=cast(FieldExp)rhs;
		if(!fe||f!=fe.f) return false;
		return e.unify(rhs,subst,meet);
	}

	override Annotation getAnnotation(){
		return e.getAnnotation();
	}

	override Expression evalImpl(Expression ntype){
		auto ne=e.eval();
		if(ne == e && ntype == type) return this;
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
	override IteExp substituteImpl(Expression[string] subst){
		auto ncond=cond.substitute(subst);
		auto nthen=cast(CompoundExp)then.substitute(subst);
		auto nothw=othw?cast(CompoundExp)othw.substitute(subst):null;
		assert(!!nthen && !!nothw==!!othw);
		if(ncond==cond&&nthen==then&&nothw==othw) return this;
		auto r=new IteExp(ncond,nthen,nothw);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto ite=cast(IteExp)rhs;
		if(!ite) return false;
		return cond.unify(ite.cond,subst,meet)&&then.unify(ite.then,subst,meet)
			&&!othw&&!ite.othw||othw&&ite.othw&&othw.unify(ite.othw,subst,meet);
	}
	override Annotation getAnnotation(){
		return min(cond.getAnnotation(), then.getAnnotation(), othw.getAnnotation());
	}
	override Expression evalImpl(Expression ntype){
		auto ncond=cond.eval(),nthen=cast(CompoundExp)then.eval(),nothw=cast(CompoundExp)othw.eval();
		assert(nthen&&nothw); // TODO: check statically
		if(ncond==cond&&nthen==then&&nothw==othw&&ntype==type) return this;
		return new IteExp(ncond,nthen,nothw);
	}
}

class WithExp: Expression{
	CompoundExp trans;
	CompoundExp bdy;
	this(CompoundExp trans, CompoundExp bdy){
		this.trans=trans;
		this.bdy=bdy;
	}
	override WithExp copyImpl(CopyArgs args){
		return new WithExp(trans.copy(),bdy.copy());
	}
	override string toString(){ return _brk("with "~trans.toString()~" do "~bdy.toString()); }
	override @property string kind(){ return "with"; }
	override bool isCompound(){ return true; }

	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree; // TODO
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(trans)) return r;
		return dg(bdy);
	}
	// semantic information
	CompoundExp itrans; // inverse transform
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

	override Expression evalImpl(Expression ntype){ return this; }
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

	override Expression evalImpl(Expression ntype){ return this; }
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

	override Expression evalImpl(Expression ntype){ return this; }
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
	override Expression substituteImpl(Expression[string] subst){
		auto ns=s.dup;
		foreach(ref x;ns) x=x.substitute(subst);
		if(ns==s) return this;
		auto r=new CompoundExp(ns);
		r.loc=loc;
		return r;

	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		return false;
	}
	override Annotation getAnnotation(){ return reduce!min(Annotation.max, s.map!(x=>x.getAnnotation())); }
	override CompoundExp evalImpl(Expression ntype){
		auto ns=s.map!(s=>s.eval()).array;
		if(ns == s && ntype==type) return this;
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
	final @property size_t length(){ return e.length; }

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		foreach(x;e) if(auto r=x.freeVarsImpl(dg)) return r;
		return 0;
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		foreach(x;e) if(auto r=dg(x)) return r;
		return 0;
	}
	override TupleExp substituteImpl(Expression[string] subst){
		auto ne=e.dup;
		foreach(ref x;ne) x=x.substitute(subst);
		if(ne==e) return this;
		auto r=new TupleExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto te=cast(TupleExp)rhs;
		if(!te||e.length!=te.e.length) return false;
		return all!(i=>e[i].unify(te.e[i],subst,meet))(iota(e.length));
	}
	override bool opEquals(Object o){
		auto tpl=cast(TupleExp)o;
		return tpl&&e==tpl.e;
	}
	override Annotation getAnnotation(){
		return reduce!min(deterministic, e.map!(x=>x.getAnnotation()));
	}
	override Expression evalImpl(Expression ntype){
		auto ne=e.map!(e=>e.eval()).array;
		if(ne == e && ntype==type) return this;
		return new TupleExp(ne);
	}
}

class LambdaExp: Expression{
	FunctionDef orig;
	FunctionDef fd;
	this(FunctionDef orig){
		this.orig=orig;
		this.fd=orig.copy();
	}
	override LambdaExp copyImpl(CopyArgs args){
		return new LambdaExp(orig);
	}
	override string toString(){
		string d=fd.isSquare?"[]":"()";
		return _brk(d[0]~join(map!(to!string)(fd.params),",")~d[1]~(fd.annotation?text(fd.annotation):"")~fd.body_.toStringFunctionDef());
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
	override Expression evalImpl(Expression ntype){ return this; } // TODO: partially evaluate lambdas?
	override Annotation getAnnotation(){ return deterministic; }
}

class ArrayExp: Expression{
	Expression[] e;
	this(Expression[] e){
		this.e=e;
	}
	override ArrayExp copyImpl(CopyArgs args){
		return new ArrayExp(e.map!(e=>e.copy(args)).array);
	}
	override string toString(){ return _brk("["~e.map!(to!string).join(",")~"]");}
	override bool isConstant(){ return e.all!(x=>x.isConstant()); }

	override bool opEquals(Object o){
		auto r=cast(ArrayExp)o;
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
	override ArrayExp substituteImpl(Expression[string] subst){
		auto ne=e.dup;
		foreach(ref x;ne) x=x.substitute(subst);
		if(ne==e) return this;
		auto r=new ArrayExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto ae=cast(ArrayExp)rhs;
		if(!ae||e.length!=ae.e.length) return false;
		return all!(i=>e[i].unify(ae.e[i],subst,meet))(iota(e.length));
	}
	override Annotation getAnnotation(){ return reduce!min(deterministic,e.map!(x=>x.getAnnotation())); }
	override Expression evalImpl(Expression ntype){
		auto ne=e.map!(e=>e.eval()).array;
		if(ne == e && ntype==type) return this;
		return new ArrayExp(ne);
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

	override Expression evalImpl(Expression ntype){
		auto ne=e.eval();
		if(ne==e&&ntype==type) return this;
		return new ReturnExp(e);
	}
	mixin VariableFree; // TODO!
	override int componentsImpl(scope int delegate(Expression) dg){ return dg(e); }

	// semantic information:
	Scope scope_;
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

	override Expression evalImpl(Expression ntype){
		auto ne=e.eval();
		if(ne==e&&ntype==type) return this;
		return new AssertExp(e);
	}
	mixin VariableFree; // TODO!
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(e);
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

	override Expression evalImpl(Expression ntype){
		auto ne=e.eval();
		if(ne==e&&ntype==type) return this;
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

	override Expression evalImpl(Expression ntype){
		auto nval=val.eval();
		if(nval==val&&ntype==type) return this;
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

	override Expression evalImpl(Expression ntype){
		auto nval=val.eval();
		if(nval==val&&ntype==type) return this;
		return new ForgetExp(var,nval);
	}
	mixin VariableFree; // TODO
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(var)) return r;
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
	assert(0,text("unknown declaration: ",typeid(s)," ",s));
}
auto dispatchDecl(alias f,alias default_=unknownDeclError,T...)(Expression d,auto ref T args){
	import core.lifetime:forward;
	// TODO: implement without cast cascade
	if(auto fd=cast(FunctionDef)d) return f(fd,forward!args);
	if(auto dd=cast(DatDecl)d) return f(dd,forward!args);

	if(auto de=cast(DefineExp)d) return f(de,forward!args);
	if(auto de=cast(DefExp)d) return f(de,forward!args);
	if(auto ce=cast(CommaExp)d) return f(ce,forward!args);

	if(auto imp=cast(ImportExp)d) return f(imp,forward!args);
	return default_(d,args);
}


private noreturn unknownStmError(T...)(Expression s,auto ref T args){
	assert(0,text("unknown statement: ",typeid(s)," ",s));
}
auto dispatchStm(alias f,alias default_=unknownStmError,bool unanalyzed=false,T...)(Expression s,auto ref T args){
	import core.lifetime:forward;
	// TODO: implement without cast cascade
	if(auto ce=cast(CallExp)s) return f(ce,forward!args);
	static if(unanalyzed) if(auto idx=cast(IndexExp)s) return f(idx,forward!args);
	if(auto ce=cast(CompoundExp)s) return f(ce,forward!args);
	if(auto ite=cast(IteExp)s) return f(ite,forward!args);
	if(auto with_=cast(WithExp)s) return f(with_,forward!args);
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
	assert(0,text("unknown expression: ",typeid(e)," ",e));
}
auto dispatchExp(alias f,alias default_=unknownExpError,bool unanalyzed=false,T...)(Expression e,auto ref T args){
	import core.lifetime:forward;
	// TODO: implement without cast cascade
	if(auto ite=cast(IteExp)e) return f(ite,forward!args);
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
	if(auto arr=cast(ArrayExp)e) return f(arr,forward!args);

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

	static if(unanalyzed){
		// expression types that only occur in unanalyzed expressions
		if(auto pr=cast(BinaryExp!(Tok!"×"))e) return f(pr,forward!args);
		if(auto ex=cast(BinaryExp!(Tok!"→"))e) return f(ex,forward!args);
		if(auto fa=cast(RawProductTy)e) return f(fa,forward!args);
	}

	return default_(e,forward!args);
}
