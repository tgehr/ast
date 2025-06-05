// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.declaration;
import astopt;

import std.array, std.algorithm, std.range, std.conv, std.exception;
import ast.lexer, ast.type, ast.expression, ast.scope_, util;

abstract class Declaration: Expression{
	Identifier name;
	Scope scope_;
	this(Identifier name){
		this.name=name;
		this.type=unit;
	}
	override @property string kind(){ return "declaration"; }
	final @property Id getId(){ auto r=rename?rename:name; return r?r.id:Id(); }
	final @property string getName(){ auto r=rename?rename:name; return r?r.name:""; }
	override string toString(){ return getName; }

	bool isLinear(){ return true; }
	bool isConst(){ return false; }

	override Expression evalImpl(){ return this; }

	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){ return 0; }

	// semantic information
	Identifier rename=null;
	Declaration splitFrom=null;
	Declaration[] splitInto=[];
	Declaration[] mergedFrom=[];
	Declaration mergedInto=null;

	@property splitSequence(){
		return recurrence!"a[n-1].splitFrom"(this).until!(d=>d is null);
	}
	bool isSplitFrom(Declaration outer){
		return splitSequence.any!(d=>d is outer);
	}

	@property Declaration[] derivedSequence(){
		auto result=[this];
		if(splitFrom) result~=splitFrom.derivedSequence;
		foreach(d;mergedFrom)
			result~=d.derivedSequence;
		return result;
	}
	bool isDerivedFrom(Declaration origin){
		if(this is origin) return true;
		if(splitFrom&&splitFrom.isDerivedFrom(origin))
			return true;
		if(mergedFrom.length&&mergedFrom.all!(d=>d.isDerivedFrom(origin)))
		   return true;
		return false;
	}
}

class CompoundDecl: Expression{
	Expression[] s;
	this(Expression[] ss){s=ss;}
	override CompoundDecl copyImpl(CopyArgs args){
		return new CompoundDecl(s.map!(s=>s.copy(args)).array);
	}

	override string toString(){return "{\n"~indent(join(map!(a=>a.toString()~(a.isCompound()?"":";"))(s),"\n"))~"\n}";}
	override bool isCompound(){ return true; }
	override int componentsImpl(scope int delegate(Expression) dg){ return 0; }

	// semantic information
	AggregateScope ascope_;

	override Expression evalImpl(){ return this; }

	mixin VariableFree; // TODO!
}



class VarDecl: Declaration{
	Expression dtype;
	this(Identifier name){ super(name); }
	override VarDecl copyImpl(CopyArgs args){
		//enforce(!args.preserveSemantic||util.among(sstate,SemState.initial,SemState.error),"TODO");
		//return new VarDecl(dtype.copy(args));
		auto r=new VarDecl(name?name.copy(args):null);
		if(dtype) r.dtype=dtype.copy(args);
		return r;
	}
	override string toString(){ return (isConst()?"const ":"")~getName~(dtype?": "~dtype.toString():vtype?": "~vtype.toString():""); }
	@property override string kind(){ return "variable"; }

	override bool isLinear(){
		return vtype&&!vtype.isClassical();
	}
	// semantic information
	Expression vtype;
	Expression initializer;
	Expression typeConstBlocker=null;
}

class Parameter: VarDecl{
	bool isConst_;
	this(bool isConst, Identifier name, Expression type){
		super(name); this.dtype=type;
		this.isConst_=isConst;
	}
	override Parameter copyImpl(CopyArgs args){
		enforce(!args.preserveSemantic||util.among(sstate,SemState.initial,SemState.error),"TODO");
		return new Parameter(isConst,name?name.copy(args):null,dtype?dtype.copy(args):dtype);
	}
	override bool isLinear(){
		return !isConst&&(!vtype||!vtype.isClassical());
	}
	override bool isConst(){
		return isConst_;
	}
	override string toString(){
		static if(language==silq){
			return (isConst?"const ":"moved ")~getName~(vtype?": "~vtype.toString():dtype?": "~dtype.toString():"");
		}else return getName~(vtype?": "~vtype.toString():dtype?": "~dtype.toString():"");
	}
	@property override string kind(){ return "parameter"; }
}

class FunctionDef: Declaration{
	Parameter[] params;
	bool isTuple;
	bool isSquare=false;
	auto annotation=Annotation.none;
	bool inferAnnotation=false;
	Expression rret;
	CompoundExp body_;
	this(Identifier name, Parameter[] params, bool isTuple, Expression rret, CompoundExp body_)in{
		assert(isTuple||params.length==1);
	}do{
		super(name); this.params=params; this.isTuple=isTuple; this.rret=rret; this.body_=body_;
	}
	override FunctionDef copyImpl(CopyArgs args){
		enforce(!args.preserveSemantic||util.among(sstate,SemState.initial,SemState.error),"TODO");
		auto r=new FunctionDef(name?name.copy(args):null,params.map!(p=>p.copy(args)).array,isTuple,rret?rret.copy(args):null,body_?body_.copy(args):null);
		r.isSquare=isSquare;
		r.annotation=annotation;
		r.inferAnnotation=inferAnnotation;
		r.attributes=attributes.array;
		return r;
	}
	override string toString(){
		string d=isSquare?"[]":"()";
		return "def "~(name?getName:"")~d[0]~join(map!(to!string)(params),",")~(isTuple&&params.length==1?",":"")~d[1]~(annotation?text(annotation):"")~(body_?body_.toStringFunctionDef():";");
	}

	override bool isCompound(){ return true; }
	override bool isLinear(){ return ftype ? !ftype.isClassical() : capturedDecls.any!(d=>d.isLinear()); } // TODO: ok?

	@property override string kind(){ return "function definition"; }

	// semantic information
	FunctionScope fscope_;
	VarDecl context;
	static if(language==psi) VarDecl contextVal;
	VarDecl thisVar; // for constructors
	Identifier[][Declaration] captures;
	Declaration[] capturedDecls;
	bool sealed=false;
	void addCapture(Declaration meaning,Identifier id)in{
		assert(!!meaning&&(!meaning.isLinear||context&&context.vtype==contextTy(false)));
	}do{
		if(meaning !in captures) capturedDecls~=meaning;
		captures[meaning]~=id;
	}
	@property string contextName()in{assert(!!context,text(this));}do{ return context.getName; }
	Expression ret; // return type
	FunTy ftype;
	void delegate(Expression)[] ftypeCallbacks; // called as soon as ftype has been determined
	bool hasReturn;
	bool isConstructor;
	string[] retNames;
	string[] attributes;

	void seal(){
		sealed=true;
	}
	bool inferringReturnType;
	bool ftypeFinal=false;
	FunctionDef[] functionDefsToUpdate=[];
	size_t numUpdatesPending=0;
	Expression origRret=null;
	CompoundExp origBody_=null;
	int numInferenceRepetitions=0;
	bool unsealed=false; // need to redo analysis of dependent declarations
	void unseal()in{
		assert(sealed);
	}do{
		sealed=false;
		unsealed=true;
	}

	@property Scope realScope(){
		if(!scope_) return null;
		if(isConstructor) return scope_.getDatDecl().scope_;
		return scope_;
	}
	@property bool isNested(){ return !!cast(NestedScope)realScope; }

	@property size_t numArgs(){
		if(!ftype) return 0;
		return ftype.dom.numComponents;
	}

	@property size_t numReturns(){
		if(!ftype) return 0;
		return ftype.cod.numComponents;
	}

	bool hasAttribute(string attr) {
		return attributes.any!(a => a == attr);
	}

	FunctionDef reversed=null;
}


enum Variance{
	invariant_,
	covariant,
	contravariant,
}

class DatParameter: Parameter{
	Variance variance;
	this(Variance variance, Identifier name, Expression type){
		this.variance=variance;
		super(true,name,type);
	}
	override DatParameter copyImpl(CopyArgs args){
		return new DatParameter(variance,name?name.copy(args):null,dtype.copy(args));
	}
	override string toString(){
		final switch(variance)with(Variance){
			case invariant_: return super.toString();
			case covariant: return "+"~super.toString();
			case contravariant: return "-"~super.toString();
		}
	}
}

class DatDecl: Declaration{
	AggregateTy dtype;
	bool hasParams;
	DatParameter[] params;
	bool isTuple;
	bool isQuantum;
	CompoundDecl body_;
	this(Identifier name,bool hasParams,DatParameter[] params,bool isTuple,bool isQuantum,CompoundDecl body_)in{
		if(hasParams) assert(isTuple||params.length==1);
		else assert(isTuple&&params.length==0);
	}do{
		super(name);
		this.hasParams=hasParams;
		this.params=params;
		this.isTuple=isTuple;
		this.isQuantum=isQuantum;
		this.body_=body_;
	}
	override DatDecl copyImpl(CopyArgs args){
		return new DatDecl(name?name.copy(args):null,hasParams,params.map!(p=>p.copy(args)).array,isTuple,isQuantum,body_.copy(args));
	}
	override string toString(){
		return "dat "~getName~(hasParams?text("[",params.map!(to!string).joiner(","),"]"):"")~(body_?body_.toString():";");
	}

	override bool isCompound(){ return true; }
	override bool isLinear(){ return false; }

	final Expression[Id] getSubst(Expression arg){
		Expression[Id] subst;
		if(isTuple){
			foreach(i,p;params)
				subst[p.getId]=new IndexExp(arg,new LiteralExp(Token(Tok!"0",to!string(i)))).eval();
		}else{
			assert(params.length==1);
			subst[params[0].getId]=arg;
		}
		return subst;
	}

	// semantic information
	int semanticDepth=0; // TODO: get rid of this
	FunctionDef constructor;
	DataScope dscope_;
	VarDecl context;
	Identifier[][Declaration] captures;
	Declaration[] capturedDecls;
	void addCapture(Declaration meaning,Identifier id){
		if(meaning !in captures) capturedDecls~=meaning;
		captures[meaning]~=id;
	}
	@property string contextName()in{assert(!!context);}do{ return context.getName; }
	@property bool isNested(){ return !!cast(NestedScope)scope_; }

	FunctionDef fd;
	FunctionDef toFunctionDef()in{ // TODO: parse DatDecl with params as function with a local DatDecl inside in the first place?
		assert(hasParams&&isSemCompleted());
	}do{
		if(fd) return fd;
		auto fparams=params.map!((dparam){
			auto name=new Identifier(dparam.getId);
			name.loc=dparam.name.loc;
			auto param=new Parameter(dparam.isConst, name, dparam.dtype);
			param.loc=dparam.loc;
			param.vtype=dparam.vtype;
			param.sstate=dparam.sstate;
			return param;
		}).array;
		auto id=new Identifier(getId);
		id.loc=this.loc;
		id.meaning=this;
		import ast.semantic_:typeForDecl;
		id.type=typeForDecl(this);
		id.setSemCompleted();
		auto ids=fparams.map!((fparam){
			auto id=new Identifier(fparam.getId);
			id.loc=fparam.loc;
			id.meaning=fparam;
			id.type=fparam.vtype;
			id.setSemCompleted();
			return id;
		}).array;
		Expression arg=ids[0];
		if(isTuple){
			arg=new TupleExp(ids.map!((Expression id)=>id).array);
			arg.loc=ids.length?ids[0].loc.to(ids[$-1].loc):this.loc;
			arg.type=tupleTy(ids.map!(id=>id.type).array);
			arg.setSemCompleted();
		}
		CallExp call=new CallExp(id,arg,true,false);
		call.loc=id.loc.to(arg.loc);
		import ast.semantic_: ConstResult, InType, expSemContext, callSemantic; // TODO: get rid of this?
		auto ncall=callSemantic(call,expSemContext(null,ConstResult.no,InType.no));
		auto ret=new ReturnExp(ncall);
		ret.type=unit;
		ret.setSemCompleted();
		auto bdy=new CompoundExp([ret]);
		bdy.type=unit;
		fd=new FunctionDef(null, fparams, isTuple, null, bdy);
		fd.isSquare=true;
		fd.annotation=pure_;
		fd.ftype=cast(ProductTy)id.type;
		assert(fd.ftype);
		assert(!captures.length,"nested dat decl not supported");
		fd.fscope_=new FunctionScope(this.dscope_.parent,fd);
		fd.context=this.context;
		fd.ret=fd.ftype.cod;
		assert(isType(fd.ret));
		fd.hasReturn=true;
		fd.retNames=["r"];
		fd.setSemCompleted();
		return fd;
	}
}

string getActualPath(string path){
	import util.path;
	import util.io:file;
	auto ext = path.extension;
	if(ext=="") path = path.setExtension(astopt.defaultExtension);
	if(file.exists(path)) return path;
	foreach_reverse(p;astopt.importPath){
		auto candidate=buildPath(p,path);
		if(file.exists(candidate))
			return candidate;
	}
	return path;
}

class ImportExp: Declaration{
	Expression[] e;
	this(Expression[] e){
		super(null);
		this.e=e;
	}
	override ImportExp copyImpl(CopyArgs args){
		return new ImportExp(e.map!(e=>e.copy(args)).array);
	}
	static string getPath(Expression e){
		static string doIt(Expression e){
			import util.path;
			if(auto i=cast(Identifier)e) return i.name;
			if(auto f=cast(BinaryExp!(Tok!"."))e) return buildPath(doIt(f.e1),doIt(f.e2));
			assert(0);
		}
		return doIt(e);
	}
	override @property string kind(){ return "import declaration"; }
	override string toString(){ return "import "~e.map!(to!string).join(","); }
	override bool isLinear(){ return false; }
}


// special declarations used during semantic analysis

abstract class DeadDecl: Declaration{
	this(Identifier name){
		super(name);
	}
	override DeadDecl copyImpl(CopyArgs cargs){
		return this; // TODO: ok?
	}
	abstract void explain(string kind,Scope sc);
}

class ConsumedDecl: DeadDecl{
	Identifier use;
	this(Declaration decl,Identifier use)in{
		assert(!!use);
	}do{
		super(decl.name);
		this.type=decl.type;
		this.use=use;
	}
	override void explain(string kind,Scope sc){
		import std.format:format;
		sc.note(format("%s '%s' consumed here",kind,use.meaning),use.loc);
	}
	override string toString(){
		return text("consumed(",super.toString(),",",use.loc,")");
	}
}

class DeadMerge: DeadDecl{
	bool quantumControl;
	size_t numBranches=2;
	this(Identifier name){
		super(name);
	}
	override void explain(string kind,Scope sc){
		import std.format:format;
		import ast.semantic_:typeForDecl;
		assert(mergedFrom.length!=0);
		auto deadDecls=mergedFrom.map!(d=>cast(DeadDecl)d).filter!(d=>!!d).array;
		if(deadDecls.length){
			foreach(dd;deadDecls)
				dd.explain(kind,sc); // TODO: good?
			return;
		}
		if(mergedFrom.length==1){
			sc.note("declared on only one path",mergedFrom[0].loc);
		}else if(mergedFrom.length<numBranches){
			foreach(d;mergedFrom){
				auto type=typeForDecl(d);
				sc.note("declared on this path",d.loc);
			}
			auto d=mergedFrom[$-1];
			sc.note("however, not declared on all paths",d.loc);
		}if(mergedFrom.length==numBranches){
			Expression common=bottom;
			foreach(d;mergedFrom){
				auto type=typeForDecl(d);
				if(type) common=common?joinTypes(common,type):null;
			}
			if(quantumControl){
				bool ok=false;
				foreach(d;mergedFrom){
					auto type=typeForDecl(d);
					if(!type) continue;
					if(!type.getQuantum){
						sc.note(format("declaration under quantum 'if' has type '%s' which cannot be promoted to quantum",type),d.loc);
						if(type.isSubtype(ℤt(true))){
							sc.note("did you mean to use `int[n]` or `uint[n]`, with explicit bit width `n`?",d.loc);
						}else if(cast(ArrayTy)type){
							sc.note("quantum-dependent tuple length not yet supported",d.loc);
						}else if(cast(FunTy)type){
							sc.note("quantum-dependent closures not yet supported",d.loc);
						}
						ok=true;
						break; // TODO: good?
					}
				}
				if(ok) return;
				if(common&&!common.getQuantum){
					foreach(d;mergedFrom){
						auto type=typeForDecl(d);
						sc.note(format("declared with type '%s' here",type),d.loc);
					}
					auto d=mergedFrom[$-1];
					sc.note(format("declarations under quantum 'if' have common type '%s' which cannot be promoted to quantum",common),d.loc);
					if(cast(ArrayTy)common){
						sc.note("quantum-dependent tuple length not yet supported",d.loc);
					}else if(cast(FunTy)type){
						sc.note("quantum-dependent closures not yet supported",d.loc);
					}
					return;
				}
			}
			if(!common){
				foreach(d;mergedFrom){
					auto type=typeForDecl(d);
					sc.note(format("declared with type '%s' here",type),d.loc);
				}
				auto d=mergedFrom[$-1];
				sc.note("declarations on different paths have incompatible types",d.loc);
			}
		}
	}
	override string toString(){
		return text("deadMerge(",super.toString(),")");
	}
}
