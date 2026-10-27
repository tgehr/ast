// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.declaration;
import astopt;

import std.array, std.algorithm, std.range, std.conv, std.exception;
import ast.lexer, ast.type, ast.expression, ast.scope_, util;

// what the dependency of a declaration is formed from: `reads` and the dependencies of `consumes` when they were consumed
struct DefinitionSources{
	import util.tuple:Q=Tuple,q=tuple;
	bool known=false;
	SetX!Declaration reads;
	Q!(Declaration,Dependency)[] consumes;
	static DefinitionSources empty(){ return DefinitionSources(true); }
	DefinitionSources dup(){ return DefinitionSources(known,reads.dup,consumes.map!(c=>q(c[0],c[1].dup)).array); }
	void consume(Declaration decl,Dependency dep){
		consumes~=q(decl,dep.dup);
	}
	void join(DefinitionSources rhs){
		if(!known) return;
		if(!rhs.known){
			this=DefinitionSources.init;
			return;
		}
		foreach(x;rhs.reads) reads.insert(x);
		foreach(c;rhs.consumes) consume(c[0],c[1]);
	}
}

abstract class Declaration: Expression{
	Identifier name;
	this(Identifier name){
		this.name=name;
		this.type=unit;
	}
	protected Identifier copyNameImpl(CopyArgs args){
		return name?name.copy(args):null;
	}
	void copyAnalyzedFieldsFrom(Declaration d){
		loc=d.loc;
		if(d.isSemError()) sstate=SemState.error;
		else if(d.isSemCompleted()) sstate=SemState.completed;
		canonicalSource_=d.canonicalSource;
		loopExitSplit=d.loopExitSplit;
		// scope, rename, split/merge links, type-const blockers are established per copy
	}
	override @property string kind(){ return "declaration"; }
	final @property Id getId(){ auto r=rename?rename:name; return r?r.id:Id(); }
	final @property string getName(){ auto r=rename?rename:name; return r?r.name:""; }
	override string toString(){ return getName; }

	bool isLinear(){ return true; }
	bool isConst(){ return false; }
	bool isPinned(){ return false; } // `const` parameters

	override Expression evalImpl(){ return this; }

	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){ return 0; }

	// semantic information
	Scope scope_;
	Identifier rename=null;
	Declaration splitFrom=null;
	Declaration[] splitInto=[];
	Declaration[] mergedFrom=[];
	Declaration mergedInto=null;
	Declaration promotedFrom=null; // if this declaration quantum-promotes another one, the original declaration
	EarlyForgottenDecl earlyForgotten=null; // if consumption was speculative early forget
	DefinitionSources definitionSources; // (what the dependency is formed from)
	ReturnExp forgottenBeforeEarlyReturn=null; // if forgotten before a conditional because of this early return in a branch

	bool loopExitSplit=false; // (at the exit of a `do`-`while` loop whose earlier iterations may change the value)
	final void cutDerivation(){
		loopExitSplit=true;
		canonicalSource_=this;
		foreach(d;splitInto) d.resetCanonicalSource();
	}
	Declaration canonicalSource_=null;
	Declaration canonicalSource(){ // TODO: compute eagerly instead?
		if(canonicalSource_) return canonicalSource_;
		if(splitFrom&&!loopExitSplit) return canonicalSource_=splitFrom.canonicalSource;
		if(mergedFrom.length&&mergedFrom.all!(d=>d.canonicalSource is mergedFrom[0].canonicalSource)) // (no path changes it)
			return canonicalSource_=mergedFrom[0].canonicalSource;
		return canonicalSource_=this;
	}
	final void resetCanonicalSource(){ // (e.g., after a split is relinked)
		if(!canonicalSource_) return;
		canonicalSource_=null;
		foreach(d;splitInto) d.resetCanonicalSource();
		if(mergedInto) mergedInto.resetCanonicalSource();
	}

	bool isToplevelDeclaration(){
		return scope_&&cast(TopScope)scope_;
	}
	bool isAggregateMember(){
		return scope_&&cast(AggregateScope)scope_;
	}

	@property splitSequence(){
		return recurrence!"a[n-1].splitFrom"(this).until!(d=>d is null);
	}
	bool isSplitFrom(Declaration outer){
		return splitSequence.any!(d=>d is outer);
	}

	@property Declaration[] derivedSequence(){
		Declaration[] result;
		SetX!Declaration visited;
		void visit(Declaration d){
			if(d in visited) return;
			visited.insert(d);
			result~=d;
			if(d.splitFrom) visit(d.splitFrom);
			foreach(m;d.mergedFrom) visit(m);
		}
		visit(this);
		return result;
	}
	bool isDerivedFrom(Declaration origin){
		MapX!(Declaration,bool) memo;
		bool rec(Declaration d){
			if(d is origin) return true;
			if(d in memo) return memo[d];
			bool r=d.splitFrom&&!d.loopExitSplit&&rec(d.splitFrom)||d.mergedFrom.length&&d.mergedFrom.all!(m=>rec(m));
			memo[d]=r;
			return r;
		}
		return rec(this);
	}
	// semantic information
	Expression typeConstBlocker=null;
	uint typeConstBlockDepth=0;
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
		auto r=new VarDecl(copyNameImpl(args));
		if(dtype) r.dtype=dtype.copy(args);
		r.isConst_=isConst_;
		r.isTemporary=isTemporary;
		return r;
	}
	bool isConst_=false;
	bool isTemporary=false; // introduced by the compiler for an intermediate value
	void setTemporary(bool isTemporary){
		this.isTemporary=isTemporary;
		if(isTemporary) name.meaning=this;
	}
	override bool isConst(){ return isConst_; }
	override string toString(){ return (isConst?"const ":"")~getName~(dtype?": "~dtype.toString():vtype?": "~vtype.toString():""); }
	@property override string kind(){ return "variable"; }
	alias copyAnalyzedFieldsFrom=Declaration.copyAnalyzedFieldsFrom;
	void copyAnalyzedFieldsFrom(VarDecl d){
		copyAnalyzedFieldsFrom(cast(Declaration)d);
		// dtype, vtype, initializer and definition are established per copy
	}

	override bool isLinear(){
		return vtype&&!vtype.isClassical();
	}
	// semantic information
	Expression vtype;
	Expression initializer;
	Expression knownValue; // (see `knownValueOf`)
	DefineExp definition;
	Expression typeSource; // (for diagnostics) the loop or assignment that determines the type of the variable, e.g., `x = n/2`
	VarDecl loweredFrom; // (for diagnostics) the variable after the loop in the analysis before the loop was lowered
	bool explicitType; // (for diagnostics) whether the type of the variable is annotated in its definition, e.g., `q:=1/2:!ℚ`
	Identifier outOfScopeCause;
	bool replaceType;
	Identifier outOfScopeDup;
}

Expression knownValueOf(Declaration d){ // (the value that the definition of a classical variable determines, e.g., `3` for `n:=3` or for `m:=n` after it, see `knownValuesEqual`)
	MapX!(Declaration,Expression) memo; // (merges that share their predecessors)
	Expression rec(Declaration d){
		auto vd=cast(VarDecl)d;
		if(!vd) return null;
		if(vd.knownValue||vd.initializer) return vd.knownValue;
		if(d in memo) return memo[d];
		memo[d]=null;
		Expression r=null;
		auto source=vd.canonicalSource;
		if(source !is vd){ // (no path changes it, e.g., in a branch, or after a loop that does not change it)
			if(!acrossLoop(vd.scope_,source.scope_)) r=rec(source);
		}else if(!vd.splitFrom&&vd.mergedFrom.length&&!vd.mergedFrom.any!(m=>acrossLoop(m.scope_,vd.scope_))){ // (not, e.g., after a loop that changes it)
			r=rec(vd.mergedFrom[0]);
			if(r) foreach(m;vd.mergedFrom[1..$]){
				auto v=rec(m);
				if(!v||!isEqual(r,v,null)){ r=null; break; }
			}
		}
		memo[d]=r;
		return r;
	}
	return rec(d);
}

bool loopContext(Scope use,Scope decl,out Scope[] loops){ // (the bodies of the loops that contain `use` but not `decl`, or `false` if the scopes are not related)
	if(!use||!decl) return false;
	Scope[] ancestors;
	for(auto sc=decl;sc;sc=sc.parentScope()) ancestors~=sc;
	static bool isLoopBody(Scope sc){ auto bs=cast(BlockScope)sc; return bs&&bs.isLoopBody; }
	for(auto sc=use;sc;sc=sc.parentScope()){
		auto i=ancestors.countUntil!(x=>x is sc);
		if(i>=0){
			loops~=ancestors[0..i].filter!isLoopBody.array;
			return true;
		}
		if(isLoopBody(sc)) loops~=sc;
	}
	return false;
}
bool acrossLoop(Scope a,Scope b){
	Scope[] loops;
	return !loopContext(a,b,loops)||loops.length!=0;
}

class Parameter: VarDecl{
	this(bool isConst, Identifier name, Expression type){
		super(name); this.dtype=type;
		this.isConst_=isConst;
	}
	override Parameter copyImpl(CopyArgs args){
		enforce(!args.preserveSemantic||util.among(sstate,SemState.initial,SemState.error),"TODO");
		auto r=new Parameter(isConst,copyNameImpl(args),dtype?dtype.copy(args):dtype);
		return r;
	}
	override bool isLinear(){
		return !isConst&&(!vtype||!vtype.isClassical());
	}
	override bool isPinned(){
		return isConst_;
	}
	override string toString(){
		static if(language==silq){
			return (isConst?"const ":"moved ")~getName~(vtype?": "~vtype.toString():dtype?": "~dtype.toString():"");
		}else return getName~(vtype?": "~vtype.toString():dtype?": "~dtype.toString():"");
	}
	@property override string kind(){ return "parameter"; }
}

abstract class FixedPointDeclaration: Declaration{
	this(Identifier name){ super(name); }
	bool typeFinal=false;
	FixedPointDeclaration[] dependents=[];
	size_t numUpdatesPending=0;
	int numInferenceRepetitions=0;
	bool unsealed=false;
	bool tainted=false;
}

class ToplevelDefinition: FixedPointDeclaration{
	DefineExp definition;
	DefineExp original;
	Expression result;
	VarDecl[] vars;
	int numActiveUpdates=0; // (analyses, together with the following reanalysis of dependents)
	this(DefineExp definition){
		super(null);
		this.definition=definition;
	}
	override ToplevelDefinition copyImpl(CopyArgs args){ assert(0); }
	override string toString(){ return text("toplevel definition `",definition,"`"); }
}

class FunctionDef: FixedPointDeclaration{
	alias ftypeFinal=typeFinal;
	Parameter[] params;
	bool isTuple;
	bool isSquare=false;
	auto annotation=Annotation.none;
	bool inferAnnotation=false;
	Location annotationLoc; // (explicit annotation)
	Expression[Annotation.max+1] weakenedBy; // weakenedBy[a]: why inferred annotation is below `a`
	void weakenAnnotation(Annotation annotation,Expression cause){
		foreach(a;annotation+1..this.annotation+1) if(!weakenedBy[a]) weakenedBy[a]=cause;
		this.annotation=min(this.annotation,annotation);
	}
	Expression rret;
	CompoundExp body_;
	this(Identifier name, Parameter[] params, bool isTuple, Expression rret, CompoundExp body_)in{
		assert(isTuple||params.length==1);
	}do{
		super(name); this.params=params; this.isTuple=isTuple; this.rret=rret; this.body_=body_;
	}
	void copyIntrinsicFieldsFrom(FunctionDef fd){
		// non-semantic fields shared by all copies (see also copyImpl)
		isSquare=fd.isSquare;
		annotation=fd.annotation;
		inferAnnotation=fd.inferAnnotation;
		annotationLoc=fd.annotationLoc;
		weakenedBy=fd.weakenedBy;
		attributes=fd.attributes.dup;
	}
	alias copyAnalyzedFieldsFrom=Declaration.copyAnalyzedFieldsFrom;
	void copyAnalyzedFieldsFrom(FunctionDef fd){
		copyAnalyzedFieldsFrom(cast(Declaration)fd);
		copyIntrinsicFieldsFrom(fd);
		ret=fd.ret;
		hasReturn=fd.hasReturn;
		static if(language==psi) retNames=fd.retNames;
		context=fd.context;
		thisVar=fd.thisVar;
		isConstructor=fd.isConstructor;
		sealed=fd.sealed;
		captureAnnotationReady=fd.captureAnnotationReady;
		ftypeFinal=fd.ftypeFinal;
	}
	override FunctionDef copyImpl(CopyArgs args){
		enforce(!args.preserveSemantic||util.among(sstate,SemState.initial,SemState.error),"TODO");
		bool keepsMeanings=args.preserveMeanings||args.preserveSemantic&&sstate==SemState.initial; // (e.g., a loop iteration of a copy with preserved meanings)
		Identifier[] selfReferences; // (recursive references refer to the copy)
		FunctionDef[] nestedDefs;
		if(keepsMeanings){
			if(args.preserveMeanings) args.boundFunctions~=canonicalSource; // (the copy declares its own parameters and locals)
			auto prevPostCopy=args.postCopy;
			args.postCopy=(Expression src,Expression cpy){
				if(prevPostCopy) prevPostCopy(src,cpy);
				if(auto id=cast(Identifier)cpy)
					if(id.meaning&&(id.meaning is this||id.meaning.isSplitFrom(this)))
						selfReferences~=id;
				if(auto nfd=cast(FunctionDef)cpy) nestedDefs~=nfd;
			};
		}
		auto r=new FunctionDef(copyNameImpl(args),params.map!(p=>p.copy(args)).array,isTuple,rret?rret.copy(args):null,body_?body_.copy(args):null);
		r.copyIntrinsicFieldsFrom(this);
		foreach(id;selfReferences) id.meaning=r;
		if(selfReferences.length){
			import ast.substitute: computeCapturesFromBody;
			foreach(nfd;nestedDefs) computeCapturesFromBody(nfd);
		}
		if(args.preserveMeanings){
			bool mentionsBound(Expression e){
				import ast.type: freeIdentifiers;
				foreach(id;e.freeIdentifiers)
					if(args.isBound(id.meaning))
						return true;
				return false;
			}
			if(!ret||!mentionsBound(ret)) r.ret=ret; // (otherwise recomputed)
			r.hasReturn=hasReturn;
			static if(language==psi) r.retNames=retNames;
		}
		if(keepsMeanings){ // (identifiers with preserved meanings are not looked up again)
			import ast.substitute: computeCapturesFromBody;
			computeCapturesFromBody(r);
		}
		return r;
	}
	override string toString(){
		string d=isSquare?"[]":"()";
		return "def "~(name?getName:"")~d[0]~join(map!(to!string)(params),",")~(isTuple&&params.length==1?",":"")~d[1]~annotationToString(annotation)~(body_?body_.toStringFunctionDef():";");
	}

	override bool isCompound(){ return true; }
	override bool isLinear(){ return ftype ? !ftype.isClassical() : context && context.vtype != contextTy(true) || capturedDecls.any!(d=>d.isLinear()); } // TODO: ok?
	override Annotation getAnnotation(){ return pure_; }

	override int freeVarsImpl(scope int delegate(Identifier) dg){
		import ast.substitute:functionDefFreeVarsImpl;
		return functionDefFreeVarsImpl(this,dg);
	}
	override Expression substituteImpl(MapSX!(Id,Expression) subst,TypeTransition* tt){
		import ast.substitute:substituteFunctionDefExp;
		return substituteFunctionDefExp(this,subst,false,tt);
	}

	@property override string kind(){ return "function"; }

	// semantic information
	FunctionScope fscope_;
	bool declaringParameters=false; // (analyzing the types of the parameters)
	DatDecl dataTypeOf=null;
	VarDecl context;
	static if(language==psi) VarDecl contextVal;
	VarDecl thisVar; // for constructors
	MapX!(Declaration,Identifier[]) captures;
	Declaration[] capturedDecls;
	Declaration[] movedCaptures; // (captures consumed from the enclosing scope, in order)
	bool captureAnnotationReady=false;
	bool sealed=false;
	static if(language==silq){
		SetX!Id consumingCaptures; // consumed classical captures
		bool captureReanalysis=false;
		Scope typeBoundary=null; // (of a closure within a type: the scope in which the analysis of the type started)
		bool readsReplacedComponent=false; // (its source reads the component from the aggregate, see `LambdaExp.copyImpl`)
	}
	void addCapture(Declaration meaning,Identifier id)in{
		assert(!!meaning&&(!meaning.isLinear||context&&context.vtype==contextTy(false)));
	}do{
		if(meaning !in captures) capturedDecls~=meaning;
		captures[meaning]~=id;
	}
	final bool isConsumedCapture(Declaration capture)in{
		assert(capture in captures);
		assert(!!fscope_);
	}do{
		static if(language==silq) if(capture.name&&capture.name.id in consumingCaptures) return true;
		auto id=captures[capture][0];
		if(!id.meaning||!id.meaning.scope_) return false;
		return id.meaning.scope_.isNestedIn(fscope_);
	}
	@property string contextName()in{assert(!!context,text(this));}do{ return context.getName; }
	final CaptureAnnotation getCaptureAnnotation(){
		bool hasConsumed=false;
		bool hasConst=false;
		foreach(capture;capturedDecls){
			import ast.semantic_:typeForDecl;
			auto type=typeForDecl(capture);
			if(!type||type.isClassical()) continue;
			if(isConsumedCapture(capture)) hasConsumed=true;
			else hasConst=true;
		}
		if(!hasConsumed&&!hasConst) return CaptureAnnotation.none;
		if(!captureAnnotationReady){
			if(hasConsumed) return CaptureAnnotation.moved;
			return CaptureAnnotation.none;
		}
		if(!hasConsumed) return CaptureAnnotation.const_;
		if(!hasConst) return CaptureAnnotation.moved;
		return CaptureAnnotation.once;
	}
	Expression ret; // return type
	FunTy ftype;
	void delegate(Expression)[] ftypeCallbacks; // called as soon as ftype has been determined
	bool hasReturn;
	bool isConstructor;
	static if(language==psi) string[] retNames;
	MapSX!(Id,Expression) attributes;

	void seal(){
		sealed=true;
	}
	bool inferringReturnType;
	CompoundExp origBody_=null;

	// inference mode
	bool finalPassDone=false;
	SetX!Id loweredConstIds; // for nested loop lowering
	bool keepLoops=false;
	int erpStage=0; // early-return elimination: 1: analyzing with loops kept, 2: rewritten
	bool deferredSpecificityCheck=false;
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

	bool boolAttribute(Id attr, bool default_=false) {
		auto p = attributes.getPtr(attr);
		if(!p||!*p) return default_;
		auto val = *p;
		if(!val) return default_;
		auto num = val.asIntegerConstant();
		if(!num) return default_; // TODO
		return num.get() != 0;
	}

	string stringAttribute(Id attr, string default_=null) {
		auto p = attributes.getPtr(attr);
		if(!p) return default_;
		auto e = cast(LiteralExp)*p;
		if(!e) return default_;
		auto str = e.asStringConstant();
		if(!str) return default_; // TODO
		return str.get();
	}

	FunctionDef reversed=null;
	bool isMain=false;
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
		return new DatParameter(variance,copyNameImpl(args),dtype.copy(args));
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
		return new DatDecl(copyNameImpl(args),hasParams,params.map!(p=>p.copy(args)).array,isTuple,isQuantum,body_.copy(args));
	}
	override string toString(){
		return "dat "~getName~(hasParams?text("[",params.map!(to!string).joiner(","),"]"):"")~(body_?body_.toString():";");
	}

	override bool isCompound(){ return true; }
	override bool isLinear(){ return false; }

	final MapSX!(Id,Expression) getSubst(Expression arg){
		MapSX!(Id,Expression) subst;
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
	MapX!(Declaration,Identifier[]) captures;
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
			assert(dparam.isSemCompleted());
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
		ncall.setSemCompleted();
		auto ret=new ReturnExp(ncall);
		ret.type=unit;
		ret.setSemCompleted();
		auto bdy=new CompoundExp([ret]);
		bdy.type=unit;
		bdy.setSemCompleted();
		fd=new FunctionDef(null, fparams, isTuple, null, bdy);
		fd.loc=this.loc;
		fd.dataTypeOf=this;
		fd.isSquare=true;
		fd.annotation=pure_;
		fd.scope_=this.scope_;
		fd.ftype=cast(ProductTy)id.type;
		assert(fd.ftype);
		assert(!captures.length,"nested dat decl not supported");
		fd.fscope_=new FunctionScope(this.dscope_.parent,fd);
		foreach(fparam; fparams) {
			fparam.scope_ = fd.fscope_;
		}
		foreach(pid; ids) pid.scope_ = fd.fscope_;
		fd.context=this.context;
		fd.ret=fd.ftype.cod;
		assert(isType(fd.ret));
		fd.hasReturn=true;
		static if(language==psi) fd.retNames=["r"];
		fd.setSemCompleted();
		return fd;
	}
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
	bool sameExplanation(DeadDecl other){ return this is other; }
	this(Identifier name){
		super(name);
	}
	override DeadDecl copyImpl(CopyArgs cargs){
		return this; // TODO: ok?
	}
	bool reportUndefinedIdentifier(Identifier id,Scope sc){ return false; }
	bool reportRedefinition(Declaration decl,Scope sc){ return false; }
	abstract void explain(string kind,Scope sc);
}

class ConsumedDecl: DeadDecl{
	override bool sameExplanation(DeadDecl other){
		auto o=cast(ConsumedDecl)other;
		return o&&typeid(o) is typeid(this)&&o.use is use;
	}
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
		sc.note(format("%s `%s` consumed here",kind,use.meaning),use.loc);
	}
	static if(language==silq)
	override bool reportUndefinedIdentifier(Identifier id,Scope sc){
		import std.format:format;
		if(use.erroneousUse) return true;
		if(!use.meaning) return false;
		auto blocking=sc.blockingComponentReplacement(use.meaning);
		if(!blocking) return false; // (consumed by a conversion whose result has components that are being replaced)
		sc.error(format("cannot access aggregate `%s` while its components are being replaced",use.meaning.getName),id.loc);
		sc.note("replaced component is here",blocking.location.loc);
		return true;
	}
	static if(language==silq)
	override bool reportRedefinition(Declaration decl,Scope sc){
		return use.meaning&&sc.blockedRedefinitionError(decl,use.meaning);
	}
	override string toString(){
		return text("consumed(",super.toString(),",",use.loc,")");
	}
}

class OutOfScopeDecl: ConsumedDecl{
	Identifier cause;
	Identifier dupUse;
	override bool sameExplanation(DeadDecl other){
		auto o=cast(OutOfScopeDecl)other;
		return o&&o.use is use&&o.cause is cause&&o.dupUse is dupUse;
	}
	this(Declaration decl,Identifier use,Identifier cause,Identifier dupUse=null)in{
		assert(!!cause);
	}do{
		super(decl,use);
		this.cause=cause;
		this.dupUse=dupUse;
	}
	override void explain(string kind,Scope sc){
		import std.format:format;
		if(!dupUse||dupUse is use){
			super.explain(kind,sc);
		}else sc.note(format("%s `%s` went out of scope here",kind,use.meaning),use.loc);
		if(dupUse&&dupUse !is use)
			sc.note(format("`%s` was used in a consuming position here",dupUse.name),dupUse.loc);
		sc.note(format("`%s` not recomputable after dependency `%s` was consumed here",use.name,cause.name),cause.loc);
	}
	override string toString(){
		return text("outOfScope(",super.toString(),",",cause.loc,")");
	}
}

class EarlyForgottenDecl: DeadDecl{
	Declaration decl;
	Declaration consumed;
	Identifier use;
	string action="consume";
	EarlyForgottenDecl reportVia=null;
	this(Declaration decl,Declaration consumed,Identifier use)in{
		assert(!!decl&&!!consumed&&!!use);
	}do{
		super(decl.name);
		this.type=decl.type;
		this.decl=decl;
		this.consumed=consumed;
		this.use=use;
	}
	override bool reportUndefinedIdentifier(Identifier id,Scope sc){
		import std.format:format;
		import ast.semantic_:typeForDecl;
		if(reportVia) return reportVia.reportUndefinedIdentifier(id,sc);
		if(isSemError()) return true;
		setSemForceError();
		sc.error(format("cannot %s `const` %s `%s`",action,consumed.kind,use),use.loc);
		sc.note(format("`%s` cannot be consumed because the type `%s` of live %s `%s` depends on it",consumed.name,typeForDecl(decl),decl.kind,decl.getName),decl.loc);
		return true;
	}
	override void explain(string kind,Scope sc){
		import std.format:format;
		if(isSemError()) return; // report only once
		setSemForceError();
		sc.note(format("%s `%s` consumed here",kind,decl),use?use.loc:decl.loc);
	}
	override string toString(){
		return text("earlyForgotten(",super.toString(),",",use?text(use.loc):"<?>",")");
	}
}

class LoopForgottenDecl: DeadDecl{ // (a variable of the body of a `do`-`while` loop that the next iteration can only forget at its last use)
	Declaration decl;
	this(Declaration decl){
		super(decl.name);
		this.type=decl.type;
		this.decl=decl;
	}
	override void explain(string kind,Scope sc){
		import std.format:format;
		sc.note(format("%s `%s` is forgotten within the loop, as the next iteration cannot keep it",kind,decl.getName),decl.loc);
	}
	override string toString(){
		return text("loopForgotten(",super.toString(),")");
	}
}

class EarlyReturnForgottenDecl: ConsumedDecl{
	Declaration decl;
	ReturnExp ret;
	this(Declaration decl,Identifier use,ReturnExp ret)in{
		assert(!!ret);
	}do{
		super(decl,use);
		this.decl=decl;
		this.ret=ret;
	}
	override bool reportUndefinedIdentifier(Identifier id,Scope sc){
		import std.format:format;
		if(isSemError()) return true; // (report only once)
		setSemForceError();
		if(cast(Parameter)decl) sc.error(format("%s `%s` is not consumed (perhaps return it or annotate it `const`)",decl.kind,decl.getName),decl.loc);
		else sc.error(format("%s `%s` is not consumed (perhaps return it)",decl.kind,decl.getName),decl.loc);
		sc.note("at function return",ret.loc);
		sc.note(format("`%s` cannot be forgotten before the conditional, as it is used again here",decl.getName),id.loc);
		return true;
	}
	override void explain(string kind,Scope sc){
		import std.format:format;
		sc.note(format("%s `%s` forgotten here, before a conditional with an early return",kind,use.meaning),use.loc);
		sc.note("early return is here",ret.loc);
	}
	override string toString(){
		return text("earlyReturnForgotten(",super.toString(),",",ret.loc,")");
	}
}
class IllegalConsumedDecl: ConsumedDecl{
	EarlyForgottenDecl earlyForgotten;
	this(Declaration decl,Identifier use,EarlyForgottenDecl earlyForgotten)in{
		assert(!!earlyForgotten);
	}do{
		super(decl,use);
		this.earlyForgotten=earlyForgotten;
	}
	override bool reportUndefinedIdentifier(Identifier id,Scope sc){
		return earlyForgotten.reportUndefinedIdentifier(id,sc);
	}
}

class DeadMerge: DeadDecl{
	bool quantumControl;
	size_t numBranches=2;
	Declaration goneMention; // (a `const` local of a branch that the type mentions)
	this(Identifier name){
		super(name);
	}
	override bool reportUndefinedIdentifier(Identifier id,Scope sc){
		if(mergedFrom.length<numBranches&&mergedFrom.any!(d=>d.isSemError())) return true;
		bool handled=false;
		foreach(d;mergedFrom)
			if(auto dd=cast(DeadDecl)d)
				handled=dd.reportUndefinedIdentifier(id,sc)||handled;
		return handled;
	}
	override bool reportRedefinition(Declaration decl,Scope sc){
		SetX!DeadDecl visited;
		return reportRedefinitionImpl(decl,sc,visited);
	}
	private bool reportRedefinitionImpl(Declaration decl,Scope sc,ref SetX!DeadDecl visited){
		foreach(d;mergedFrom){
			auto dd=cast(DeadDecl)d;
			if(!dd||dd in visited) continue;
			visited.insert(dd);
			if(auto dm=cast(DeadMerge)dd){
				if(dm.reportRedefinitionImpl(decl,sc,visited)) return true;
			}else if(dd.reportRedefinition(decl,sc)) return true;
		}
		return false;
	}
	override void explain(string kind,Scope sc){
		import std.format:format;
		import ast.semantic_:typeForDecl;
		assert(mergedFrom.length!=0);
		auto deadDecls=mergedFrom.map!(d=>cast(DeadDecl)d).filter!(d=>!!d).array;
		if(deadDecls.length){
			DeadDecl[] explained;
			foreach(dd;deadDecls){
				if(explained.any!(e=>e.sameExplanation(dd))) continue;
				explained~=dd;
				dd.explain(kind,sc); // TODO: good?
			}
			return;
		}
		if(goneMention){
			sc.note(format("declared with type `%s` here",typeForDecl(mergedFrom[0])),mergedFrom[0].loc);
			sc.note(format("`const` variable `%s` is not visible after its block",goneMention.getName),goneMention.loc);
		}else if(mergedFrom.length==1){
			sc.note("declared on only one path",mergedFrom[0].loc);
		}else if(mergedFrom.length<numBranches){
			foreach(d;mergedFrom){
				auto type=typeForDecl(d);
				sc.note("declared on this path",d.loc);
			}
			auto d=mergedFrom[$-1];
			sc.note("however, not declared on all paths",d.loc);
		}else if(mergedFrom.length==numBranches){
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
					if(!isType(type.getQuantum)){
						sc.note(format("declaration under quantum `if` has type `%s` which cannot be promoted to quantum",type),d.loc);
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
						sc.note(format("declared with type `%s` here",type),d.loc);
					}
					auto d=mergedFrom[$-1];
					sc.note(format("declarations under quantum `if` have common type `%s` which cannot be promoted to quantum",common),d.loc);
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
					sc.note(format("declared with type `%s` here",type),d.loc);
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

bool isConstLocal(Declaration decl){
	auto vd=cast(VarDecl)decl;
	return vd&&!cast(Parameter)vd&&vd.isConst_;
}
