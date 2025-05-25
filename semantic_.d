// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.semantic_;
import astopt;

import std.array,std.algorithm,std.range,std.exception;
import std.format, std.conv, util.tuple:Q=Tuple,q=tuple;
import ast.lexer,ast.scope_,ast.expression,ast.type,ast.conversion;
import ast.declaration,ast.error,ast.reverse,util;
import ast.lowerings;
import ast.modules: importModule, getPreludeScope, isInPrelude;

Id freshName(){ // TODO: improve mechanism for generating temporaries
	static int counter=0;
	return Id.intern(text("__tmp",counter++));
}

Expression moveExp(Expression e){
	// TODO: implement
	return e;
}

Expression getFixedIntTy(Expression bits,bool isSigned,bool isClassical,Location loc,Scope isc){ // TODO: do not require a scope
	auto sym=getPreludeSymbol(isSigned?"int":"uint",loc,isc);
	auto ce=new CallExp(sym,bits,true,isClassical);
	ce.loc=loc;
	ce.type=isClassical?ctypeTy:qtypeTy;
	ce.sstate=sym.sstate;
	return ce;
}

Identifier getDup(Location loc,Scope isc){
	return getPreludeSymbol("dup",loc,isc);
}

Expression dupExp(Expression e,Location loc,Scope isc){
	static if(language==silq){
		auto r=new CallExp(getDup(loc,isc),e,false,false);
		r.loc=loc;
		return r;
	}else return e;
}

void propErr(Expression e1,Expression e2){
	if(e1.sstate==SemState.error) e2.sstate=SemState.error;
}

DataScope isInDataScope(Scope sc){
	auto asc=cast(AggregateScope)sc;
	if(asc) return cast(DataScope)asc.parent;
	return null;
}

AggregateTy isDataTyId(Expression e){
	if(auto ce=cast(CallExp)e)
		return isDataTyId(ce.e);
	if(auto id=cast(Identifier)e)
		if(auto decl=cast(DatDecl)id.meaning)
			return decl.dtype;
	if(auto fe=cast(FieldExp)e)
		if(auto decl=cast(DatDecl)fe.f.meaning)
			return decl.dtype;
	return null;
}

void declareParameters(P)(Expression parent,bool isSquare,P[] params,Scope sc)if(is(P==Parameter)||is(P==DatParameter)){
	foreach(ref p;params){
		if(!p.dtype){ // !ℝ is the default parameter type for () and * is the default parameter type for []
			if(isSquare){
				auto id=New!Identifier("*");
				id.loc=p.loc;
				p.dtype=id;
			}else{
				auto id=New!Identifier(isSquare?"*":"ℝ");
				id.loc=p.loc;
				static if(language==silq){
					p.dtype=New!(UnaryExp!(Tok!"!"))(id);
					p.dtype.loc=p.loc;
				}else p.dtype=id;
			}
		}
		p=cast(P)varDeclSemantic(p,sc);
		assert(!!p);
		propErr(p,parent);
		sc.addDefaultDependency(p);
	}
}

VarDecl addVar(string name,Expression ty,Location loc,Scope sc){
	auto id=new Identifier(name);
	id.loc=loc;
	auto var=new VarDecl(id);
	var.loc=loc;
	var.vtype=ty;
	if(var.vtype){
		if(!sc) var.sstate=SemState.completed;
		else var=varDeclSemantic(var,sc);
		assert(!!var && var.sstate==SemState.completed);
	}else var.sstate=SemState.error;
	return var;
}

void prepareFunctionDef(FunctionDef fd,Scope sc){
	auto fsc=fd.fscope_;
	if(!fsc) return;
	if(fd.body_&&!fd.body_.blscope_) fd.body_.blscope_=new BlockScope(fsc);
	if(auto dsc=isInDataScope(sc)){
		auto id=new Identifier(dsc.decl.name.name);
		id.loc=dsc.decl.loc;
		id.meaning=dsc.decl;
		id=cast(Identifier)expressionSemantic(id,expSemContext(sc,ConstResult.no,InType.yes));
		assert(!!id);
		Expression ctxty=id;
		if(dsc.decl.hasParams){
			auto args=dsc.decl.params.map!((p){
				auto id=new Identifier(p.name.name);
				id.meaning=p;
				auto r=expressionSemantic(id,expSemContext(sc,ConstResult.no,InType.yes));
				assert(r.sstate==SemState.completed);
				return r;
			}).array;
			assert(dsc.decl.isTuple||args.length==1);
			ctxty=callSemantic(new CallExp(ctxty,dsc.decl.isTuple?new TupleExp(args):args[0],true,false),expSemContext(sc,ConstResult.no,InType.yes));
			ctxty.sstate=SemState.completed;
			assert(isType(ctxty));
		}
		if(dsc.decl.name.name==fd.name.name){
			assert(!fd.body_||!!fd.body_.blscope_);
			fd.isConstructor=true;
			if(fd.sstate!=SemState.error)
				dsc.decl.constructor=fd;
			if(fd.rret){
				sc.error("constructor cannot have return type annotation",fd.loc);
				fd.sstate=SemState.error;
			}else{
				assert(dsc.decl.dtype);
				fd.ret=ctxty;
			}
			if(dsc.decl.context){
				fd.context=dsc.decl.context; // TODO: ok?
				static if(language==psi) fd.contextVal=fd.context;
			}
			if(!fd.body_) return;
			auto thisVar=addVar("this",ctxty,fd.loc,fd.body_.blscope_); // the 'this' variable
			fd.thisVar=thisVar;
			if(!fd.body_.s.length||!cast(ReturnExp)fd.body_.s[$-1]){
				auto thisid=new Identifier(thisVar.getName);
				thisid.loc=fd.loc;
				thisid.scope_=fd.body_.blscope_;
				thisid.meaning=thisVar;
				thisid.type=ctxty;
				thisid.sstate=SemState.completed;
				auto rete=new ReturnExp(thisid);
				rete.loc=thisid.loc;
				rete.sstate=SemState.completed;
				fd.body_.s~=rete;
			}
		}else{
			static if(language==psi) fd.contextVal=addVar("this",unit,fd.loc,fsc);
			assert(!fd.body_||!!fd.body_.blscope_);
			assert(fsc.allowMerge);
			fsc.allowMerge=false; // TODO: this is hacky
			if(fd.body_) fd.context=addVar("this",ctxty,fd.loc,fd.body_.blscope_);
			fsc.allowMerge=true;
		}
		assert(dsc.decl.dtype);
	}else if(auto nsc=cast(NestedScope)sc){
		fd.context=addVar("`outer",contextTy(true),fd.loc,null); // TODO: replace contextTy by suitable record type; make name 'outer' available
		static if(language==psi) fd.contextVal=fd.context;
	}
}

Expression presemantic(Declaration expr,Scope sc){
	bool success=true; // dummy
	if(!expr.scope_) makeDeclaration(expr,success,sc);
	if(auto dat=cast(DatDecl)expr){
		if(dat.dtype) return expr;
		auto dsc=new DataScope(sc,dat);
		assert(!dat.dscope_);
		dat.dscope_=dsc;
		dat.dtype=new AggregateTy(dat,!dat.isQuantum);
		if(dat.hasParams) declareParameters(dat,true,dat.params,dsc);
		if(!dat.body_.ascope_) dat.body_.ascope_=new AggregateScope(dat.dscope_);
		if(cast(NestedScope)sc) dat.context = addVar("`outer",contextTy(true),dat.loc,null);
		foreach(ref exp;dat.body_.s) exp=makeDeclaration(exp,success,dat.body_.ascope_);
		foreach(ref exp;dat.body_.s) if(auto decl=cast(Declaration)exp) exp=presemantic(decl,dat.body_.ascope_);
	}
	if(auto fd=cast(FunctionDef)expr){
		if(fd.fscope_) return fd;
		auto fsc=new FunctionScope(sc,fd);
		fd.type=unit;
		fd.fscope_=fsc;
		declareParameters(fd,fd.isSquare,fd.params,fsc); // parameter variables
		if(fd.rret){
			fd.ret=typeSemantic(fd.rret,fsc);
			propErr(fd.rret,fd);
			setFtype(fd,true);
			if(!fd.body_){
				switch(fd.getName){
					case "invQImpl":
						// capture c:
						auto id=new Identifier("c");
						id.loc=fd.loc;
						expressionSemantic(id,expSemContext(fsc,ConstResult.yes,InType.no));
						break;
					default: break;
				}
				return expr;
			}
		}
		if(!fd.body_){
			sc.error("function without body should have a return type annotation",fd.loc);
			fd.sstate=SemState.error;
			return expr;
		}
		if(fd.sstate==SemState.completed)
			return fd;
		prepareFunctionDef(fd,sc);
	}
	return expr;
}

Expression makeDeclaration(Expression expr,ref bool success,Scope sc){
	if(auto imp=cast(ImportExp)expr){
		imp.scope_ = sc;
		auto ctsc=cast(TopScope)sc;
		if(!ctsc){
			sc.error("nested imports not supported",imp.loc);
			imp.sstate=SemState.error;
			return imp;
		}
		foreach(p;imp.e){
			auto path = getActualPath(ImportExp.getPath(p));
			Expression[] exprs;
			TopScope tsc;
			if(importModule(path,sc.handler,exprs,tsc,imp.loc)){
				imp.sstate=SemState.error;
			}
			if(tsc) ctsc.import_(tsc);
		}
		if(imp.sstate!=SemState.error) imp.sstate=SemState.completed;
		return imp;
	}
	if(auto decl=cast(Declaration)expr){
		if(!decl.scope_) success&=sc.insert(decl);
		return decl;
	}
	if(auto ce=cast(CommaExp)expr){
		ce.e1=makeDeclaration(ce.e1,success,sc);
		propErr(ce.e1,ce);
		ce.e2=makeDeclaration(ce.e2,success,sc);
		propErr(ce.e2,ce);
		return ce;
	}
	if(auto be=cast(DefineExp)expr){
		VarDecl makeVar(Identifier id){
			auto nid=new Identifier(id.name);
			nid.loc=id.loc;
			auto vd=new VarDecl(nid);
			vd.loc=id.loc;
			if(be.sstate!=SemState.error||!sc.lookupHere(nid,false,Lookup.probing))
				success&=sc.insert(vd);
			id.meaning=vd;
			id.id=vd.getId;
			id.scope_=sc;
			return vd;
		}
		if(auto id=cast(Identifier)be.e1){
			auto vd=makeVar(id);
			propErr(vd,be);
			return be;
		}else if(auto tpl=cast(TupleExp)be.e1){
			VarDecl[] vds;
			foreach(exp;tpl.e){
				if(auto id=cast(Identifier)exp) vds~=makeVar(id);
				else goto LbadDefLhs;
			}
			foreach(vd;vds) if(vd) propErr(vd,be);
			return be;
		}else if(auto ce=cast(CallExp)be.e1){
			auto f=ce.e,ft=cast(ProductTy)f.type;
			if(!ft||ft.isSquare!=ce.isSquare)
				goto LbadDefLhs;
			bool allConst=iota(ft.nargs).all!(i=>ft.isConstForReverse[i]);
			if(allConst) return be;
			bool allMoved=iota(ft.nargs).all!(i=>!ft.isConstForReverse[i]);
			if(auto tpl=cast(TupleExp)ce.arg){
				if(allMoved) goto LbadDefLhs;
				assert(!tpl.length||ft.isTuple&&ft);
				if(tpl.length!=ft.nargs){
					assert(ce.sstate==SemState.error);
					success=false;
					return null;
				}
				auto movedIndices=iota(tpl.length).filter!(i=>!ft.isConstForReverse[i]);
				VarDecl[] vds;
				foreach(exp;movedIndices.map!(i=>tpl.e[i])){
					if(auto id=cast(Identifier)exp) vds~=makeVar(id);
					else goto LbadDefLhs;
				}
				foreach(vd;vds) if(vd) propErr(vd,be);
				return be;
			}
			if(!allMoved) goto LbadDefLhs;
			if(auto id=cast(Identifier)ce.arg){
				auto vd=makeVar(id);
				propErr(vd,be);
				return be;
			}else goto LbadDefLhs;
		}else if(cast(IndexExp)be.e1){
			return be;
		}else if(auto ce=cast(CatExp)be.e1){
			if(!knownLength(ce.e1,true)&&!knownLength(ce.e2,true))
				goto LbadDefLhs;
			if(auto id=cast(Identifier)unwrap(ce.e1)) propErr(makeVar(id),be);
			else if(!cast(IndexExp)unwrap(be.e1)) goto LbadDefLhs;
			if(auto id=cast(Identifier)unwrap(ce.e2)) propErr(makeVar(id),be);
			else if(!cast(IndexExp)unwrap(be.e2)) goto LbadDefLhs;
			return be;
		}else LbadDefLhs:{
			if(be.sstate!=SemState.error){
				sc.error("invalid definition left-hand side",be.e1.loc);
				be.e1.sstate=SemState.error;
				be.sstate=SemState.error;
			}
			success=false;
		}
		success&=expr.sstate==SemState.completed;
		return expr;
	}
	if(auto tae=cast(TypeAnnotationExp)expr){
		if(auto id=cast(Identifier)tae.e){
			auto vd=new VarDecl(id);
			vd.loc=tae.loc;
			vd.dtype=tae.t;
			vd.vtype=typeSemantic(vd.dtype,sc);
			vd.loc=id.loc;
			success&=sc.insert(vd);
			id.meaning=vd;
			id.id=vd.getId;
			id.scope_=sc;
			return vd;
		}
	}
	if(expr.sstate!=SemState.error&&expr.loc.line!=0)
		sc.error("not a declaration: "~expr.toString()~" ",expr.loc);
	expr.sstate=SemState.error;
	success=false;
	return expr;
}

void checkNotLinear(Expression e,Scope sc){
	if(sc.allowsLinear()) return;
	if(auto decl=cast(Declaration)e){
		if(decl.isLinear()){
			sc.error(format("cannot make linear declaration '%s' at this location",e),e.loc);
			e.sstate=SemState.error;
		}
	}
}


Expression[] semantic(Expression[] exprs,Scope sc){
	bool success=true;
	foreach(ref expr;exprs) if(!cast(DefineExp)expr&&!cast(CommaExp)expr) expr=makeDeclaration(expr,success,sc); // TODO: get rid of special casing?
	/+foreach(ref expr;exprs){
	 if(auto decl=cast(Declaration)expr) expr=presemantic(decl,sc);
		if(cast(DefineExp)expr) expr=makeDeclaration(expr,success,sc);
	}+/
	foreach(ref expr;exprs){
		if(auto decl=cast(Declaration)expr) expr=presemantic(decl,sc);
		expr=toplevelSemantic(expr,sc);
		success&=expr.sstate==SemState.completed;
	}
	foreach(expr;exprs){ // TODO: ok?
		if(expr.sstate==SemState.passive)
			expr.sstate=SemState.completed;
	}
	if(!sc.allowsLinear()){
		foreach(ref expr;exprs){
			checkNotLinear(expr,sc);
		}
	}
	return exprs;
}

Expression toplevelSemanticImpl(FunctionDef fd,Scope sc){
	return functionDefSemantic(fd,sc);
}
Expression toplevelSemanticImpl(DatDecl dd,Scope sc){
	return datDeclSemantic(dd,sc);
}
Expression toplevelSemanticImpl(DefineExp expr,Scope sc){
	return defineOrAssignSemantic(expr,sc);
}
Expression toplevelSemanticImpl(CommaExp ce,Scope sc){
	return expectDefineOrAssignSemantic(ce,sc);
}
Expression toplevelSemanticImpl(ImportExp imp,Scope sc){
	assert(util.among(imp.sstate,SemState.error,SemState.completed));
	return imp;
}
Expression toplevelSemanticImplDefault(Expression expr,Scope sc){
	sc.error("not supported at toplevel",expr.loc);
	expr.sstate=SemState.error;
	return expr;
}

Expression toplevelSemantic(Expression expr,Scope sc){
	if(expr.sstate==SemState.error) return expr;
	return expr.dispatchDecl!(toplevelSemanticImpl,toplevelSemanticImplDefault)(sc);
}

static if(language==silq)
enum BuiltIn{
	none,
	π,pi=π,
	primitive,
	show,
	query,
	typeTy,
	bottom,
	unit,
	B,two=B,
	ℕ,N=ℕ,
	ℤ,Z=ℤ,
	ℚ,Q=ℚ,
	ℝ,R=ℝ,
	ℂ,C=ℂ,
}

static if(language==psi)
enum BuiltIn{
	none,
	π,pi=π,
	readCSV,
	Marginal,
	sampleFrom,
	Expectation,
	typeTy,
	bottom,
	unit,
	B,two=B,
	ℕ,N=ℕ,
	ℤ,Z=ℤ,
	ℚ,Q=ℚ,
	ℝ,R=ℝ,
	ℂ,C=ℂ,
}

BuiltIn isBuiltIn(Identifier id){
	if(!id||id.meaning) return BuiltIn.none;
	switch(id.name){
		default: return BuiltIn.none;
		case "π","pi": return BuiltIn.π;
		static if(language==psi){
			case "readCSV":
				return BuiltIn.readCSV;
		}
		static if(language==silq){
			case "__primitive":
				return BuiltIn.primitive;
			case "__show":
				return BuiltIn.show;
			case "__query":
				return BuiltIn.query;
		}else static if(language==psi){
			case "Marginal":
				return BuiltIn.Marginal;
			case "sampleFrom":
				return BuiltIn.sampleFrom;
			case "Expectation":
				return BuiltIn.Expectation;
		}else static assert(0);
		case "*":
			return BuiltIn.typeTy;
		case "𝟘","⊥","bottom","never":
			return BuiltIn.bottom;
		case "𝟙","unit":
			return BuiltIn.unit;
		case "𝔹","B","𝟚":
			return BuiltIn.B;
		case "ℕ","N":
			return BuiltIn.ℕ;
		case "ℤ","Z":
			return BuiltIn.ℤ;
		case "ℚ","Q":
			return BuiltIn.ℚ;
		case "ℝ","R":
			return BuiltIn.ℝ;
		case "ℂ","C":
			return BuiltIn.ℂ;
	}
}

static if(language==silq)
enum PreludeSymbol{
	none,
	dup,
	measure,
	H,
	X,
	Y,
	Z,
	phase,
	rotX,
	rotY,
	rotZ,
	I,
	S,
	CNOT,
	reverse,
	floor,
	ceil,
	round,
	inℤ,
	sqrt,
	exp,
	log,
	sin,
	asin,
	cos,
	acos,
	tan,
	atan,
	abs,
	min,
	max,
	array,
	vector,
	print,
	dump,
	exit,
}

static if(language==psi)
enum PreludeSymbol{
	none,
	// TODO
}

PreludeSymbol isPreludeSymbol(Identifier id){
	if(!id||!id.meaning) return PreludeSymbol.none;
	return isPreludeSymbol(id.meaning);
}
PreludeSymbol isPreludeSymbol(Declaration decl){
	if(!isInPrelude(decl)) return PreludeSymbol.none;
	if(!decl.name) return PreludeSymbol.none;
	switch(decl.name.name){
		default: return PreludeSymbol.none;
		import std.traits:EnumMembers;
		static foreach(ps;EnumMembers!PreludeSymbol){
			case text(ps):
				return ps;
		}
	}
}

PreludeSymbol isPreludeCall(CallExp ce){
	if(!ce) return PreludeSymbol.none;
	return isPreludeSymbol(cast(Identifier)ce.e);
}
BuiltIn isBuiltInCall(CallExp ce){
	if(!ce) return BuiltIn.none;
	return isBuiltIn(cast(Identifier)ce.e);
}

static if(language==silq)
string isPrimitive(Expression e){
	auto ce=cast(CallExp)e;
	if(!ce) return null;
	auto id=cast(Identifier)ce.e;
	if(!id) return null;
	if(id.meaning || id.name != "__primitive") return null;
	auto args=cast(TupleExp)ce.arg;
	enforce(!!args&&args.e.length==2);
	auto opLit=cast(LiteralExp)args.e[0];
	enforce(!!opLit&&opLit.lit.type==Tok!"``");
	return opLit.lit.str;
}

// TODO `class PrimitiveExp: Expression { string prim; Expression[] args; Annotation annotation; }`
static if(language==silq)
string isPrimitiveCall(Expression e){
	auto ce=cast(CallExp)e;
	if(!ce) return null;
	if(ce.isSquare || ce.isClassical_) return null;
	return isPrimitive(ce.e);
}

Identifier getPreludeSymbol(string name,Location loc,Scope isc){
	auto res=new Identifier(name);
	res.loc=loc;
	res.scope_=isc;
	res.meaning=getPreludeScope(isc.handler, loc).lookup(res,false,false,Lookup.constant);
	if(!res.meaning){
		res.sstate=SemState.error;
	}else{
		res.type=res.typeFromMeaning;
		res.constLookup=false;
		res.sstate=SemState.completed;
	}
	return res;
}

static if(language==psi)
Expression getDistribution(Location loc,Scope sc){
	return getPreludeSymbol("Distribution",loc,sc);
}

static if(language==psi)
Expression distributionTy(Expression base,Scope sc){
	return typeSemantic(new CallExp(getDistribution(base.loc,sc),base,true,true),sc);
}

Expression builtIn(Identifier id,Scope sc){
	Expression t=null;
	switch(id.name){
		static if(language==psi){
			case "readCSV": t=funTy(stringTy(true),arrayTy(ℝ(true)),false,false,true); break;
		}
		case "π","pi": t=ℝ(true); break;
		static if(language==psi){
			case "Marginal","sampleFrom":
				t=unit;
				break;
		}
		static if(language==silq){
			case "__primitive","__query","__show":
				t=unit;
				break; // those are actually magic polymorphic functions
		}
		static if(language==psi){
			case "Expectation": t=funTy(ℝ(false),ℝ(false),false,false,true); break; // TODO: should be lifted
		}
		static if(language==silq){
			case "ctype","qtype","qnumeric","utype","etype":
				goto case;
		}
		case "*","type","𝟘","⊥","bottom","never","𝟙","unit","𝟚","B","𝔹","N","ℕ","Z","ℤ","Q","ℚ","R","ℝ","C","ℂ":
			id.type=ctypeTy;
			switch(id.name){
				case "*","type": return typeTy;
				static if(language==silq){
					case "ctype": return ctypeTy;
					case "qtype": return qtypeTy;
					case "qnumeric": return qnumericTy;
				}
				case "utype": return utypeTy;
				case "etype": return etypeTy;
				case "𝟘","⊥","bottom","never": return bottom;
				case "𝟙","unit": return unit;
				case "𝟚","B","𝔹": return Bool(false);
				case "N","ℕ": return ℕt(false);
				case "Z","ℤ": return ℤt(false);
				case "Q","ℚ": return ℚt(false);
				case "R","ℝ": return ℝ(false);
				case "C","ℂ": return ℂ(false);
				default: return null;
			}
		default: return null;
	}
	id.type=t;
	id.sstate=SemState.completed;
	return id;
}

bool isBuiltIn(FieldExp fe)in{
	assert(fe.e.sstate==SemState.completed);
}do{
	if(fe.f.meaning) return false;
	if(cast(ArrayTy)fe.e.type||cast(VectorTy)fe.e.type||cast(TupleTy)fe.e.type){
		if(fe.f.name=="length"){
			return true;
		}
	}
	return false;
}

Expression builtIn(FieldExp fe,Scope sc)in{
	assert(fe.e.sstate==SemState.completed);
}do{
	if(fe.f.meaning) return null;
	if(cast(ArrayTy)fe.e.type||cast(VectorTy)fe.e.type||cast(TupleTy)fe.e.type){
		if(fe.f.name=="length"){
			fe.type=ℕt(true); // no superpositions over arrays with different lengths
			fe.f.sstate=SemState.completed;
			return fe;
		}else return null;
	}
	return null;
}

bool isFieldDecl(Expression e){
	if(cast(VarDecl)e) return true;
	if(auto tae=cast(TypeAnnotationExp)e)
		if(auto id=cast(Identifier)tae.e)
			return true;
	return false;
}

Expression fieldDeclSemantic(Expression e,Scope sc)in{
	assert(isFieldDecl(e));
}do{
	e.sstate=SemState.completed;
	return e;
}

Expression expectFieldDeclSemantic(Expression e,Scope sc){
	if(auto ce=cast(CommaExp)e){
		ce.e1=expectFieldDeclSemantic(ce.e1,sc);
		ce.e2=expectFieldDeclSemantic(ce.e2,sc);
		propErr(ce.e1,ce);
		propErr(ce.e2,ce);
		return ce;
	}
	if(isFieldDecl(e)) return fieldDeclSemantic(e,sc);
	sc.error("expected field declaration",e.loc);
	e.sstate=SemState.error;
	return e;
}

Expression nestedDeclSemantic(Expression e,Scope sc){
	if(auto fd=cast(FunctionDef)e)
		return functionDefSemantic(fd,sc);
	if(auto dd=cast(DatDecl)e)
		return datDeclSemantic(dd,sc);
	if(isFieldDecl(e)) return fieldDeclSemantic(e,sc);
	if(auto ce=cast(CommaExp)e) return expectFieldDeclSemantic(ce,sc);
	sc.error("not a declaration",e.loc);
	e.sstate=SemState.error;
	return e;
}

CompoundDecl compoundDeclSemantic(CompoundDecl cd,Scope sc){
	auto asc=cd.ascope_;
	if(!asc) asc=new AggregateScope(sc);
	++asc.getDatDecl().semanticDepth;
	scope(exit) if(--asc.getDatDecl().semanticDepth==0&&asc.close()) cd.sstate=SemState.error; // TODO: fix
	cd.ascope_=asc;
	bool success=true; // dummy
	foreach(ref e;cd.s) e=makeDeclaration(e,success,asc);
	foreach(ref e;cd.s) if(auto decl=cast(Declaration)e) e=presemantic(decl,asc);
	foreach(ref e;cd.s){
		e=nestedDeclSemantic(e,asc);
		propErr(e,cd);
	}
	if(!sc.allowsLinear()){
		foreach(ref e;cd.s){
			checkNotLinear(e,sc);
			propErr(e,cd);
		}
	}
	cd.type=unit;
	return cd;
}

Expression statementSemanticImpl(CallExp ce,Scope sc){
	auto context=expSemContext(sc,ConstResult.yes,InType.no);
	return callSemantic(ce,context.nestConst);
}

Expression statementSemanticImpl(IndexExp idx,Scope sc){
	auto context=expSemContext(sc,ConstResult.yes,InType.no);
	idx.e=expressionSemantic(idx.e,context.nestConst);
	if(auto ft=cast(FunTy)idx.e.type){
		auto ce=new CallExp(idx.e,idx.a,true,false);
		ce.loc=idx.loc;
		return callSemantic(ce,context.nestConst);
	}else return statementSemanticImplDefault(idx,sc);
}

Expression statementSemanticImpl(TypeAnnotationExp tae,Scope sc){
	tae.e=statementSemantic(tae.e,sc);
	auto context=expSemContext(sc,ConstResult.yes,InType.no);
	return expressionSemantic(tae,context.nestConst);
}

CompoundExp statementSemanticImpl(CompoundExp ce,Scope sc){
	foreach(ref s;ce.s){
		s=statementSemantic(s,sc);
		propErr(s,ce);
	}
	return ce;
}

Expression statementSemanticImpl(IteExp ite,Scope sc){
	ite.cond=conditionSemantic!true(ite.cond,sc,InType.no);
	if(ite.cond.type) ite.cond.type=ite.cond.type.eval();
	static if(language==silq){
		auto quantumControl=ite.cond.type&&!ite.cond.type.isClassical();
		auto restriction_=quantumControl?Annotation.mfree:Annotation.none;
	}else{
		enum quantumControl=false;
		enum restriction_=Annotation.none;
	}
	// initialize scopes, to allow captures to be inserted
	if(!ite.then.blscope_) ite.then.blscope_=new BlockScope(sc,restriction_);
	if(!ite.othw){
		ite.othw=New!CompoundExp((Expression[]).init);
		ite.othw.loc=ite.loc;
	}
	if(!ite.othw.blscope_) ite.othw.blscope_=new BlockScope(sc,restriction_);
	ite.then=controlledCompoundExpSemantic(ite.then,sc,ite.cond,restriction_);
	ite.othw=controlledCompoundExpSemantic(ite.othw,sc,ite.cond,restriction_);
	propErr(ite.cond,ite);
	propErr(ite.then,ite);
	propErr(ite.othw,ite);
	NestedScope[] scs;
	assert(equal(sc.activeNestedScopes,only(ite.then.blscope_,ite.othw.blscope_)));
	foreach(branch;only(ite.then,ite.othw)){
		if(!definitelyReturns(branch)) scs~=branch.blscope_;
		else branch.blscope_.closeUnreachable(sc);
	}
	sc.activeNestedScopes=scs;
	if(scs.length && sc.merge(quantumControl,scs)){
		sc.note("trying to merge branches of this if expression", ite.loc);
		ite.sstate=SemState.error;
	}
	ite.type=definitelyReturns(ite.then)&&definitelyReturns(ite.othw)?bottom:unit;
	return ite;
}

static if(language==silq)
Expression statementSemanticImpl(WithExp with_,Scope sc){
	if(with_.bdy.s.length){
		if(auto ret=cast(ReturnExp)with_.bdy.s[$-1]){ // TODO: generalize?
			if(ret.e.sstate==SemState.initial){
				auto id=new Identifier(freshName());
				id.loc=ret.e.loc;
				auto id2=id.copy();
				auto def=new DefineExp(id2,ret.e);
				def.loc=ret.loc;
				ret.e=id;
				with_.bdy.s[$-1]=def;
				auto r=new CompoundExp([with_,ret]);
				r.loc=with_.loc;
				return statementSemantic(r,sc);
			}
		}
	}
	if(with_.isIndices){
		foreach(e;with_.trans.s){
			auto de=cast(DefineExp)e;
			assert(!!de);
			auto id=cast(Identifier)unwrap(de.e1);
			assert(!!id);
			auto idx=cast(IndexExp)unwrap(de.e2);
			assert(!!idx);
			id.byRef=true;
			idx.byRef=true;
		}
	}
	with_.trans=compoundExpSemantic(with_.trans,sc,Annotation.mfree);
	if(with_.trans.blscope_) sc.merge(false,with_.trans.blscope_);
	if(auto ret=mayReturn(with_.trans)){
		sc.error("cannot return from within `with` transformation",ret.loc);
		ret.sstate=SemState.error;
		with_.trans.sstate=SemState.error;
	}
	propErr(with_.trans,with_);
	with_.bdy=compoundExpSemantic(with_.bdy,sc);
	if(with_.bdy.blscope_) sc.merge(false,with_.bdy.blscope_);
	if(auto ret=mayReturn(with_.bdy)){
		sc.error("early return in `with` body must be last statement",ret.loc);
		ret.sstate=SemState.error;
		with_.bdy.sstate=SemState.error;
	}
	propErr(with_.trans,with_);
	if(with_.itrans){
		if(with_.itrans.sstate!=SemState.completed&&with_.itrans.sstate!=SemState.error){
			with_.itrans=compoundExpSemantic(with_.itrans,sc,Annotation.mfree);
			if(with_.itrans.blscope_) sc.merge(false,with_.itrans.blscope_);
		}
	}else if(with_.trans.sstate==SemState.completed){
		with_.itrans=new CompoundExp(reverseStatements(with_.trans.s,[],sc,false)); // TODO: fix (this is incomplete)
		with_.itrans.loc=with_.trans.loc;
		with_.itrans=compoundExpSemantic(with_.itrans,sc,Annotation.mfree);
		if(with_.itrans.blscope_) sc.merge(false,with_.itrans.blscope_);
		if(with_.itrans.sstate==SemState.error){
			sc.note("unable to reverse with transformation",with_.itrans.loc);
		}
		propErr(with_.itrans,with_);
	}
	with_.type=unit;
	if(with_.sstate!=SemState.error) with_.sstate=SemState.completed;
	return with_;
}

Expression statementSemanticImpl(ReturnExp ret,Scope sc){
	return returnExpSemantic(ret,sc);
}
Expression statementSemanticImpl(FunctionDef fd,Scope sc){
	return functionDefSemantic(fd,sc);
}
Expression statementSemanticImpl(DatDecl dd,Scope sc){
	return datDeclSemantic(dd,sc);
}
Expression statementSemanticImpl(CommaExp ce,Scope sc){
	return expectDefineOrAssignSemantic(ce,sc);
}

struct FixedPointIterState{
	Scope.ScopeState origStateSnapshot;
	Scope.ScopeState prevStateSnapshot;
	Scope.ScopeState nextStateSnapshot;
	BlockScope loopScope=null;
	BlockScope forgetScope=null;
	void beginIteration(){ prevStateSnapshot=nextStateSnapshot; }
	BlockScope makeScopes(Scope sc){
		loopScope=new BlockScope(sc);
		forgetScope=new BlockScope(sc);
		return loopScope;
	}
	void endIteration(Scope sc){ nextStateSnapshot=sc.getStateSnapshot(true); }
	bool converged(){ return nextStateSnapshot==prevStateSnapshot; }

	void fixSplitMergeGraph(Scope sc){
		sc.fixLoopSplitMergeGraph(loopScope,forgetScope,origStateSnapshot,prevStateSnapshot);
	}
}
FixedPointIterState startFixedPointIteration(Scope sc){
	auto origStateSnapshot=sc.getStateSnapshot(true);
	return FixedPointIterState(origStateSnapshot,origStateSnapshot,origStateSnapshot);
}

Expression lowerLoop(T)(T loop,FixedPointIterState state,Scope sc)in{
	assert(loop.sstate==SemState.completed);
}do{
	enum returnOnlyMoved=false; // (experimental)
	auto loopParams_=state.nextStateSnapshot.loopParams(loop.bdy.blscope_);
	auto constParams=loopParams_[0], movedParams=loopParams_[1];
	static if(is(T==WhileExp)){
		Q!(Id,Expression,bool,Location)[] loopParams=[];
	}else static if(is(T==ForExp)){
		auto loopVarId=loop.var.id;
		assert(loop.left.type && loop.right.type);
		auto loopVarType=joinTypes(loop.left.type, loop.right.type);
		auto loopParams=[q(loopVarId,cast(BoolTy)loopVarType?ℕt(true):loopVarType,true,loop.var.loc)];
	}else static if(is(T==RepeatExp)){
		auto loopVarId=freshName();
		Expression loopVarType=ℕt(true);
		auto loopParams=[q(loopVarId,loopVarType,true,loop.num.loc)];
	}else static assert(0);
	Expression.CopyArgs cargsDefault;
	//imported!"util.io".writeln(constParams,movedParams,nsbdy);
	Identifier[] ids(Q!(Id,Expression,bool,Location)[] prms,bool checkDefined=false){
		return prms.map!((p){
			auto id=new Identifier(p[0]);
			id.loc=p[3];
			return id;
		}).filter!((id){
			if(!checkDefined) return true;
			return !!sc.lookupHere(id,false,Lookup.probing);
		}).array;
	}
	auto fi=freshName();
	auto allParams=loopParams~constParams~movedParams;
	auto loopConstParams=loopParams~constParams;
	auto constMovedParams=constParams~movedParams;
	static if(returnOnlyMoved){
		auto movedTpl=new TupleExp(cast(Expression[])ids(movedParams,true));
		movedTpl.loc=loop.loc;
		auto returnTpl=movedTpl;
	}else{
		auto returnTpl=new TupleExp(cast(Expression[])ids(constMovedParams.filter!(p=>p[2]).array,true));
		returnTpl.loc=loop.loc;
	}
	auto cee=new Identifier(fi);
	cee.loc=loop.loc;
	Identifier[] constTmpNames;
	Parameter[] params;
	foreach(i,p;allParams){
		bool isConst=i<loopParams.length+constParams.length;
		bool mayChange=p[2];
		auto id=isConst&&mayChange?freshName:p[0];
		auto pname=new Identifier(id);
		pname.loc=p[3];
		if(isConst&&mayChange) constTmpNames~=pname.copy(cargsDefault);
		auto ptype=p[1];
		auto param=new Parameter(isConst,pname,ptype);
		params~=param;
	}
	auto paramTmpTpl=new TupleExp(cast(Expression[])chain(constTmpNames[loopParams.length..$].map!(id=>id.copy(cargsDefault)),ids(movedParams)).array);
	DefineExp constParamDef=null;
	if(constTmpNames.length){
		auto constTmpTpl=new TupleExp(cast(Expression[])constTmpNames);
		constTmpTpl.loc=loop.loc;
		auto constTpl=new TupleExp(cast(Expression[])ids(loopConstParams.filter!(p=>p[2]).array));
		constTpl.loc=loop.loc;
		static if(is(T==ForExp)){
			if(loopConstParams[0][2]&&loopConstParams[0][1]!is loopVarType){
				auto tae=new TypeAnnotationExp(constTpl.e[0],loopVarType,TypeAnnotationType.coercion);
				tae.loc=constTpl.e[0].loc;
				constTpl.e[0]=tae;
			}
		}
		constParamDef=new DefineExp(constTpl,constTmpTpl);
		constParamDef.loc=loop.loc;
	}
	static if(is(T==WhileExp)){
		auto ncond=loop.cond.copy(cargsDefault);
	}else static if(is(T==ForExp)){
		//writeln("?? ",constParams);
		auto leftName=new Identifier(freshName());
		leftName.loc=loop.left.loc;
		auto leftInit=loop.left.copy(cargsDefault);
		leftInit.loc=loop.left.loc;
		if(loop.leftExclusive){
			auto one=LiteralExp.makeInteger(1);
			one.loc=loop.left.loc;
			leftInit=new AddExp(leftInit,one);
			leftInit.loc=loop.left.loc;
		}
		auto leftDef=new DefineExp(leftName,leftInit);
		leftDef.loc=loop.left.loc;
		auto rightName=new Identifier(freshName());
		rightName.loc=loop.right.loc;
		auto rightInit=loop.right.copy(cargsDefault);
		rightInit.loc=loop.right.loc;
		if(!loop.rightExclusive){
			auto one=LiteralExp.makeInteger(1);
			one.loc=loop.right.loc;
			rightInit=new AddExp(rightInit,one);
			rightInit.loc=loop.right.loc;
		}
		auto rightDef=new DefineExp(rightName,rightInit);
		rightDef.loc=loop.right.loc;
		Identifier stepName=null;
		Expression stepDef=null;
		if(loop.step){
			stepName=new Identifier(freshName());
			auto stepInit=loop.step.copy(cargsDefault);
			stepInit.loc=loop.step.loc;
			stepDef=new DefineExp(stepName,stepInit);
			stepDef.loc=loop.step.loc;
		}
		auto loopVarName=constTmpNames[0].copy(cargsDefault);
		loopVarName.loc=loop.var.loc;
		auto ncond=new LtExp(loopVarName,rightName.copy(cargsDefault));
		ncond.loc=loop.loc;
	}else static if(is(T==RepeatExp)){
		auto numName=new Identifier(freshName());
		numName.loc=loop.num.loc;
		auto numInit=loop.num.copy(cargsDefault);
		numInit.loc=loop.num.loc;
		auto numDef=new DefineExp(numName,numInit);
		numDef.loc=loop.num.loc;
		auto loopVarName=new Identifier(loopVarId);
		loopVarName.loc=loop.num.loc;
		auto ncond=new LtExp(loopVarName,numName.copy(cargsDefault));
		ncond.loc=loop.loc;
	}else static assert(0,"unsupported type of loop for lowering: ",T);
	auto paramTpl=new TupleExp(cast(Expression[])ids(allParams));
	paramTpl.loc=loop.loc;
	static if(is(T==ForExp)){{
		auto loopVar=constTmpNames[0].copy(cargsDefault);
		auto step=stepName?stepName.copy(cargsDefault):LiteralExp.makeInteger(1);
		step.loc=loopVar.loc;
		auto addExp=new AddExp(loopVar,step);
		paramTpl.e[0]=addExp;
	}}else static if(is(T==RepeatExp)){{
		auto loopVar=paramTpl.e[0];
		auto step=LiteralExp.makeInteger(1);
		step.loc=loopVar.loc;
		auto addExp=new AddExp(loopVar,step);
		paramTpl.e[0]=addExp;
	}}
	auto ce=new CallExp(cee,paramTpl,false,false);
	ce.loc=loop.loc;
	//auto thene=new ReturnExp(ce); // avoid non-toplevel return
	auto retName=new Identifier(freshName());
	retName.loc=loop.loc;
	auto nbdy=loop.bdy.copy(cargsDefault);
	if(!definitelyReturns(loop.bdy)){
		auto thene=new DefineExp(retName,ce);
		thene.loc=ce.loc;
		nbdy.s~=thene;
	}
	bool hasEarlyReturns=false;
	Expression inj(Expression e,bool isRet){ // TODO: use sum type
		auto wrap=new VectorExp([e]);
		wrap.loc=e.loc;
		auto dummy=new VectorExp([]);
		dummy.loc=e.loc;
		auto res=new TupleExp(isRet?[wrap,dummy]:[dummy,wrap]);
		res.loc=e.loc;
		return res;
	}
	void match(ref Expression[] stmts,Expression e,Expression rlhs,CompoundExp ret,Expression olhs,CompoundExp other){
		auto lhs=new TupleExp([new Identifier(freshName),new Identifier(freshName)]);
		lhs.e.each!(id=>id.loc=e.loc);
		auto mdef=new DefineExp(lhs,e);
		mdef.loc=e.loc;
		stmts~=mdef;
		auto zero=LiteralExp.makeInteger(0);
		zero.loc=e.loc;
		auto lenId=new Identifier("length");
		lenId.loc=e.loc;
		auto len=new FieldExp(lhs.e[0].copy(),lenId);
		len.loc=e.loc;
		auto isret=new BinaryExp!(Tok!"≠")(len,zero);
		isret.loc=e.loc;
		auto rwrap=new VectorExp([rlhs]);
		rwrap.loc=rlhs.loc;
		auto remp=new VectorExp([]);
		remp.loc=rlhs.loc;
		auto runpl=new TupleExp([rwrap,remp]);
		runpl.loc=rlhs.loc;
		Expression runp=new DefineExp(runpl,lhs.copy());
		runp.loc=rlhs.loc;
		auto oemp=new VectorExp([]);
		oemp.loc=olhs.loc;
		auto owrap=new VectorExp([olhs]);
		owrap.loc=olhs.loc;
		auto ounpl=new TupleExp([oemp,owrap]);
		ounpl.loc=olhs.loc;
		Expression ounp=new DefineExp(ounpl,lhs.copy());
		ounp.loc=olhs.loc;
		ret.s=[runp]~ret.s;
		other.s=[ounp]~other.s;
		auto ite=new IteExp(isret,ret,other);
		ite.loc=e.loc;
		stmts~=ite;
	}
	void adjustEarlyReturns(Expression e){
		if(auto ret=cast(ReturnExp)e){
			hasEarlyReturns=true;
			ret.e=inj(ret.e,true);
		}else if(auto ce=cast(CompoundExp)e){
			foreach(s;ce.s)
				adjustEarlyReturns(s);
		}else if(auto ite=cast(IteExp)e){
			adjustEarlyReturns(ite.then);
			adjustEarlyReturns(ite.othw);
		}else if(auto fe=cast(ForExp)e)
			adjustEarlyReturns(fe.bdy);
		else if(auto we=cast(WhileExp)e)
			adjustEarlyReturns(we.bdy);
		else if(auto re=cast(RepeatExp)e)
			adjustEarlyReturns(re.bdy);
		else if(auto we=cast(WithExp)e)
			adjustEarlyReturns(we.bdy);
	}
	Expression bdy;
	if(!isTrue(ncond)){
		adjustEarlyReturns(nbdy);
		//auto othwe=new ReturnExp(returnTpl) // avoid non-toplevel return
		Expression retexp=returnTpl;
		if(hasEarlyReturns) retexp=inj(retexp,false);
		auto othwe=new DefineExp(retName.copy(cargsDefault),retexp);
		othwe.loc=loop.loc;
		auto othw=new CompoundExp([othwe]);
		othw.loc=othwe.loc;
		auto ite=new IteExp(ncond,nbdy,othw);
		ite.loc=loop.loc;
		bdy=ite;
	}else bdy=nbdy;
	auto fdn=new Identifier(fi);
	fdn.loc=loop.loc;
	auto ret=new ReturnExp(retName.copy(cargsDefault)); // avoid non-toplevel return
	ret.loc=loop.loc;
	auto cmpbdy=cast(CompoundExp)bdy;
	auto fbdy=new CompoundExp((constParamDef?[cast(Expression)constParamDef]:[])~(cmpbdy?cmpbdy.s~ret:[bdy,ret]));
	fbdy.loc=bdy.loc;
	auto fd=new FunctionDef(fdn,params,true,null,fbdy);
	fd.annotation=pure_;
	fd.inferAnnotation=true;
	fd.loc=loop.loc;
	static if(is(T==ForExp)){
		auto paramTpl2=new TupleExp([cast(Expression)leftName.copy(cargsDefault)]~cast(Expression[])ids(constMovedParams));
		paramTpl2.loc=loop.loc;
		auto ce2=new CallExp(cee.copy(cargsDefault),paramTpl2,false,false);
		ce2.loc=loop.loc;
	}else static if(is(T==RepeatExp)){
		auto zero=LiteralExp.makeInteger(0);
		zero.loc=loop.loc;
		auto paramTpl2=new TupleExp([cast(Expression)zero]~cast(Expression[])ids(constMovedParams));
		paramTpl2.loc=loop.loc;
		auto ce2=new CallExp(cee.copy(cargsDefault),paramTpl2,false,false);
		ce2.loc=loop.loc;
	}else{
		auto ce2=ce.copy(cargsDefault);
	}
	static if(returnOnlyMoved){
		auto defTpl=movedTpl.copy(cargsDefault);
	}else{
		auto defTpl=new TupleExp(cast(Expression[])chain(constTmpNames[loopParams.length..$].map!(id=>id.copy(cargsDefault)),ids(movedParams,true)).array);
		defTpl.loc=loop.loc;
	}
	Expression[] stmts=[fd];
	void defineLocals(ref Expression[] stmts,Expression locals){
		auto def=new DefineExp(defTpl,locals);
		def.loc=loop.loc;
		stmts~=def;
		static if(!returnOnlyMoved){
			if(constTmpNames[loopParams.length..$].length){
				auto assgnTpl1=new TupleExp(cast(Expression[])ids(constParams.filter!(p=>p[2]).array));
				assgnTpl1.loc=loop.loc;
				auto assgnTpl2=new TupleExp(cast(Expression[])constTmpNames[loopParams.length..$].map!(id=>id.copy(cargsDefault)).array);
				assgnTpl2.loc=loop.loc;
				auto assgn=new AssignExp(assgnTpl1,assgnTpl2);
				assgn.loc=loop.loc;
				stmts~=assgn;
			}
		}
	}
	if(hasEarlyReturns){
		auto retId2=new Identifier(freshName());
		retId2.loc=ce2.loc;
		auto fret=new ReturnExp(retId2.copy());
		fret.loc=ce2.loc;
		auto then=new CompoundExp([fret]);
		auto locals=new Identifier(freshName());
		locals.loc=ce2.loc;
		Expression[] defLocals;
		defineLocals(defLocals,locals.copy());
		auto othw=new CompoundExp(defLocals);
		match(stmts,ce2,retId2,then,locals,othw);
	}else if(isTrue(ncond)){
		auto fret=new ReturnExp(ce2);
		fret.loc=loop.loc;
		stmts~=fret;
	}else if(defTpl.e.length){
		defineLocals(stmts,ce2);
	}else{
		stmts~=ce2;
	}
	static if(is(T==ForExp)){
		stmts=[cast(Expression)leftDef]~(stepDef?[stepDef]:[])~[cast(Expression)rightDef]~stmts;
	}else static if(is(T==RepeatExp)){
		stmts=[cast(Expression)numDef]~stmts;
	}
	auto lowered=new CompoundExp(stmts);
	lowered.loc=loop.loc;
	sc.restoreStateSnapshot(state.origStateSnapshot);
	//imported!"util.io".writeln(lowered);
	auto result=statementSemantic(lowered,sc);
	if(result.sstate==SemState.error){
		sc.note("loop not yet supported by loop lowering pass",result.loc);
	}
	static if(__traits(hasMember,astopt,"dumpLoops")) if(astopt.dumpLoops){
		import util.io:stderr;
		stderr.writeln(loop);
		stderr.writeln("-loop-lowering→");
		stderr.writeln(result);
	}
	return result;
}

// TODO: supertypes for define and assign?
Expression statementSemanticImpl(ForExp fe,Scope sc){
	auto context=expSemContext(sc,ConstResult.yes,InType.no);
	assert(!fe.bdy.blscope_);
	fe.left=expressionSemantic(fe.left,context.nestConst);
	propErr(fe.left,fe);
	static if(language==silq) sc.clearConsumed();
	if(fe.left.sstate==SemState.completed && !isSubtype(fe.left.type, ℝ(true))){
		sc.error(format("lower bound for loop variable should be a classical number, not %s",fe.left.type),fe.left.loc);
		fe.sstate=SemState.error;
	}
	if(fe.step){
		fe.step=expressionSemantic(fe.step,context.nestConst);
		if(fe.step.sstate==SemState.completed && !isSubtype(fe.step.type, ℤt(true))){
			sc.error(format("step should be a classical integer, not %s",fe.step.type),fe.step.loc);
			fe.sstate=SemState.error;
		}
	}
	fe.right=expressionSemantic(fe.right,context.nestConst);
	propErr(fe.right,fe);
	static if(language==silq) sc.clearConsumed();
	if(fe.right.sstate==SemState.completed && !isSubtype(fe.right.type, ℝ(true))){
		sc.error(format("upper bound for loop variable should be a classical number, not %s",fe.right.type),fe.right.loc);
		fe.sstate=SemState.error;
	}
	bool converged=false;
	CompoundExp bdy;
	auto state=startFixedPointIteration(sc);
	while(!converged){ // TODO: limit number of iterations?
		state.beginIteration();
		Expression.CopyArgs cargs={preserveSemantic: true};
		bdy=fe.bdy.copy(cargs);
		auto fesc=bdy.blscope_=state.makeScopes(sc);
		auto vd=new VarDecl(fe.var);
		vd.vtype=fe.left.type && fe.right.type ? joinTypes(fe.left.type, fe.right.type) : ℤt(true);
		assert(fe.sstate==SemState.error||vd.vtype.isClassical());
		if(fe.sstate==SemState.error){
			if(!vd.vtype) vd.vtype=ℤt(true);
			vd.vtype=vd.vtype.getClassical();
		}
		vd.loc=fe.var.loc;
		fe.fescope_=fesc;
		fe.var.id=vd.getId;
		fe.loopVar=vd;
		if(vd.name.name!="_"&&!fesc.insert(vd))
			fe.sstate=vd.sstate=SemState.error;
		if(vd.sstate!=SemState.error)
			vd.sstate=SemState.completed;
		bdy=compoundExpSemantic(bdy,sc);
		assert(!!bdy);
		propErr(bdy,fe);
		static if(language==silq){
			if(sc.merge(false,fesc,state.forgetScope)){
				sc.note("possibly consumed in for loop", fe.loc);
				fe.sstate=SemState.error;
				converged=true;
			}
			if(state.forgetScope.forgottenVars.any!(d=>d.isLinear())){
				sc.error("variables potentially consumed multiple times in for loop",fe.loc);
				foreach(decl;state.forgetScope.forgottenVars.filter!(d=>d.isLinear()))
					sc.note(format("variable '%s'",decl.name),decl.loc);
				fe.sstate=SemState.error;
				converged=true;
			}
		}else sc.merge(false,fesc,state.forgetScope);
		state.endIteration(sc);
		converged|=bdy.sstate==SemState.error||state.converged;
	}
	state.fixSplitMergeGraph(sc);
	fe.bdy=bdy;
	fe.type=unit;
	if(fe.sstate!=SemState.error)
		fe.sstate=SemState.completed;
	if(fe.sstate==SemState.completed&&astopt.removeLoops)
		return lowerLoop(fe,state,sc);
	return fe;
}

Expression statementSemanticImpl(WhileExp we,Scope sc){
	Expression.CopyArgs cargs={preserveSemantic: true};
	static if(language==silq) sc.clearConsumed();
	CompoundExp bdy;
	auto state=startFixedPointIteration(sc);
	bool converged=false;
	bool condSucceeded=false;
	Expression ncond=null;
	while(!converged){ // TODO: limit number of iterations?
		state.beginIteration();
		auto prevStateSnapshot=sc.getStateSnapshot();
		bdy=we.bdy.copy(cargs);
		auto wesc=bdy.blscope_=state.makeScopes(sc);
		ncond=we.cond.copy(cargs);
		ncond=conditionSemantic(ncond,wesc,InType.no); // TODO: treat like `if cond { do { ... } until cond; }` instead.
		static if(language==silq) wesc.clearConsumed();
		propErr(ncond,we);
		condSucceeded|=ncond.sstate==SemState.completed;
		bdy=compoundExpSemantic(bdy,sc);
		propErr(bdy,we);
		if(condSucceeded&&ncond.sstate==SemState.error)
			sc.note("variable declaration may be missing in while loop body", we.loc);
		static if(language==silq){
			if(sc.merge(false,bdy.blscope_,state.forgetScope)){
				sc.note("possibly consumed in while loop", we.loc);
				we.sstate=SemState.error;
				converged=true;
			}
			if(state.forgetScope.forgottenVars.any!(d=>d.isLinear())){
				sc.error("variables potentially consumed multiple times in while loop", we.loc);
				foreach(decl;state.forgetScope.forgottenVars.filter!(d=>d.isLinear()))
					sc.note(format("variable '%s'",decl.name),decl.loc);
				we.sstate=SemState.error;
				converged=true;
			}
		}else sc.merge(false,bdy.blscope_,state.forgetScope);
		state.endIteration(sc);
		converged|=bdy.sstate==SemState.error||state.converged;
	}
	state.fixSplitMergeGraph(sc);
	auto fcond=we.cond.copy(cargs);
	fcond=conditionSemantic(fcond,sc,InType.no); // TODO: treat like `if cond { do { ... } until cond; }` instead.
	propErr(fcond,we);
	if(ncond) we.cond=ncond;
	if(bdy) we.bdy=bdy;
	we.type=isTrue(we.cond)?bottom:unit;
	if(we.sstate!=SemState.error)
		we.sstate=SemState.completed;
	if(we.sstate==SemState.completed&&astopt.removeLoops)
		return lowerLoop(we,state,sc);
	return we;
}

Expression statementSemanticImpl(RepeatExp re,Scope sc){
	auto context=expSemContext(sc,ConstResult.yes,InType.no);
	re.num=expressionSemantic(re.num,context.nestConst);
	static if(language==silq) sc.clearConsumed();
	propErr(re.num,re);
	if(re.num.sstate==SemState.completed && !isSubtype(re.num.type, ℤt(true))){
		sc.error(format("number of iterations should be a classical integer, not %s",re.num.type),re.num.loc);
		re.sstate=SemState.error;
	}
	bool converged=false;
	Expression.CopyArgs cargs={preserveSemantic: true};
	CompoundExp bdy;
	auto state=startFixedPointIteration(sc);
	while(!converged){ // TODO: limit number of iterations?
		state.beginIteration();
		bdy=re.bdy.copy(cargs);
		bdy.blscope_=state.makeScopes(sc);
		bdy=compoundExpSemantic(bdy,sc);
		propErr(bdy,re);
		static if(language==silq){
			if(sc.merge(false,bdy.blscope_,state.forgetScope)){
				sc.note("possibly consumed in repeat loop", re.loc);
				re.sstate=SemState.error;
				converged=true;
			}
			if(state.forgetScope.forgottenVars.any!(d=>d.isLinear())){
				sc.error("variables potentially consumed multiple times in repeat loop", re.loc);
				foreach(decl;state.forgetScope.forgottenVars.filter!(d=>d.isLinear()))
					sc.note(format("variable '%s'",decl.name),decl.loc);
				re.sstate=SemState.error;
				converged=true;
			}
		}else sc.merge(false,bdy.blscope_,state.forgetScope);
		state.endIteration(sc);
		converged|=bdy.sstate==SemState.error||state.converged;
	}
	state.fixSplitMergeGraph(sc);
	re.bdy=bdy;
	re.type=isPositive(re.num)&&definitelyReturns(re.bdy)?bottom:unit;
	if(re.sstate!=SemState.error)
		re.sstate=SemState.completed;
	if(re.sstate==SemState.completed&&astopt.removeLoops)
		return lowerLoop(re,state,sc);
	return re;
}

Expression statementSemanticImpl(ObserveExp oe,Scope sc){
	oe.e=conditionSemantic(oe.e,sc,InType.no);
	propErr(oe.e,oe);
	oe.type=isFalse(oe.e)?bottom:unit;
	return oe;
}

Expression statementSemanticImpl(CObserveExp oe,Scope sc){
	auto context=expSemContext(sc,ConstResult.yes,InType.no);
	oe.var=expressionSemantic(oe.var,context.nestConst);
	oe.val=expressionSemantic(oe.val,context.nestConst);
	propErr(oe.var,oe);
	propErr(oe.val,oe);
	if(oe.sstate==SemState.error)
		return oe;
	if(!oe.var.type.isSubtype(ℝ(true)) || !oe.val.type.isSubtype(ℝ(true))){
		static if(language==silq)
			sc.error("both arguments to cobserve should be classical real numbers",oe.loc);
		else sc.error("both arguments to cobserve should be real numbers",oe.loc);
		oe.sstate=SemState.error;
	}
	oe.type=unit;
	return oe;
}

Expression statementSemanticImpl(AssertExp ae,Scope sc){
	ae.e=conditionSemantic(ae.e,sc,InType.no);
	propErr(ae.e,ae);
	ae.type=isFalse(ae.e)?bottom:unit;
	return ae;
}

Expression statementSemanticImpl(ForgetExp fe,Scope sc){
	auto context=expSemContext(sc,ConstResult.yes,InType.no);
	return expressionSemantic(fe,context.nestConst);
}

Expression statementSemanticImplDefault(Expression e,Scope sc){
	auto context=expSemContext(sc,ConstResult.yes,InType.no),oe=e;
	e=expressionSemantic(e,context);
	if(e.sstate!=SemState.error){
		sc.error("not supported at this location",oe.loc);
		e.sstate=SemState.error;
	}
	return e;
}

Expression statementSemantic(Expression e,Scope sc)in{
	assert(sc.allowsLinear());
}do{
	if(e.sstate==SemState.completed) return e;
	scope(success) if(e.sstate!=SemState.error) e.sstate=SemState.completed;
	static if(language==silq){
		scope(exit){
			sc.clearConsumed();
			sc.resetConst();
		}
	}
	if(isDefineOrAssign(e)) return defineOrAssignSemantic(e,sc);
	return e.dispatchStm!(statementSemanticImpl,statementSemanticImplDefault,true)(sc);
}

CompoundExp controlledCompoundExpSemantic(CompoundExp ce,Scope sc,Expression control,Annotation restriction_)in{
	//assert(!ce.blscope_);
}do{
	static if(language==silq){
		if(control.type&&!control.type.isClassical()){
			if(!ce.blscope_) ce.blscope_=new BlockScope(sc,restriction_);
			if(control.isQfree()) ce.blscope_.addControlDependency(control.getDependency(ce.blscope_));
			else ce.blscope_.addControlDependency(Dependency(true));
		}
	}
	return compoundExpSemantic(ce,sc,restriction_);
}

CompoundExp compoundExpSemantic(CompoundExp ce,Scope sc,Annotation restriction_=Annotation.none){
	if(!ce.blscope_) ce.blscope_=new BlockScope(sc,restriction_);
	foreach(ref e;ce.s){
		//imported!"util.io".writeln("BEFORE: ",e," ",typeid(e)," ",e.sstate," ",ce.blscope_.getStateSnapshot());
		e=statementSemantic(e,ce.blscope_);
		//imported!"util.io".	writeln("AFTER: ",e," ",typeid(e)," ",e.sstate," ",ce.blscope_.getStateSnapshot());
		propErr(e,ce);
	}
	ce.type=definitelyReturns(ce)?bottom:unit;
	if(ce.sstate!=SemState.error)
		ce.sstate=SemState.completed;
	return ce;
}

VarDecl varDeclSemantic(VarDecl vd,Scope sc){
	bool success=true;
	if(!vd.scope_) makeDeclaration(vd,success,sc);
	vd.type=unit;
	if(!success) vd.sstate=SemState.error;
	if(!vd.vtype){
		assert(vd.dtype,text(vd));
		vd.vtype=typeSemantic(vd.dtype,sc);
	}
	if(!vd.vtype) vd.sstate=SemState.error;
	if(vd.sstate!=SemState.error)
		vd.sstate=SemState.completed;
	return vd;
}

static if(language==silq){
Dependency getDependency(Expression e,Scope sc)in{
	assert(e.isQfree());
}do{
	auto result=Dependency(false);
	foreach(id;e.freeIdentifiers){
		if(id.type&&!id.type.isClassical){
			if(id.meaning){
				auto decl=id.meaning;
				while(decl&&decl.splitFrom&&decl.scope_&&decl.scope_.getFunction()!=sc.getFunction())
					decl=decl.splitFrom;
				if(!sc.dependencyTracked(decl))
					sc.addDefaultDependency(decl); // TODO: ideally can be removed
				result.dependencies.insert(decl);
				if(!id.constLookup||id.byRef){
					/+auto vd=cast(VarDecl)id.meaning;
					 if(!vd||!(vd.typeConstBlocker||sc.isConst(vd)))+/
					result.replace(decl,sc.getDependency(decl));
				}
			}
		}
	}
	return result;
}

bool consumes(Expression e){
	if(!e.constLookup&&cast(Identifier)e&&(!e.type||!e.type.isClassical())) return true;
	foreach(c;e.components)
		if(c.consumes())
			return true;
	return false;
}
bool isLifted(Expression e,Scope sc){
	if(e.isQfree()){
		if(!consumes(e)) return true;
		if(astopt.allowUnsafeCaptureConst && !e.getDependency(sc).isTop) return true;
	}
	return false;
}
}
bool isLiftedBuiltIn(Expression e){ // TODO: implement in terms of dispatchExp?
	if(cast(AddExp)e||cast(SubExp)e||cast(NSubExp)e||cast(MulExp)e||cast(DivExp)e||cast(IDivExp)e||cast(ModExp)e||cast(PowExp)e||cast(BitOrExp)e||cast(BitXorExp)e||cast(BitAndExp)e||cast(UMinusExp)e||cast(UNotExp)e||cast(UBitNotExp)e||cast(AndExp)e||cast(OrExp)e||cast(LtExp)e||cast(LeExp)e||cast(GtExp)e||cast(GeExp)e||cast(EqExp)e||cast(NeqExp)e||cast(AssertExp)e)
		return true;
	if(cast(LiteralExp)e) return true;
	if(cast(SliceExp)e) return true;
	if(auto tae=cast(TypeAnnotationExp)e)
		return isLiftedBuiltIn(tae.e);
	return false;
}

struct DefineLhsContext{
	ExpSemContext expSem;
	@property sc(){ return expSem.sc; }
	@property constResult(){ return expSem.constResult; }
	@property inType(){ return expSem.inType; }
	static if(language==silq)
	Id nameIndex(IndexExp index){
		auto name=freshName();
		sc.nameIndex(index,name);
		return name;
	}
	Expression type;
	Expression initializer;
}
auto defineLhsContext(ExpSemContext expSem,Expression type,Expression initializer){
	return DefineLhsContext(expSem,type,initializer);
}
auto nest(DefineLhsContext context,ConstResult newConstResult,Expression newType,Expression newInitializer){
	return defineLhsContext(context.expSem.nest(newConstResult),context.tupleof[1..$-2],newType,newInitializer);
}
auto nestConst(ref DefineLhsContext context,Expression newType,Expression newInitializer){
	return context.nest(ConstResult.yes,newType,newInitializer);
}
auto nestConsumed(ref DefineLhsContext context,Expression newType,Expression newInitializer){
	return context.nest(ConstResult.no,newType,newInitializer);
}

template defineLhsSemanticImpls(bool isPresemantic){
Expression defineLhsSemanticImpl(CompoundDecl cd,DefineLhsContext context){
	return defineLhsSemanticImplDefault(cd,context); // TODO: get rid of this case
}
Expression defineLhsSemanticImpl(CompoundExp ce,DefineLhsContext context){
	return defineLhsSemanticImplDefault(ce,context); // TODO: get rid of this case?
}
Expression defineLhsSemanticImpl(CommaExp ce,DefineLhsContext context){
	return defineLhsSemanticImplDefault(ce,context); // TODO: get rid of this case?
}

Expression defineLhsSemanticImpl(IteExp ite,DefineLhsContext context){
	return defineLhsSemanticImplCurrentlyUnsupported(ite,context);
}

Expression defineLhsSemanticImpl(AssertExp ae,DefineLhsContext context){
	return defineLhsSemanticImplLifted(ae,context);
}

Expression defineLhsSemanticImpl(LiteralExp lit,DefineLhsContext context){
	return defineLhsSemanticImplLifted(lit,context);
}
Expression defineLhsSemanticImpl(LambdaExp le,DefineLhsContext context){
	return defineLhsSemanticImplUnsupported(le,context);
}

Expression defineLhsSemanticImpl(FunctionDef fd,DefineLhsContext context){
	return defineLhsSemanticImplDefault(fd,context); // TODO: get rid of this case
}
Expression defineLhsSemanticImpl(ReturnExp re,DefineLhsContext context){
	return defineLhsSemanticImplDefault(re,context); // TODO: get rid of this case
}
static if(language==silq)
Expression defineLhsSemanticImpl(CallExp ce,DefineLhsContext context){
	auto result=callSemantic!isPresemantic(ce,context);
	static if(!isPresemantic){ // TODO: move into callSemantic!(false,DefineLhsContext)?
		auto sc=context.sc;
		assert(util.among(ce.e.sstate,SemState.error,SemState.completed));
		bool ok=true;
		if(ce.sstate!=SemState.error){
			auto f=ce.e,ft=cast(ProductTy)f.type;
			if(ft){
				if(ft.annotation<Annotation.mfree){
					sc.error("reversed function must be 'mfree'",f.loc);
					ok=false;
				}
				if(!ft.isClassical_){
					sc.error("reversed function must be classical",f.loc);
					ok=false;
				}
				if(ft.cod.hasAnyFreeVar(ft.names)){
					sc.error("arguments to reversed function call cannot appear in result type",f.loc);
					ok=false;
				}else{
					ce.type=ft.cod;
					if(context.type&&!isSubtype(context.type,ce.type)){
						if(!joinTypes(context.type,ce.type)||!meetTypes(context.type,ce.type)){
							sc.error(format("cannot call reversed function with return type '%s' with a result type of '%s'",ce.type,context.type),ce.loc);
							ok=false;
						}
						auto nresult=new TypeAnnotationExp(result,context.type,TypeAnnotationType.coercion);
						nresult.loc=result.loc;
						nresult.type=context.type;
						nresult.sstate=SemState.completed;
						result=nresult;
					}
				}
			}
		}
	}
	static if(!isPresemantic) if(!ok){
		result.sstate=SemState.error;
		foreach(e;result.subexpressions()){
			if(auto id=cast(Identifier)e){
				if(!id.constLookup){
					if(id.meaning&&id.meaning.sstate!=SemState.completed)
						id.meaning.sstate=SemState.error;
				}
			}
		}
	}
	return result;
}

static if(language==psi)
Expression defineLhsSemanticImpl(CallExp ce,DefineLhsContext context){
	return defineLhsSemanticImplDefault(ce,context);
}

static if(language==psi)
Expression defineLhsSemanticImpl(PlaceholderExp pl,DefineLhsContext context){
	return defineLhsSemanticImplCurrentlyUnsupported(pl,context);
}

Expression defineLhsSemanticImpl(ForgetExp fe,DefineLhsContext context){
	static if(isPresemantic){
		fe.type=unit;
	}else{
		if(context.type&&fe.type&&!isSubtype(context.type,fe.type)){
			context.sc.error(format("cannot assign '%s' to '%s'",context.type,fe.type),fe.loc);
			fe.sstate=SemState.error;
		}
	}
	return fe;
}
Expression defineLhsSemanticImpl(Identifier id,DefineLhsContext context){
	if(!isPresemantic){
		if(id.sstate!=SemState.error)
		if(auto vd=cast(VarDecl)id.meaning){
			if(context.type){
				if(vd.vtype){
					if(auto nt=joinTypes(vd.vtype,context.type)){
						vd.vtype=nt;
					}else{
						context.sc.error(format("incompatible types '%s' and '%s' for variable '%s'",vd.vtype,context.type),id.loc);
						id.sstate=SemState.error;
					}
				}else vd.vtype=context.type;
			}else id.sstate=SemState.error;
			if(context.initializer){
				assert(!vd.initializer);
				vd.initializer=context.initializer;
			}
		}
		if(id.meaning){
			propErr(id,id.meaning);
			propErr(id.meaning,id);
		}
		if(context.type){
			id.type=context.type;
		}else{
			context.sc.error(format("cannot determine type for '%s",id),id.loc);
			id.sstate=SemState.error;
		}
	}
	return id;
}
Expression defineLhsSemanticImpl(FieldExp fe,DefineLhsContext context){
	// TODO: add new fields to records?
	return defineLhsSemanticImplUnsupported(fe,context);
}

static if(language==silq){
Expression defineLhsSemanticImpl(IndexExp idx,DefineLhsContext context){
	assert(!context.constResult);
	Expression analyzeAggregate(IndexExp e,DefineLhsContext context){
		auto next=unwrap(e.e);
		propErr(next,e);
		propErr(e,idx);
		if(e.sstate==SemState.error)
			return e;
		if(auto id=cast(Identifier)next){
			id.byRef=true;
			id.indexedDirectly=true;
			id.scope_=context.sc;
			if(!id.meaning) id.meaning=lookupMeaning(id,Lookup.probingWithCapture,context.sc);
			propErr(next,e);
			if(id.meaning){
				id.meaning=context.sc.split(id.meaning);
				if(id.meaning.rename) id.id=id.meaning.rename.id;
				id.type=id.typeFromMeaning;
				if(auto ft=cast(FunTy)id.type){
					auto ce=new CallExp(id,e.a,true,false);
					ce.loc=e.loc;
					if(context.constResult) return callSemantic(ce,context.expSem);
					else return callSemantic!isPresemantic(ce,context);
				}
			}else{
				context.sc.error(format("undefined identifier %s",id.name),id.loc);
				id.sstate=SemState.error;
				e.e.sstate=SemState.error;
				idx.sstate=SemState.error;
				return idx;
			}
		}
		if(auto idx=cast(IndexExp)next){
			if(auto r=analyzeAggregate(idx,context.nestConst(null,null))){
				e.e=r;
				propErr(e.e,e);
				return e;
			}
		}
		if(next!is e.e) propErr(next,e.e);
		propErr(next,e);
		return null;
	}
	if(auto r=analyzeAggregate(idx,context))
		if(idx.sstate==SemState.error||!cast(IndexExp)unwrap(r))
			return r;
	auto sc=context.sc;
	void analyzeIndex(IndexExp e){
		if(auto idx=cast(IndexExp)unwrap(e.e)){
			analyzeIndex(idx);
			propErr(idx,e);
		}
		e.a=expressionSemantic(e.a,context.expSem.nestConst);
		propErr(e.a,e);
		propErr(e.a,idx);
		if(e.a.sstate==SemState.completed){
			if(e.a.type&&!isBasicIndexType(e.a.type)){
				sc.error(format("index for component replacement must be integer, not '%s'",e.a.type),e.a.loc);
				idx.sstate=SemState.error;
			}
			if(!e.a.isLifted(sc)){
				sc.error("index for component replacement must be 'lifted'",e.a.loc);
				static if(language==silq) sc.clearConsumed();
				idx.sstate=SemState.error;
			}
		}
	}
	analyzeIndex(idx);
	if(idx.byRef){
		auto result=expressionSemantic(idx,context.expSem);
		static if(!isPresemantic){
			if(result.sstate==SemState.completed&&context.type){
				assert(!!result.type);
				bool ok=true;
				if(auto id=getIdFromIndex(idx)){
					if(auto nt=updatedType(id,idx,context.type)){
						if(auto vd=cast(VarDecl)id.meaning)
							vd.vtype=nt;
					}else ok=false;
				}else if(!joinTypes(context.type,result.type)){
					ok=false;
				}
				if(!ok){
					context.sc.error(format("cannot assign '%s' to '%s'",context.type,result.type),result.loc);
					result.sstate=SemState.error;
				}
			}
		}
		return result;
	}
	bool checkReplaceable(IndexExp e){
		if(auto id=cast(Identifier)unwrap(e.e)){
			if(id.meaning){
				auto r=checkAssignable(id.meaning,idx.e.loc,sc,true,true);
				if(!r) id.meaning.sstate=SemState.error;
				return r;
			}
			assert(id.sstate==SemState.error);
			return true; // TODO: ok?
		}
		if(auto idx2=cast(IndexExp)unwrap(e.e)) return checkReplaceable(idx2);
		static if(isPresemantic){
			context.sc.error("not supported at this location",unwrap(e.e).loc);
			unwrap(e.e).sstate=SemState.error;
			e.e.sstate=SemState.error;
		}else assert(e.e.sstate==SemState.error);
		return false;
	}
	if(!checkReplaceable(idx)){
		idx.sstate=SemState.error;
		return idx;
	}
	// TODO: determine type?
	auto name=context.nameIndex(idx);
	auto id=new Identifier(name); // TODO: subclass Identifier and give it the original IndexExp?
	id.loc=idx.loc;
	return id;
}
}else{ // language!=silq
Expression defineLhsSemanticImpl(IndexExp idx,DefineLhsContext context){
	return defineLhsSemanticImplDefault(idx,context);
}
}
Expression defineLhsSemanticImpl(SliceExp slc,DefineLhsContext context){
	// return defineLhsSemanticImplLifted(slc,context);
	// maybe we will want to support slice replacement
	return defineLhsSemanticImplCurrentlyUnsupported(slc,context);
}
Expression defineLhsSemanticImpl(TupleExp tpl,DefineLhsContext context){
	auto at=cast(ArrayTy)context.type;
	// auto vt=cast(VectorTy)context.type; // TODO
	auto tt=!at&&context.type?context.type.isTupleTy:null;
	Expression[] es=[];
	if(auto te=cast(TupleExp)context.initializer) es=te.e;
	if(auto ve=cast(VectorExp)context.initializer) es=ve.e;
	bool isBottom=context.type&&isEmpty(context.type);
	foreach(i,ref e;tpl.e){
		auto ttype=at?at.next:tt&&i<tt.length?tt[i]:isBottom?bottom:null;
		auto ninit=i<es.length?es[i]:null;
		e=defineLhsSemantic!isPresemantic(e,context.nest(context.constResult,ttype,ninit));
		propErr(e,tpl);
	}
	static if(!isPresemantic){
		auto sc=context.sc;
		if(context.type){
			if(tt){
				if(tpl.length!=tt.length){
					sc.error(text("inconsistent number of tuple entries for definition: ",tpl.length," vs. ",tt.length),tpl.loc);
					tpl.sstate=SemState.error;
				}
			}else if(!at&&!isBottom){
				sc.error(format("cannot unpack type %s as a tuple",context.type),tpl.loc);
				tpl.sstate=SemState.error;
			}
		}else tpl.sstate=SemState.error; // TODO: ok?
		if(isBottom) tpl.type=bottom;
		else if(tpl.e.all!(e=>!!e.type))
			tpl.type=tupleTy(tpl.e.map!(e=>e.type).array);
	}
	return tpl;
}
Expression defineLhsSemanticImpl(VectorExp vec,DefineLhsContext context){
	// TODO: do we even keep this?
	auto at=cast(ArrayTy)context.type;
	auto vt=cast(VectorTy)context.type;
	auto tt=!at&&!vt&&context.type?context.type.isTupleTy:null;
	foreach(i,ref e;vec.e){
		auto ttype=at?at.next:vt?vt.next:tt&&i<tt.length?tt[i]:null;
		e=defineLhsSemantic!isPresemantic(e,context);
		propErr(e,vec);
	}
	static if(!isPresemantic){
		auto sc=context.sc;
		if(context.type){
			if(tt){
				if(vec.e.length!=tt.length){
					sc.error(text("inconsistent number of vector entries for definition: ",vec.e.length," vs. ",tt.length),vec.loc);
					vec.sstate=SemState.error;
				}
			}else if(vt){
				// TODO: technically this violates type refinement
				auto lit=LiteralExp.makeInteger(vec.e.length);
				Expression neq=new NeqExp(lit,vt.num);
				neq=expressionSemantic(neq,context.expSem.nestConst);
				assert(neq.sstate==SemState.completed);
				if(neq.eval()==LiteralExp.makeBoolean(1)){
					sc.error(text("inconsistent number of vector entries for definition: ",vec.e.length," vs. ",vt.num.eval),vec.loc);
					vec.sstate=SemState.error;
				}
			}else if(!at){
				sc.error(format("cannot unpack type %s as a vector",context.type),vec.loc);
				vec.sstate=SemState.error;
			}
		}else vec.sstate=SemState.error; // TODO: ok?
		if(vec.e.all!(e=>!!e.type)){
			Expression t=null;
			foreach(e;vec.e){
				t=joinTypes(t,e.type);
				if(!t) break;
			}
			if(t) vec.type=vectorTy(t,LiteralExp.makeInteger(vec.e.length));
			else if(vec.e.length) vec.type=tupleTy(vec.e.map!(e=>e.type).array);
			else vec.type=vectorTy(bottom,LiteralExp.makeInteger(0));
		}
	}
	return vec;
}

Expression defineLhsSemanticImpl(TypeAnnotationExp tae,DefineLhsContext context){
	auto sc=context.sc;
	static if(!isPresemantic){
		if(context.type){
			if(auto r=resolveWildcards(tae.t,context.type))
				tae.t=r;
		}
		tae.type=typeSemantic(tae.t,context.sc);
		if(tae.type) tae.t=tae.type;
	}
	tae.e=defineLhsSemantic!isPresemantic(tae.e,context.nest(context.constResult,tae.type,context.initializer));
	static if(!isPresemantic){
		return expressionSemantic(tae,context.expSem);
	}else return tae;
	// TODO: need to do anything else?
}

Expression defineLhsSemanticImpl(UMinusExp ume,DefineLhsContext context){
	return defineLhsSemanticImplLifted(ume,context);
}
Expression defineLhsSemanticImpl(UNotExp une,DefineLhsContext context){
	return defineLhsSemanticImplLifted(une,context);
}
Expression defineLhsSemanticImpl(UBitNotExp ubne,DefineLhsContext context){
	return defineLhsSemanticImplLifted(ubne,context);
}

static if(language==silq)
Expression defineLhsSemanticImpl(UnaryExp!(Tok!"const") ce,DefineLhsContext context){
	return defineLhsSemanticImplDefault(ce,context);
}
static if(language==silq)
Expression defineLhsSemanticImpl(UnaryExp!(Tok!"moved") ce,DefineLhsContext context){
	return defineLhsSemanticImplDefault(ce,context);
}

Expression defineLhsSemanticImpl(AddExp ae,DefineLhsContext context){
	return defineLhsSemanticImplLifted(ae,context);
}
Expression defineLhsSemanticImpl(SubExp se,DefineLhsContext context){
	return defineLhsSemanticImplLifted(se,context);
}
Expression defineLhsSemanticImpl(NSubExp nse,DefineLhsContext context){
	return defineLhsSemanticImplLifted(nse,context);
}
Expression defineLhsSemanticImpl(MulExp me,DefineLhsContext context){
	return defineLhsSemanticImplLifted(me,context);
}
Expression defineLhsSemanticImpl(DivExp de,DefineLhsContext context){
	return defineLhsSemanticImplLifted(de,context);
}
Expression defineLhsSemanticImpl(IDivExp ide,DefineLhsContext context){
	return defineLhsSemanticImplLifted(ide,context);
}
Expression defineLhsSemanticImpl(ModExp me,DefineLhsContext context){
	return defineLhsSemanticImplLifted(me,context);
}
Expression defineLhsSemanticImpl(PowExp pe,DefineLhsContext context){
	return defineLhsSemanticImplLifted(pe,context);
}
Expression defineLhsSemanticImpl(BitOrExp boe,DefineLhsContext context){
	return defineLhsSemanticImplLifted(boe,context);
}
Expression defineLhsSemanticImpl(BitXorExp bxe,DefineLhsContext context){
	return defineLhsSemanticImplLifted(bxe,context);
}
Expression defineLhsSemanticImpl(BitAndExp bae,DefineLhsContext context){
	return defineLhsSemanticImplLifted(bae,context);
}

Expression defineLhsSemanticImpl(AndExp ae,DefineLhsContext context){
	return defineLhsSemanticImplLifted(ae,context);
}
Expression defineLhsSemanticImpl(OrExp oe,DefineLhsContext context){
	return defineLhsSemanticImplLifted(oe,context);
}

Expression defineLhsSemanticImpl(LtExp le,DefineLhsContext context){
	return defineLhsSemanticImplLifted(le,context);
}
Expression defineLhsSemanticImpl(LeExp le,DefineLhsContext context){
	return defineLhsSemanticImplLifted(le,context);
}
Expression defineLhsSemanticImpl(GtExp ge,DefineLhsContext context){
	return defineLhsSemanticImplLifted(ge,context);
}
Expression defineLhsSemanticImpl(GeExp ge,DefineLhsContext context){
	return defineLhsSemanticImplLifted(ge,context);
}
Expression defineLhsSemanticImpl(EqExp eq,DefineLhsContext context){
	return defineLhsSemanticImplLifted(eq,context);
}
Expression defineLhsSemanticImpl(NeqExp neq,DefineLhsContext context){
	return defineLhsSemanticImplLifted(neq,context);
}

Expression defineLhsSemanticImpl(CatExp ce,DefineLhsContext context){
	auto sc=context.sc;
	auto l1=knownLength(ce.e1,true),l2=knownLength(ce.e2,true);
	static if(!isPresemantic){
		Expression ntype1=null,ntype2=null;
		if(!l1&&!l2||!context.type){
			return defineLhsSemanticImplCurrentlyUnsupported(ce,context);
		}
		if(l1){
			l1=expressionSemantic(l1,context.expSem.nestConst);
			propErr(l1,ce);
		}
		if(l2){
			l2=expressionSemantic(l2,context.expSem.nestConst);
			propErr(l2,ce);
		}
		if(context.type&&
		   (!l1||l1.sstate==SemState.completed||l1.type&&isSubtype(l1.type,ℕt(true)))&&
		   (!l2||l2.sstate==SemState.completed&&l2.type&&isSubtype(l2.type,ℕt(true)))
		){
			if(auto vt=cast(VectorTy)context.type){
				if(l1){
					if(!l2){
						auto sub=new NSubExp(vt.num,l1);
						sub.loc=l1.loc;
						sub.type=ℕt(true);
						sub.sstate=SemState.completed;
						ntype2=vectorTy(vt.next,sub);
					}
					ntype1=vectorTy(vt.next,l1);
				}
				if(l2){
					if(!l1){
						auto sub=new NSubExp(vt.num,l2);
						sub.loc=l2.loc;
						sub.type=ℕt(true);
						sub.sstate=SemState.completed;
						ntype1=vectorTy(vt.next,sub);
					}
					ntype2=vectorTy(vt.next,l2);
				}
			}else if(auto at=cast(ArrayTy)context.type){
				ntype1=ntype2=context.type;
				if(l1) ntype1=vectorTy(at.next,l1);
				if(l2) ntype2=vectorTy(at.next,l2);
			}else if(auto tt=context.type.isTupleTy){
				size_t mid;
				bool ok=false;
				if(!ok&&l1){
					if(auto x=l1.eval().asIntegerConstant()){
						ok=true;
						try mid=min(x.get.to!size_t,tt.length);
						catch(Exception) ok=false;
					}
				}
				if(!ok&&l2){
					if(auto x=l2.eval().asIntegerConstant()){
						ok=true;
						try mid=tt.length-min(x.get.to!size_t,tt.length);
						catch(Exception) ok=false;
					}
				}
				if(ok){
					assert(mid<=tt.length);
					ntype1=tupleTy(iota(0,mid).map!(i=>tt[i]).array);
					ntype2=tupleTy(iota(mid,tt.length).map!(i=>tt[i]).array);
				}else if(l1||l2){
					Expression elemTy=null;
					foreach(i;0..tt.length){
						elemTy=joinTypes(elemTy, tt[i]);
						if(!elemTy) break;
					}
					if(elemTy){
						if(l1) ntype1=vectorTy(elemTy,l1);
						if(l2) ntype2=vectorTy(elemTy,l2);
					}
				}
			}
		}
		//imported!"util.io".writeln("!! ",ce," ",ntype1," ",ntype2," ",l1," ",l2," ",context.type);
	}else auto ntype1=null,ntype2=null;
	Expression ninit1=null,ninit2=null;
	if(context.initializer&&context.initializer.sstate==SemState.completed){
		assert(!!context.initializer.type);
		bool isTupleExp=false,isVectorExp=false;
		Expression[] es;
		if(auto te=cast(TupleExp)context.initializer){
			es=te.e;
			isTupleExp=true;
		}
		if(auto ve=cast(VectorExp)context.initializer){
			es=ve.e;
			isVectorExp=true;
		}
		if(isTupleExp||isVectorExp){
			bool ok=false;
			size_t mid;
			if(!ok&&l1){
				if(auto x=l1.eval().asIntegerConstant()){
					ok=true;
					try mid=min(x.get.to!size_t,es.length);
					catch(Exception) ok=false;
				}
			}
			if(!ok&&l2){
				if(auto x=l2.eval().asIntegerConstant()){
					ok=true;
					try mid=es.length-min(x.get.to!size_t,es.length);
					catch(Exception) ok=false;
				}
			}
			if(ok){
				ninit1=expressionSemantic(isTupleExp?new TupleExp(es[0..mid]):new VectorExp(es[0..mid]),context.expSem);
				ninit2=expressionSemantic(isTupleExp?new TupleExp(es[mid..$]):new VectorExp(es[mid..$]),context.expSem);
			}
		}
	}
	auto ncontext1=context.nest(context.constResult,ntype1,ninit1);
	auto ncontext2=context.nest(context.constResult,ntype2,ninit2);
	ce.e1=defineLhsSemantic!isPresemantic(ce.e1,ncontext1);
	propErr(ce.e1,ce);
	ce.e2=defineLhsSemantic!isPresemantic(ce.e2,ncontext2);
	propErr(ce.e2,ce);
	static if(!isPresemantic){
		ce.type=ce.e1.type&&ce.e2.type?concatType(ce.e1.type.eval(),ce.e2.type.eval()):null;
		if(!ce.type){
			if(ce.e1.type&&ce.e2.type)
				sc.error(format("incompatible types %s and %s for ~",ce.e1.type,ce.e2.type),ce.loc);
			ce.sstate=SemState.error;
		}else if(context.type&&!isSubtype(context.type,ce.type)){
			if(!joinTypes(context.type,ce.type)||!meetTypes(context.type,ce.type)){ // TODO: ok?
				sc.error(format("incompatible types for split: '%s' vs '%s",ce.type,context.type),ce.loc);
				ce.sstate=SemState.error;
			}
		}
	}
	return ce;
}

Expression defineLhsSemanticImpl(WildcardExp e,DefineLhsContext context){
	e.type=context.type;
	e.sstate=SemState.completed;
	return e;
}

Expression defineLhsSemanticImpl(TypeofExp ty,DefineLhsContext context){
	return defineLhsSemanticImplDefault(ty,context);
}
Expression defineLhsSemanticImpl(BinaryExp!(Tok!"×") pr,DefineLhsContext context){
	return defineLhsSemanticImplDefault(pr,context);
}
Expression defineLhsSemanticImpl(BinaryExp!(Tok!"→") ex,DefineLhsContext context){
	return defineLhsSemanticImplDefault(ex,context);
}
Expression defineLhsSemanticImpl(RawProductTy fa,DefineLhsContext context){
	return defineLhsSemanticImplDefault(fa,context);
}
Expression defineLhsSemanticImpl(RawVariadicTy va,DefineLhsContext context){
	return defineLhsSemanticImplDefault(va,context);
}


Expression defineLhsSemanticImplLifted(Expression e,DefineLhsContext context){
	auto result=expressionSemantic(e,context.expSem);
	static if(!isPresemantic){
		if(context.type&&result.type){
			if(!joinTypes(context.type,result.type)){ // TODO: generate coerce expression instead?
				context.sc.error(format("'lifted' expression of type '%s' incompatible with right-hand side type '%s'",result.type,context.type),result.loc);
				result.sstate=SemState.error;
			}
		}
	}
	return result;
}

Expression defineLhsSemanticImplCurrentlyUnsupported(Expression e,DefineLhsContext context){
	auto sc=context.sc;
	if(context.type&&context.type==bottom){
		auto lit=LiteralExp.makeBoolean(false);
		lit.loc=e.loc;
		auto r=new AssertExp(lit); // TODO: detect and error out if this makes it past type checking?
		r.loc=e.loc;
		return defineLhsSemantic!isPresemantic(r,context);
	}
	if(e.sstate!=SemState.error){
		sc.error("currently not supported as definition left-hand side",e.loc);
		e.sstate=SemState.error;
	}
	return e;
}
Expression defineLhsSemanticImplUnsupported(Expression e,DefineLhsContext context){
	auto sc=context.sc;
	if(e.sstate!=SemState.error){
		sc.error("not supported as definition left-hand side",e.loc);
		e.sstate=SemState.error;
	}
	return e;
}

Expression defineLhsSemanticImplDefault(Expression e,DefineLhsContext context){
	return defineLhsSemanticImplUnsupported(e,context);
}

}

alias defineLhsSemanticImpl(bool isPresemantic)=defineLhsSemanticImpls!isPresemantic.defineLhsSemanticImpl;
alias defineLhsSemanticImplDefault(bool isPresemantic)=defineLhsSemanticImpls!isPresemantic.defineLhsSemanticImplDefault;


Expression defineLhsSemantic(bool isPresemantic=false)(Expression lhs,DefineLhsContext context){
	Expression r;
	static if(!isPresemantic) scope(success){
		assert(!!r);
		if(r.sstate!=SemState.error){
			assert(!!r.type);
			r.sstate=SemState.completed;
			r.constLookup=context.constResult;
		}
	}
	if(context.constResult) return r=expressionSemantic(lhs,context.expSem);
	return r=dispatchExp!(defineLhsSemanticImpl!isPresemantic,defineLhsSemanticImplDefault!isPresemantic,true)(lhs,context);
}

Expression defineLhsPresemantic(Expression lhs,DefineLhsContext context){
	return defineLhsSemantic!true(lhs,context);
}

static if(language==silq)
Expression swapSemantic(DefineExp be,Scope sc){
	bool isSwap=false;
	auto tpl1=cast(TupleExp)unwrap(be.e1);
	auto tpl2=cast(TupleExp)unwrap(be.e2);
	if(!tpl1||!tpl2) return null;
	if(tpl1.length!=2||tpl2.length!=2) return null;
	IndexExp[2] idx1=[cast(IndexExp)tpl1.e[0],cast(IndexExp)tpl1.e[1]];
	IndexExp[2] idx2=[cast(IndexExp)tpl2.e[0],cast(IndexExp)tpl2.e[1]];
	if(!idx1[0]||!idx1[1]||!idx2[0]||!idx2[1]) return null;
	if(!getIdFromIndex(idx1[0])||!getIdFromIndex(idx1[1])||!getIdFromIndex(idx2[0])||!getIdFromIndex(idx2[1]))
		return null;
	auto preState=sc.getStateSnapshot(true);
	foreach(i;0..2){
		if(!guaranteedSameLocations(idx1[i],idx2[$-1-i],be.loc,sc,InType.no)){
			sc.restoreStateSnapshot(preState);
			return null;
		}
	}
	if(guaranteedDifferentLocations(idx2[0],idx2[1],be.loc,sc,InType.no)){
		sc.restoreStateSnapshot(preState);
		return null;
	}
	be.isSwap=true;
	foreach(idx;chain(idx1[],idx2[])) idx.byRef=true;
	auto econtext=expSemContext(sc,ConstResult.no,InType.no);
	auto id=getIdFromIndex(idx2[0]);
	assert(!!id);
	id.byRef=true;
	id.meaning=lookupMeaning(id,Lookup.probingWithCapture,sc);
	if(id.meaning) id.meaning=sc.split(id.meaning);
	propErr(id,be.e2);
	be.e2=expressionSemantic(be.e2,econtext);
	propErr(be.e2,be);
	if(be.sstate!=SemState.error){
		ArrayConsumer consumer;
		//imported!"util.io".writeln("!!! ",idx2[0]," ",idx2[0].sstate);
		Expression.CopyArgs cargs={ preserveMeanings: true };
		consumer.consumeArray(idx2[0].copy(),econtext);
		consumer.redefineArrays(be.loc,sc);
	}
	be.e1=defineLhsSemantic(be.e1,DefineLhsContext(econtext,be.e2.type,be.e2));
	propErr(be.e1,be);
	if(be.sstate!=SemState.error) be.sstate=SemState.completed;
	return be;
}

bool prepareIndexReplacements(ref Expression lhs,Scope sc,ref CompoundExp[] prologues,ref CompoundExp[] epilogues,Location loc){
	auto econtext=expSemContext(sc,ConstResult.no,InType.no);
	auto dcontext=defineLhsContext(econtext,null,null);
	auto creplsCtx=sc.moveLocalComponentReplacements(); // TODO: get rid of this
	lhs=defineLhsPresemantic(lhs,dcontext);
	//writeln("{",indicesToReplace.map!(x=>text(x[0]?x[0].toString:"null",",",x[1],",",x[2]?x[2].toString():"null")).join(";"),"}");
	auto creplss=sc.localComponentReplacementsByDecl();
	if(!creplss.length){
		sc.restoreLocalComponentReplacements(creplsCtx); // TODO: get rid of this
		return false;
	}
	if(astopt.splitComponents)
		creplss=unnestComponentReplacements(creplss,loc,sc);
	foreach(crepls;creplss){
		assert(crepls.length);
		Expression[] reads;
		foreach(ref crepl;crepls){
			if(!crepl.write) continue;
			auto id=new Identifier(crepl.name);
			id.loc=loc;
			id.byRef=true;
			auto idx=crepl.write.copy();
			idx.loc=crepl.write.loc;
			idx.byRef=true;
			if(auto cid=getIdFromIndex(idx))
				cid.byRef=true;
			auto read=new BinaryExp!(Tok!":=")(id,moveExp(idx));
			read.loc=crepl.write.loc;
			reads~=read;
		}
		auto creplsCtx2=sc.moveLocalComponentReplacements(); // TODO: get rid of this
		auto prologue=new CompoundExp(reads);
		prologue.loc=loc;
		prologue=statementSemanticImpl(prologue,sc);
		if(prologue.sstate!=SemState.error) prologue.sstate=SemState.completed;
		prologues~=prologue;
		sc.restoreLocalComponentReplacements(creplsCtx2); // TODO: get rid of this
		prologue.loc=loc;
		Expression[] writes;
		foreach_reverse(ref crepl;crepls){
			if(!crepl.write) continue;
			auto id=new Identifier(crepl.name);
			id.loc=loc;
			id.byRef=true;
			auto idx=crepl.write.copy();
			idx.loc=crepl.write.loc;
			idx.byRef=true;
			if(auto cid=getIdFromIndex(idx))
				cid.byRef=true;
			auto write=new BinaryExp!(Tok!":=")(moveExp(idx),id);
			write.loc=crepl.write.loc;
			writes~=write;
		}
		auto epilogue=new CompoundExp(writes);
		epilogue.loc=loc;
		epilogues~=epilogue;
	}
	return true;
}

Expression lowerIndexReplacement(CompoundExp[] prologues,CompoundExp[] epilogues,Expression r,Scope sc){
	static if(language==silq) sc.clearConsumed();
	if(!prologues.length||!epilogues.length) return r;
	assert(prologues.length==epilogues.length);
	assert(prologues.all!(prologue=>util.among(prologue.sstate,SemState.completed,SemState.error)));
	assert(r&&util.among(r.sstate,SemState.completed,SemState.error));
	Expression current=r;
	foreach_reverse(eplg;epilogues){
		eplg=statementSemanticImpl(eplg,sc);
		if(eplg.sstate!=SemState.error) eplg.sstate=SemState.completed;
	}
	foreach_reverse(prlg,eplg;zip(prologues,epilogues)){
		auto prev=cast(CompoundExp)current;
		if(!prev){
			prev=new CompoundExp([current]);
			prev.loc=current.loc;
			prev.type=unit;
			prev.sstate=SemState.completed;
			propErr(current,prev);
		}
		auto with_=new WithExp(prlg,prev);
		with_.itrans=eplg;
		with_.loc=r.loc;
		with_.isIndices=true;
		with_.type=unit;
		with_.sstate=SemState.completed;
		propErr(prlg,with_);
		propErr(prev,with_);
		propErr(eplg,with_);
		current=with_;
	}
	//imported!"util.io".writeln(current);
	return current;
}

Expression defineSemantic(DefineExp be,Scope sc){
	auto econtext=expSemContext(sc,ConstResult.no,InType.no);
	CompoundExp[] prologues,epilogues;
	static if(language==silq)
	if(sc.allowsLinear){
		if(auto r=swapSemantic(be,sc)) return r;
		prepareIndexReplacements(be.e1,sc,prologues,epilogues,be.loc);
	}
	propErr(be.e1,be);
	static if(language==psi){ // TODO: remove this?
		if(auto ce=cast(CallExp)be.e2){
			if(auto id=cast(Identifier)ce.e){
				if(id.name=="array" && !ce.isSquare){
					ce.arg=expressionSemantic(ce.arg,expSemContext(sc,ConstResult.yes,InType.no));
					if(isSubtype(ce.arg.type,ℕt)){
						ce.e.type=funTy(ℝ,arrayTy(ℝ),false,false,Annotation.pure_,true);
						ce.e.sstate=SemState.completed;
					}
				}
			}
		}
	}
	auto context=expSemContext(sc,ConstResult.yes,InType.no);
	if(sc.allowsLinear){
		auto preState=sc.getStateSnapshot(true);
		be.e2=expressionSemantic(be.e2,context.nestConsumed);
		propErr(be.e2,be);
		checkIndexReplacement(be,sc);
		if(be.sstate!=SemState.error){
			enum flags=LowerDefineFlags.createFresh, unchecked=false;
			if(auto e=lowerDefine!flags(be,sc,unchecked)){
				if(e.sstate!=SemState.error){
					sc.restoreStateSnapshot(preState);
					auto r=statementSemantic(e,sc);
					static if(language==silq){
						finishIndexReplacement(be,sc);
					}
					if(be.sstate==SemState.error){
						sc.clearConsumed();
						return be;
					}
					return lowerIndexReplacement(prologues,epilogues,r,sc);
				}else{
					static if(language==silq)
						finishIndexReplacement(be,sc);
					return lowerIndexReplacement(prologues,epilogues,e,sc);
				}
			}
		}else{
			sc.resetLocalComponentReplacements();
			epilogues=[]; // (avoids error messages)
			// TODO: clean up other temporaries
		}
	}else{
		be.e2=expressionSemantic(be.e2,context.nestConsumed);
	}
	bool success=true;
	auto e2orig=be.e2;
	static if(language==silq) bool badUnpackLhs=false; // (to check that makeDeclaration will indeed produce an error)
	auto de=cast(DefineExp)makeDeclaration(be,success,sc);
	static if(language==silq){
		if(be.e2.sstate==SemState.completed&&sc.getFunction()){
			//getIndexDependency(be.e1)
			Dependency getIndexDependency(Expression e){
				if(auto idx=cast(IndexExp)e){
					auto dep=getIndexDependency(idx.e);
					dep.joinWith(idx.a.getDependency(sc));
					return dep;
				}
				return Dependency(false);
			}
			void addDependencies(Expression[] lhs,Expression[] rhs)in{
				assert(lhs.length==rhs.length);
			}do{
				Q!(Declaration,Dependency)[] dependencies;
				foreach(i;0..lhs.length){
					if(auto id=getIdFromDefLhs(lhs[i])){
						if(id.meaning){
							if(rhs[i].isQfree()){
								auto dep=rhs[i].getDependency(sc);
								dep.joinWith(getIndexDependency(lhs[i]));
								dependencies~=q(id.meaning,dep);
							}else{
								dependencies~=q(id.meaning,Dependency(true));
							}
						}else badUnpackLhs=true;
					}else badUnpackLhs=true;
				}
				sc.addDependencies(dependencies);
			}
			void addDependencyMulti(Expression[] lhs,Dependency dependency){
				Q!(Declaration,Dependency)[] dependencies;
				foreach(i;0..lhs.length){
					if(auto id=getIdFromDefLhs(lhs[i])){
						if(id.meaning){
							auto dep=dependency.dup;
							dep.joinWith(getIndexDependency(lhs[i]));
							dependencies~=q(id.meaning,dep);
						}else badUnpackLhs=true;
					}else badUnpackLhs=true;
				}
				sc.addDependencies(dependencies);
			}
			if(auto id=getIdFromDefLhs(be.e1)){
				addDependencies([be.e1],[be.e2]);
			}else if(auto tpl1=cast(TupleExp)be.e1){
				bool ok=false;
				if(auto tpl2=cast(TupleExp)be.e2){
					if(tpl1.length==tpl2.length){
						ok=true;
						addDependencies(tpl1.e,tpl2.e);
					}
				}
				if(!ok&&be.e2.isQfree()){
					auto dep=be.e2.getDependency(sc);
					addDependencyMulti(tpl1.e,dep);
				}
			}else if(auto ce=cast(CallExp)be.e1){
				// TODO: add dependencies
			}else if(auto ce=cast(CatExp)be.e1){
				if(be.e1.isQfree()){
					Expression[] ids;
					if(auto id=cast(Identifier)unwrap(ce.e1))
						ids~=id;
					if(auto id=cast(Identifier)unwrap(ce.e2))
						ids~=id;
					auto dep=be.e2.getDependency(sc);
					addDependencyMulti(ids,dep);
				}
			}else badUnpackLhs=true;
		}
		if(sc.allowsLinear)
			finishIndexReplacement(be,sc);
	}
	static if(language==silq) if(badUnpackLhs) assert(!de||de.sstate==SemState.error);
	if(!de) be.sstate=SemState.error;
	else propErr(de,be.e1);
	assert(success && de is be || !de||de.sstate==SemState.error);
	auto tt=be.e2.type?be.e2.type.isTupleTy:null;
	auto isBottom=be.e2.type&&isEmpty(be.e2.type);
	if(be.e2.sstate==SemState.completed){
		auto tpl=cast(TupleExp)be.e1;
		if(be.e2.type){
			auto dcontext=defineLhsContext(econtext,be.e2.type,be.e2);
			defineLhsSemantic(be.e1,dcontext);
		}
		if(de){
			if(be.e1.sstate==SemState.error) de.setError();
			if(de.sstate!=SemState.error){
				int i=0;
				foreach(vd;&de.varDecls){
					scope(success) i++;
					if(vd){
						auto nvd=varDeclSemantic(vd,sc);
						assert(nvd is vd);
					}else if(tpl&&tt){
						if(tpl.e.length>i&&tpl.e[i].type&&tt.length>i){
							if(!isSubtype(tt[i],tpl.e[i].type)){
								sc.error(format("cannot assign %s to %s",tt[i],tpl.e[i].type),tpl.e[i].loc);
								be.sstate=SemState.error;
							}
						}
					}else if(be.e1.type&&be.e2.type){
						if(!isSubtype(be.e2.type,be.e1.type)){
							sc.error(format("cannot assign %s to %s",be.e2.type,be.e1.type),be.loc);
							be.sstate=SemState.error;
						}
					}
				}
			}
			de.type=isBottom?bottom:unit;
			propErr(be,de);
		}
		if(cast(TopScope)sc){
			if(!be.e2.isConstant() && !cast(PlaceholderExp)be.e2 && !(isType(be.e2)||isQNumeric(be.e2))){
				sc.error("global constant initializer must be a constant",e2orig.loc);
				if(de){ de.setError(); be.sstate=SemState.error; }
			}
		}
	}else if(de) de.setError();
	auto r=de?de:be;
	if(be.e2.type && be.e2.type.sstate==SemState.completed){
		foreach(id;be.e2.type.freeIdentifiers){
			assert(!!id.meaning);
			auto blocker=r;
			//if(auto sde=cast(SingleDefExp)blocker) if(sde.decl) blocker=sde.decl;
			typeConstBlock(id.meaning,blocker,sc);
		}
	}
	be.type=isBottom?bottom:unit;
	if(r.sstate!=SemState.error) r.sstate=SemState.completed;
	return lowerIndexReplacement(prologues,epilogues,r,sc);
}

Identifier getIdFromIndex(IndexExp e){
	if(auto idx=cast(IndexExp)unwrap(e.e)) return getIdFromIndex(idx);
	return cast(Identifier)unwrap(e.e);
}

Identifier getIdFromDefLhs(Expression e){
	if(auto idx=cast(IndexExp)unwrap(e)) return getIdFromDefLhs(idx.e);
	return cast(Identifier)unwrap(e);
}

bool isBasicIndexType(Expression ty){
	return isSubtype(ty,ℤt(true))||isSubtype(ty,Bool(false))||isFixedIntTy(ty);
}

bool guaranteedDifferentValues(Expression e1,Expression e2,Location loc,Scope sc,InType inType){
	if(auto tpl1=cast(TupleExp)unwrap(e1)){
		if(auto tpl2=cast(TupleExp)unwrap(e2))
			return zip(tpl1.e,tpl2.e).any!(x=>guaranteedDifferentValues(x.expand,loc,sc,inType));
		return false;
	}
	e1=expressionSemantic(e1,expSemContext(sc,ConstResult.yes,inType));
	e2=expressionSemantic(e2,expSemContext(sc,ConstResult.yes,inType));
	if(!util.among(e1.type,Bool(true),ℕt(true),ℤt(true))||!util.among(e2.type,Bool(true),ℕt(true),ℤt(true)))
		return false;
	Expression neq=new NeqExp(e1,e2);
	neq.loc=loc;
	neq=expressionSemantic(neq,expSemContext(sc,ConstResult.yes,inType));
	assert(neq.sstate==SemState.completed);
	return neq.eval()==LiteralExp.makeBoolean(1);
}
bool guaranteedDifferentLocations(Expression e1,Expression e2,Location loc,Scope sc,InType inType){
	e1=unwrap(e1), e2=unwrap(e2);
	if(auto id1=cast(Identifier)e1)
		if(auto id2=cast(Identifier)e2)
			if(id1.name!=id2.name) // TODO: this may become imprecise
				return true;
	if(auto idx1=cast(IndexExp)e1){
		if(auto idx2=cast(IndexExp)e2){
			if(guaranteedDifferentLocations(idx1.e,idx2.e,loc,sc,inType))
				return true;
			return guaranteedDifferentValues(idx1.a,idx2.a,loc,sc,inType);
		}else return true;
	}else if(auto idx2=cast(IndexExp)e2)
		return true;
	return false;
}

bool guaranteedSameValues(Expression e1,Expression e2,Location loc,Scope sc,InType inType){
	if(guaranteedSameLocations(e1,e2,loc,sc,inType)) return true; // TODO: more complete check
	e1=expressionSemantic(e1,expSemContext(sc,ConstResult.yes,inType));
	e2=expressionSemantic(e2,expSemContext(sc,ConstResult.yes,inType));
	if(e1.sstate==SemState.error||e2.sstate==SemState.error)
		return false;
	if(!util.among(e1.type,Bool(true),ℕt(true),ℤt(true))||!util.among(e2.type,Bool(true),ℕt(true),ℤt(true)))
		return false;
	Expression eq=new EqExp(e1,e2);
	eq=expressionSemantic(eq,expSemContext(sc,ConstResult.yes,inType));
	eq.loc=loc;
	assert(eq.sstate==SemState.completed);
	return eq.eval()==LiteralExp.makeBoolean(1);
}
bool guaranteedSameLocations(Expression e1,Expression e2,Location loc,Scope sc,InType inType){
	if(auto id1=cast(Identifier)e1){
		if(auto id2=cast(Identifier)e2){
			// TODO: this is likely to break
			/+if(id1.meaning&&id2.meaning) return id1.meaning==id2.meaning;
			if(id1.meaning) return id1.meaning.name.name==id2.name;
			if(id2.meaning) return id1.name==id2.meaning.name.name;+/
			return id1.name==id2.name;
		}
	}
	if(auto idx1=cast(IndexExp)e1){
		if(auto idx2=cast(IndexExp)e2){
			if(!guaranteedSameLocations(idx1.e,idx2.e,loc,sc,inType))
				return false;
			return guaranteedSameValues(idx1.a,idx2.a,loc,sc,inType);
		}
	}
	return false;
}


static if(language==silq){
struct ArrayConsumer{
	Q!(Expression,Declaration,Dependency,SemState,Scope)[string] consumed;
	Identifier[] ids;
	void consumeArray(IndexExp e,ExpSemContext context){
		Identifier id=null;
		void doIt(IndexExp e){
			if(auto idx=cast(IndexExp)unwrap(e.e)){
				doIt(idx);
				propErr(idx,e.e);
				return;
			}
			auto id=cast(Identifier)unwrap(e.e);
			assert(!!id);
			if(id.name in consumed){
				auto tpl=consumed[id.name];
				id.constLookup=true;
				id.type=tpl[0];
				id.meaning=tpl[1];
				id.sstate=tpl[3];
				id.scope_=tpl[4];
				return;
			}
			if(id.meaning) id.id=id.meaning.name.id;
			auto oldMeaning=id.meaning;
			id.meaning=null;
			//assert(id.sstate!=SemState.completed);
			id.sstate=SemState.initial;
			id.byRef=true;
			e.e=expressionSemantic(e.e,context.nestConsumed); // consume array
			id.byRef=false;
			auto dep=getDependency(e.e,context.sc);
			if(e.e.sstate!=SemState.completed)
				return;
			if(oldMeaning){
				// assert(id.meaning is oldMeaning); // TODO. (id.meaning should already move into local scope earlier)
				assert(id.meaning is oldMeaning||oldMeaning.scope_!is context.sc&&id.meaning.scope_ is context.sc,text(id.meaning," ",oldMeaning," ",id.loc));
				assert(id.name==oldMeaning.getName);
			}
			e.e.constLookup=true;
			id=cast(Identifier)unwrap(e.e);
			assert(!!id);
			ids~=id;
			consumed[id.name]=q(id.type,id.meaning,dep,e.e.sstate,id.scope_);
		}
		doIt(e);
	}
	void redefineArrays(Location loc,Scope sc){
		SetX!Id added;
		foreach(id;ids){
			if(id&&id.meaning&&id.type&&id.id !in added){
				auto var=addVar(id.meaning.name.name,id.type,loc,sc);
				if(id.name in consumed)
					sc.addDependency(var,consumed[id.name][2]);
				else sc.addDefaultDependency(var);
				added.insert(id.id);
			}
		}
	}
}

void checkIndexReplacement(Expression be,Scope sc){
	auto inType=InType.no;
	auto creplss=sc.localComponentReplacementsByDecl();
	foreach(crepls;creplss){
		auto indicesToReplace=crepls.map!(x=>x.write).filter!(x=>!!x).array;
		assert(indicesToReplace.all!(x=>!!getIdFromIndex(x)));
		foreach(i;0..indicesToReplace.length){
			auto idx1=indicesToReplace[i];
			if(idx1.sstate==SemState.error) continue;
			foreach(j;i+1..indicesToReplace.length){
				auto idx2=indicesToReplace[j];
				// (scope will handle this)
				if(idx2.sstate==SemState.error) continue;
				if(!guaranteedDifferentLocations(idx1,idx2,be.loc,sc,inType)){
					if(guaranteedSameLocations(idx1,idx2,be.loc,sc,inType)) sc.error("indices refer to same value in reassignment",idx2.loc);
					else sc.error("indices may refer to same value in reassignment",idx2.loc);
					sc.note("other index is here",idx1.loc);
					idx2.sstate=SemState.error;
					//return;
				}
			}
		}
		foreach(i;0..crepls.length){
			if(!crepls[i].read){
				sc.error("reassigned component must be consumed in right-hand side", indicesToReplace[i].loc);
				indicesToReplace[i].sstate=SemState.error;
				be.sstate=SemState.error;
				if(auto meaning=sc.peekSymtab(crepls[i].name))
					meaning.sstate=SemState.error;
			}
		}
	}
}

void finishIndexReplacement(Expression be,Scope sc){
	auto inType=InType.no;
	auto context=expSemContext(sc,ConstResult.yes,inType);

	auto crepls=sc.localComponentReplacements();
	scope(exit) sc.resetLocalComponentReplacements();
	auto indicesToReplace=crepls.map!(x=>x.write).filter!(x=>!!x).array;
	assert(indicesToReplace.all!(x=>!!getIdFromIndex(x)));
	ArrayConsumer consumer;
	foreach(theIndex;indicesToReplace)
		consumer.consumeArray(theIndex,context);
	consumer.redefineArrays(be.loc,sc);
	foreach(theIndex;indicesToReplace)
		if(theIndex.sstate!=SemState.error)
			theIndex.sstate=SemState.completed;
	foreach(idx;indicesToReplace)
		if(auto id=getIdFromIndex(idx))
			if(id.meaning&&id.meaning.rename)
				id.id=id.meaning.rename.id;
}
}

IndexExp getBaseIndex(IndexExp e){
	if(cast(Identifier)unwrap(e.e)) return e;
	if(auto idx=cast(IndexExp)unwrap(e.e)) return getBaseIndex(idx);
	return null;
}

Expression replaceBaseIndex(T)(T e,Expression newBase)if(is(T==IndexExp)||is(T==TypeAnnotationExp)){
	static if(is(T==IndexExp)) if(cast(Identifier)unwrap(e.e)) return newBase;
	if(auto tae=cast(TypeAnnotationExp)e.e){
		if(auto ne=replaceBaseIndex(tae,newBase)){
			e.e=ne;
			return e;
		}
	}
	if(auto idx=cast(IndexExp)e.e){
		if(auto ne=replaceBaseIndex(idx,newBase)){
		   e.e=ne;
		   return e;
		}
	}
	return null;
}

Scope.DeclProp.ComponentReplacement[][] unnestComponentReplacements(Scope.DeclProp.ComponentReplacement[][] creplss,Location loc,Scope sc){
    Scope.DeclProp.ComponentReplacement[][] result;
    foreach(crepls;creplss){
        void doIt(Scope.DeclProp.ComponentReplacement[] crepls){
            Scope.DeclProp.ComponentReplacement[] curGroup;
	        static struct MapEntry{
		        IndexExp idx;
		        Id name;
	        }
	        MapEntry[] entries;
	        Scope.DeclProp.ComponentReplacement[][] newGroups;
            foreach(crepl;crepls){
	            assert(!!crepl.write);
	            auto idx=getBaseIndex(crepl.write);
	            assert(!!idx);
	            if(idx is crepl.write){
		            curGroup~=crepl;
		            continue;
	            }
	            auto nname=freshName();
	            curGroup~=Scope.DeclProp.ComponentReplacement(idx,nname);
	            auto id=new Identifier(nname);
	            id.loc=idx.loc;
	            auto nidx=cast(IndexExp)replaceBaseIndex(crepl.write.copy(),id);
	            assert(!!nidx,text(crepl.write," ",id));
	            auto ncrepl=Scope.DeclProp.ComponentReplacement(nidx,crepl.name);
                bool ok=false;
                foreach(i,entry;entries){
	                if(guaranteedSameLocations(entry.idx,idx,loc,sc,InType.no)){
		                newGroups[i]~=ncrepl;
                        ok=true;
                        break;
                    }
                }
                if(!ok){
	                entries~=MapEntry(nidx,nname);
                    newGroups~=[ncrepl];
                }
            }
            bool ok=false;
            foreach(i;0..curGroup.length){
	            foreach(j;i+1..curGroup.length){
		            auto a=curGroup[i],b=curGroup[j];
		            assert(a.write&&b.write);
		            if(a.write.sstate==SemState.error||b.write.sstate==SemState.error)
			            continue;
		            if(!guaranteedDifferentLocations(a.write,b.write,loc,sc,InType.no)){
			            if(guaranteedSameLocations(a.write,b.write,loc,sc,InType.no)){
				            sc.error("aliasing of partial index expression not supported yet by component-splitting lowering pass",b.write.loc);
			            }else{
				            sc.error("potential aliasing of partial index expression not supported yet by component-splitting lowering pass",b.write.loc);
			            }
			            sc.note("other index is here",a.write.loc);
			            a.write.sstate=SemState.error;
			            b.write.sstate=SemState.error;
			            ok=false;
		            }
	            }
	            if(!ok) break;
            }

            result~=curGroup;
            foreach(newGroup;newGroups)
	            doIt(newGroup);
        }
        doIt(crepls);
    }
    return result;
}

void typeConstBlock(Declaration decl,Expression blocker,Scope sc){
	if(!isAssignable(decl,sc)) return;
	if(auto vd=cast(VarDecl)decl)
		vd.typeConstBlocker=blocker;
	assert(!isAssignable(decl,sc));
}

bool isAssignable(Declaration meaning,Scope sc){
	auto vd=cast(VarDecl)meaning;
	if(!vd||vd.isConst||vd.typeConstBlocker||sc.isConst(vd)) return false;
	for(auto csc=sc;csc !is meaning.scope_&&cast(NestedScope)csc;csc=(cast(NestedScope)csc).parent)
		if(auto fsc=cast(FunctionScope)csc)
			return false;
	return true;
}

void typeConstBlockNote(VarDecl vd,Scope sc)in{
	assert(!!vd.typeConstBlocker);
}do{
	string name;
	if(auto decl=cast(Declaration)vd.typeConstBlocker) name=decl.getName;
	if(name){
		sc.note(format("'%s' was made 'const' because it appeared in type of '%s'",vd.name,name),vd.typeConstBlocker.loc);
	}else{
		sc.note(format("'%s' was made 'const' because it appeared in type of local variable",vd.name),vd.typeConstBlocker.loc);
	}
}

bool isNonConstVar(Declaration decl,Scope sc){
	auto vd=cast(VarDecl)decl;
	if(!vd||vd.isConst||vd.typeConstBlocker||sc.isConst(vd))
		return false;
	return true;
}

bool checkNonConstVar(string action,string continuous)(Declaration meaning,Location loc,Scope sc){
	if(isNonConstVar(meaning,sc)) return true;
	auto vd=cast(VarDecl)meaning;
	if(vd&&(vd.isConst||vd.typeConstBlocker||sc.isConst(vd))){
		if(cast(Parameter)meaning&&(cast(Parameter)meaning).isConst)
			sc.error("cannot "~action~" 'const' parameters",loc);
		else sc.error("cannot "~action~" 'const' variables",loc);
		if(vd.typeConstBlocker) typeConstBlockNote(vd,sc);
		else if(auto read=sc.isConst(vd))
			sc.note("variable was made 'const' here", read.loc);
	}else if(meaning&&!vd) sc.error(continuous~" non-variables not supported",loc); // (once this works, remember to support typeConstBlocker)
		else if(meaning) sc.error("cannot assign",loc);
	return false;
}

bool checkAssignable(Declaration meaning,Location loc,Scope sc,bool isReversible,bool isReplacement){
	if(!meaning||meaning.sstate==SemState.error) return false;
	if(!checkNonConstVar!("reassign","reassigning")(meaning,loc,sc))
		return false;
	auto vd=cast(VarDecl)meaning;
	static if(language==silq){
		if(!isReversible&&!vd.vtype.isClassical()&&!sc.canForget(meaning)){
			sc.error("cannot reassign quantum variable", loc);
			return false;
		}
	}
	if(isTypeTy(vd.vtype)){
		sc.error("cannot reassign type variables", loc);
		return false;
	}
	if(!isReplacement)
	for(auto csc=sc;csc !is meaning.scope_;csc=(cast(NestedScope)csc).parent){
		if(auto fsc=cast(FunctionScope)csc){
			// TODO: what needs to be done to lift this restriction?
			// TODO: method calls are also implicit assignments.
			auto crepls=meaning.scope_.componentReplacements(meaning);
			if(crepls.length){
				sc.error(format("cannot access aggregate '%s' while its components are being replaced",meaning.getName),loc);
				if(crepls[0].write) sc.note("replaced component is here",crepls[0].write.loc);
				return false;
			}else{
				// TODO: could in principle be allowed (but variable should be removed from outer scope)
				sc.error("cannot assign to variable in closure context",loc);
				sc.note("declared here",meaning.loc);
				return false;
			}

		}
	}
	return true;
}

Expression updatedType(Expression id,Expression lhs,Expression rhsty)in{
	assert(id&&id.type);
	assert(lhs&&lhs.type);
	assert(!!rhsty);
}do{
	if(id is lhs) return rhsty;
	auto idx=cast(IndexExp)lhs;
	assert(!!idx,text(id," ",lhs));
	Expression getNrhsty(){
		if(auto tt=idx.e.type.isTupleTy){
			if(auto lit=idx.a.eval().asIntegerConstant()){
				auto c=lit.get();
				if(c<0||c>=tt.length) return idx.e.type;
				return tupleTy(iota(tt.length).map!(i=>i==c?rhsty:tt[i]).array);
			}
			Expression[] ntypes;
			foreach(i;0..tt.length){
				auto ntype=joinTypes(tt[i],rhsty);
				if(!ntype) return null;
				ntypes~=ntype;
			}
			return tupleTy(ntypes);
		}
		if(auto vt=cast(VectorTy)idx.e.type){
			auto nnext=joinTypes(vt.next,rhsty);
			if(!nnext) return null;
			return vectorTy(nnext,vt.num);
		}
		if(auto at=cast(ArrayTy)idx.e.type){
			auto nnext=joinTypes(at.next,rhsty);
			if(!nnext) return null;
			return arrayTy(nnext);
		}
		if(isFixedIntTy(idx.e.type)){
			if(!cast(BoolTy)rhsty) return null;
			auto rtype=idx.e.type;
			if(!rhsty.isClassical||!idx.a.type.isClassical) rtype=rtype.getQuantum();
			return rtype;
		}
		return null;
	}
	auto nrhsty=getNrhsty();
	if(nrhsty&&!idx.a.type.isClassical) nrhsty=nrhsty.getQuantum();
	if(!nrhsty) return null;
	return updatedType(id,idx.e,nrhsty);
}

Expression assignExpSemantic(AssignExp ae,Scope sc){
	auto context=expSemContext(sc,ConstResult.yes,InType.no);
	CompoundExp[] prologues,epilogues;
	static if(language==silq)
	if(sc.allowsLinear){
		auto oe1=ae.e1.copy();
		prepareIndexReplacements(oe1,sc,prologues,epilogues,ae.loc);
	}
	ae.e2=expressionSemantic(ae.e2,context.nestConsumed);
	propErr(ae.e2,ae);
	void prepareLhs(Expression lhs){
		if(auto id=cast(Identifier)lhs){
			id.byRef=true;
		}else if(auto idx=cast(IndexExp)lhs){
			idx.byRef=true;
		}else if(auto tpl=cast(TupleExp)lhs){
			foreach(exp;tpl.e)
				prepareLhs(exp);
		}
	}
	prepareLhs(ae.e1);
	ae.e1=expressionSemantic(ae.e1,context.nestConsumed);
	propErr(ae.e1,ae);
	if(ae.e1.sstate==SemState.error){
		sc.resetLocalComponentReplacements();
		return ae;
	}
	checkIndexReplacement(ae,sc);
	void checkLhs(Expression lhs,bool indexed){
		if(auto id=cast(Identifier)lhs){
			if(!checkAssignable(id.meaning,ae.loc,sc,false,false))
				ae.sstate=SemState.error;
		}else if(auto tpl=cast(TupleExp)lhs){
			if(indexed){
				sc.error("cannot index into tuple expression in left-hand side of assignment",lhs.loc);
				ae.sstate=SemState.error;
				return;
			}
			foreach(exp;tpl.e)
				checkLhs(exp,indexed);
		}else if(auto idx=cast(IndexExp)lhs){
			checkLhs(idx.e,true);
		}else if(auto fe=cast(FieldExp)lhs){
			if(isBuiltIn(fe))
				goto LbadAssgnmLhs;
			checkLhs(fe.e,true);
		}else if(auto tae=cast(TypeAnnotationExp)lhs){
			checkLhs(tae.e,indexed);
		}else{
		LbadAssgnmLhs:
			sc.error(format("cannot assign to %s",lhs),ae.e1.loc);
			ae.sstate=SemState.error;
		}
	}
	checkLhs(ae.e1,false);
	propErr(ae.e1,ae);
	void checkCompat(Expression lhs,Expression type){
		if(auto id=cast(Identifier)lhs)
			return; // strong update allowed
		if(auto tpl=cast(TupleExp)lhs){
			if(auto tt=type.isTupleTy){
				if(tpl.length!=tt.length){
					// TODO: technically this violates monotonicity of type checking w.r.t. subtyping
					sc.error(text("inconsistent number of tuple entries for assignment: ",tpl.length," vs. ",tt.length),lhs.loc);
					ae.sstate=SemState.error;
				}else{
					foreach(i,exp;tpl.e)
						checkCompat(exp,tt[i]);
				}
			}else if(auto at=cast(ArrayTy)type){
				foreach(exp;tpl.e)
					checkCompat(exp,at.next);
			}else{
				sc.error(format("cannot unpack type %s as a tuple",type),lhs.loc);
				ae.sstate=SemState.error;
			}
		}else if(auto idx=cast(IndexExp)lhs){
			if(!joinTypes(type,lhs.type)){
				sc.error(format("cannot assign '%s' to array entry '%s' of type '%s'",type,lhs,lhs.type),lhs.loc);
				ae.sstate=SemState.error;
			}
		}else if(auto fe=cast(FieldExp)lhs){
			// TODO: add strong field updates
			if(!isSubtype(type,lhs.type)){
				sc.error(format("cannot assign '%s' to field '%s' of type '%s'",type,lhs,lhs.type),lhs.loc);
				ae.sstate=SemState.error;
			}
		}else if(auto tae=cast(TypeAnnotationExp)lhs){
			checkCompat(tae.e,type); // TODO: ok?
		}else assert(ae.sstate==SemState.error);
	}
	if(ae.e2.type) checkCompat(ae.e1,ae.e2.type);
	static if(language==silq){
		enum Stage{
			collectDeps,
			consumeLhs,
			defineVars,
		}
	}else{
		enum Stage{
			consumeLhs,
			defineVars,
		}
	}
	static if(language==silq){
		Dependency[Declaration] dependencies;
		int curDependency;
	}
	Declaration[Declaration] consumed;
	void[0][Id] defined;
	void updateVars(Expression lhs,Expression rhs,Stage stage){
		Dependency rhsdep(){
			if(stage!=Stage.collectDeps||!rhs.isQfree()) return Dependency(true);
			return rhs.getDependency(sc);
		}
		void updateVars2(Expression lhs,Expression olhs,bool indexed,Expression rhsty,Dependency rhsdep,Stage stage){
			if(auto id=cast(Identifier)lhs){
				if(id&&id.meaning&&id.meaning.name){
					static if(language==psi){
						if(auto fd=sc.getFunction){
							if(id.meaning is fd.context)
								return; // TODO: this is a hack. treat "this" parameter as ref instead.
						}
					}
					auto decl=id.meaning;
					final switch(stage){
						static if(language==silq){
							case Stage.collectDeps:
								if(rhs.isQfree()){
									auto dep=rhsdep.dup;
									if(indexed){
										dep.joinWith(lhs.getDependency(sc)); // TODO: index-aware dependency tracking?
										if(decl in dependencies) dep.joinWith(dependencies[decl]);
									}
									if(decl in dep.dependencies){
										dep.remove(decl);
										dep.joinWith(sc.getDependency(decl));
									}
									dependencies[decl]=dep;
								}
								break;
						}
						case Stage.consumeLhs:
							if(decl !in consumed){
								if(!indexed) id.constLookup=false;
								if(decl.scope_ is sc){
									sc.unconsume(decl);
									consumed[decl]=sc.consume(decl);
								}else{
									consumed[decl]=decl;
									assert(ae.sstate==SemState.error);
								}
								static if(language==silq)
									sc.clearConsumed();
							}
							break;
						case Stage.defineVars:
							if(decl.getId !in defined){
								auto name=decl.name.name;
								Expression ntype=indexed?null:rhsty;
								if(id.type&&rhsty){
									ntype=updatedType(id,olhs,rhsty);
									if(!ntype){
										sc.error("assignment not yet supported",ae.loc);
										ae.sstate=SemState.error;
										ntype=indexed?id.type:rhsty;
									}
								}
								auto var=addVar(name,ntype,lhs.loc,sc);
								static if(language==silq){
									if(rhs.isQfree()) sc.addDependency(var,dependencies[decl]);
								}
								defined[decl.getId]=[];
								ae.replacements~=AssignExp.Replacement(consumed[decl],var);
							}
							break;
					}
				}
			}else if(auto tpll=cast(TupleExp)lhs){
				if(auto tt=rhsty?rhsty.isTupleTy:null){
					assert(tpll.length==tt.length);
					foreach(i,exp;tpll.e) updateVars2(exp,exp,indexed,tt[i],rhsdep,stage);
				}else if(auto at=cast(ArrayTy)rhsty){
					foreach(exp;tpll.e) updateVars2(exp,olhs,indexed,at.next,rhsdep,stage);
				}else assert(ae.sstate==SemState.error);
			}else if(auto idx=cast(IndexExp)lhs){
				auto nrhsdep=rhsdep;
				if(stage==Stage.collectDeps){
					nrhsdep=nrhsdep.dup;
					nrhsdep.joinWith(idx.a.getDependency(sc));
				}
				updateVars2(idx.e,olhs,true,rhsty,nrhsdep,stage); // TODO: pass indices down?
			}else if(auto fe=cast(FieldExp)lhs){
				updateVars2(fe.e,olhs,true,rhsty,rhsdep,stage);
			}else if(auto tae=cast(TypeAnnotationExp)lhs){
				updateVars2(tae.e,olhs,indexed,rhsty,rhsdep,stage);
			}else assert(ae.sstate==SemState.error);
		}
		if(auto tpll=cast(TupleExp)lhs){
			bool ok=false;
			if(auto tplr=cast(TupleExp)rhs){
				if(tpll.e.length==tplr.e.length){
					foreach(i;0..tpll.e.length)
						updateVars(tpll.e[i],tplr.e[i],stage);
					return;
				}
			}
		}else if(auto tae=cast(TypeAnnotationExp)lhs){
			return updateVars(tae.e,rhs,stage);
		}
		return updateVars2(lhs,lhs,false,rhs.type,rhsdep,stage);
	}
	static if(language==silq)
		updateVars(ae.e1,ae.e2,Stage.collectDeps);
	updateVars(ae.e1,ae.e2,Stage.consumeLhs);
	static if(language==silq)
		sc.clearConsumed();
	updateVars(ae.e1,ae.e2,Stage.defineVars);
	ae.type=unit;
	if(ae.sstate!=SemState.error){
		static if(language==silq){
			finishIndexReplacement(ae,sc);
		}
	}else{
		sc.resetLocalComponentReplacements();
		epilogues=[]; // (avoids error messages)
		// TODO: clean up other temporaries
	}
	if(ae.sstate!=SemState.error) ae.sstate=SemState.completed;
	return lowerIndexReplacement(prologues,epilogues,ae,sc);
}

AAssignExp isOpAssignExp(Expression e){ return cast(AssignExp)e?null:cast(AAssignExp)e; }

AAssignExp isInvertibleOpAssignExp(Expression e){
	auto r=isOpAssignExp(e);
	if(r&&(cast(AddAssignExp)e||cast(SubAssignExp)e||cast(NSubAssignExp)e||cast(CatAssignExp)e||cast(BitXorAssignExp)e))
		return r;
	return null;
}

Expression opAssignExpSemantic(AAssignExp be,Scope sc)in{
	assert(isOpAssignExp(be));
}do{
	auto context=expSemContext(sc,ConstResult.yes,InType.no);
	CompoundExp[] prologues,epilogues;
	static if(language==silq)
	if(sc.allowsLinear){
		auto oe1=be.e1.copy();
		prepareIndexReplacements(oe1,sc,prologues,epilogues,be.loc);
	}
	static if(language==silq){
		// TODO: assignments to fields
		auto semanticDone=false;
		if(auto id=cast(Identifier)be.e1){
			int nerr=sc.handler.nerrors; // TODO: this is a bit hacky
			auto meaning=sc.lookup(id,false,true,Lookup.probingWithCapture);
			if(nerr!=sc.handler.nerrors){
				sc.note("looked up here",id.loc);
				return be;
			}
			if(meaning){
				meaning=sc.split(meaning);
				id.meaning=meaning;
				id.id=meaning.getId;
				id.type=id.typeFromMeaning;
				id.scope_=sc;
				id.sstate=SemState.completed;
			}else{
				sc.error(format("undefined identifier %s",id.name),id.loc);
				id.sstate=SemState.error;
			}
			semanticDone=true;
		}
	}else enum semanticDone=false;
	be.e2=expressionSemantic(be.e2,context.nest(cast(CatAssignExp)be?ConstResult.no:ConstResult.yes));
	propErr(be.e2,be);
	if(!semanticDone){
		void prepareLhs(Expression lhs){
			if(auto id=cast(Identifier)lhs){
				id.byRef=true;
			}else if(auto idx=cast(IndexExp)lhs){
				idx.byRef=true;
			}
		}
		prepareLhs(be.e1);
		be.e1=expressionSemantic(be.e1,context.nestConsumed);
		propErr(be.e1,be);
		if(auto id=cast(Identifier)be.e1){
			if(id.meaning&&be.sstate!=SemState.error){
				if(!sc.lookup(id,false,false,Lookup.probing))
					sc.unconsume(id.meaning); // TODO: ok?
			}
			id.byRef=false; // TODO: why does checker not like this?
		}
	}
	if(be.sstate==SemState.error){
		sc.resetLocalComponentReplacements();
		return be;
	}
	checkIndexReplacement(be,sc);
	void checkULhs(Expression lhs){
		if(auto id=cast(Identifier)lhs){
			if(!checkAssignable(id.meaning,be.loc,sc,!!isInvertibleOpAssignExp(be),true))
				be.sstate=SemState.error;
		}else if(auto idx=cast(IndexExp)lhs){
			checkULhs(idx.e);
		}else if(auto fe=cast(FieldExp)lhs){
			checkULhs(fe.e);
		}else{
		LbadAssgnmLhs:
			sc.error(format("cannot update-assign to %s",lhs),be.e1.loc);
			be.sstate=SemState.error;
		}
	}
	ABinaryExp ce=null;
	import ast.parser;
	static foreach(op;binaryOps){
		static if(op.endsWith("←")&&op!="←"){
			if(auto ae=cast(BinaryExp!(Tok!op))be){
				ce=new BinaryExp!(Tok!(op[0..$-"←".length]))(be.e1.copy(), be.e2);
				ce.loc=be.loc;
				ae.operation=ce;
			}
		}
	}
	assert(!!ce);
	auto nce=expressionSemantic(ce,context.nestConsumed);
	if(auto id=cast(Identifier)be.e1)
		if(auto nid=cast(Identifier)ce.e1)
			if(nid.meaning)
				id.meaning=nid.meaning;
	assert(nce is ce);
	propErr(ce, be);
	checkULhs(be.e1);
	static if(language==silq){
		if(be.sstate!=SemState.error&&!be.e1.type.isClassical()){
			auto id=cast(Identifier)be.e1;
			if(!id){
				sc.error(format("cannot update-assign to quantum expression %s",be.e1),be.e1.loc);
				be.sstate=SemState.error;
			}else if((!isInvertibleOpAssignExp(be)||be.e2.hasFreeIdentifier(id.id))&&id.meaning&&!sc.canForget(id.meaning)){
				sc.error("quantum update must be invertible",be.loc);
				be.sstate=SemState.error;
			}
		}
	}
	auto id=cast(Identifier)be.e1;
	if(id&&id.meaning&&id.meaning.name){
		void consume(){
			id.constLookup=false;
			sc.consume(id.meaning);
			static if(language==silq)
				sc.clearConsumed();
		}
		void define(Dependency dependency){
			auto name=id.meaning.name.name;
			auto var=addVar(name,ce.type,be.loc,sc);
			be.replacements~=AAssignExp.Replacement(id.meaning,var);
			sc.addDependency(var,dependency);
			auto from=typeForDecl(id.meaning),to=typeForDecl(var);
			if(isFixedIntTy(to)&&!joinTypes(from,to)){ // TODO: generalize?
				sc.error(format("operator assign from type '%s' to type '%s' is disallowed",from,to),be.loc);
				sc.note(format("change the type of '%s' or use a regular assignment",id.meaning),id.meaning.loc);
				be.sstate=SemState.error;
			}
		}
		static if(language==silq){
			bool ok=false;
			if(be.e2.isQfree()){
				auto dependency=sc.getDependency(id.meaning);
				auto rhsDep=be.e2.getDependency(sc);
				rhsDep.remove(id.meaning);
				dependency.joinWith(rhsDep);
				consume();
				define(dependency);
			}else{
				consume();
				define(Dependency(true));
			}
		}else{
			consume();
			define();
		}
	}
	be.type=unit;
	if(be.sstate!=SemState.error){
		static if(language==silq){
			finishIndexReplacement(be,sc);
		}
	}else{
		sc.resetLocalComponentReplacements();
		epilogues=[]; // (avoids error messages)
		if(id&&id.meaning&&id.meaning.getName.startsWith("__"))
			sc.consume(id.meaning);
		foreach(repl;be.replacements)
			if(repl.new_.getName.startsWith("__"))
			   sc.consume(repl.new_);
	}
	if(be.sstate!=SemState.error) be.sstate=SemState.completed;
	return lowerIndexReplacement(prologues,epilogues,be,sc);
}

bool isAssignment(Expression e){
	return cast(AssignExp)e||isOpAssignExp(e);
}

Expression assignSemantic(Expression e,Scope sc)in{
	assert(isAssignment(e));
}do{
	if(auto ae=cast(AssignExp)e) return assignExpSemantic(ae,sc);
	if(auto be=isOpAssignExp(e)) return opAssignExpSemantic(be,sc);
	assert(0);
}

bool isDefineOrAssign(Expression e){
	return isAssignment(e)||cast(DefineExp)e;
}

Expression defineOrAssignSemantic(Expression e,Scope sc)in{
	assert(isDefineOrAssign(e));
}do{
	if(isAssignment(e)) return assignSemantic(e,sc);
	if(auto be=cast(DefineExp)e) return defineSemantic(be,sc);
	assert(0);
}

Expression expectDefineOrAssignSemantic(Expression e,Scope sc){
	if(auto ce=cast(CommaExp)e){
		ce.e1=expectDefineOrAssignSemantic(ce.e1,sc);
		propErr(ce.e1,ce);
		ce.e2=expectDefineOrAssignSemantic(ce.e2,sc);
		propErr(ce.e2,ce);
		ce.type=unit;
		if(ce.sstate!=SemState.error) ce.sstate=SemState.completed;
		return ce;
	}
	if(isDefineOrAssign(e)) return defineOrAssignSemantic(e,sc);
	sc.error("expected assignment or variable declaration",e.loc);
	e.sstate=SemState.error;
	return e;
}


static if(language==silq){

Identifier getReverse(Location loc,Scope isc,Annotation annotation,bool checked,bool outerWanted)in{
	assert(annotation>=Annotation.mfree);
}do{
	auto r=getPreludeSymbol(annotation==Annotation.qfree?"__reverse_qfree":"reverse",loc,isc);
	if(!checked) r.checkReverse=false; // TODO: is there a better solution than this for frontend reverse?
	if(!outerWanted) r.outerWanted=false; // TODO: is there a better solution than this?
	return r;
}

bool isReverse(Identifier id){
	if(!id) return false;
	if(id.name!="reverse") return false;
	return id.meaning&&isReverse(id.meaning);
}

bool isReverse(Declaration decl){
	if(!isInPrelude(decl)) return false;
	if(!decl.name) return false;
	return decl.getName=="reverse";
}

Parameter[] makeParams(C,R,T)(C isConst,R paramNames,T types,Location loc)in{
	assert(isConst.length==paramNames.length);
}do{
	return zip(isConst,paramNames,types).map!((x){
		auto isConst=x[0], name=new Identifier(x[1]), type=x[2];
		name.loc=loc;
		name.type=type;
		auto param=new Parameter(isConst,name,type);
		param.loc=loc;
		return param;
	}).array;
}

Expression[] makeIdentifiers(S)(S names,Location loc){
	return names.map!((name){
		Expression id=new Identifier(name);
		id.loc=loc;
		return id;
	}).array;
}

Expression[] makeIndexLookups(I)(Id name,I indices,Location loc){
	return indices.map!((i){
		auto id=new Identifier(name);
		id.loc=loc;
		auto index=LiteralExp.makeInteger(i);
		index.loc=loc;
		Expression idx=new IndexExp(id,index);
		idx.loc=loc;
		return idx;
	}).array;
}

Expression lookupParams(Parameter[] params, bool isTuple,Location loc)in{
	assert(isTuple||params.length==1);
}do{
	auto args=params.map!((p){
		auto id=new Identifier(p.name.id);
		id.meaning=p;
		id.loc=p.loc;
		Expression r=id;
		return r;
	}).array;
	auto narg=isTuple?new TupleExp(args):args[0];
	narg.loc=loc;
	return narg;
}

Expression makeReverseCall(Expression ce1,Annotation annotation,bool check,Scope sc,Location loc,bool outerWanted){
	auto ce2=new CallExp(getReverse(loc,sc,annotation,check,outerWanted),ce1,false,false);
	ce2.loc=loc;
	return ce2;
}

CompoundExp makeLambdaBody(Expression ce2,Location loc){
	auto ret=new ReturnExp(ce2);
	ret.loc=loc;
	auto body_=new CompoundExp([ret]);
	body_.loc=loc;
	return body_;
}

Expression makeLambda(Parameter[] params,bool isTuple,bool isSquare,Annotation annotation,CompoundExp body_,Location loc){
	auto def=new FunctionDef(null,params,isTuple,null,body_);
	def.isSquare=isSquare;
	def.annotation=annotation;
	def.loc=loc;
	auto le=new LambdaExp(def);
	le.loc=loc;
	return le;
}

Expression tryReverse(Identifier reverse,Expression f,bool isSquare,bool isClassical,Scope sc,bool simplify){
	bool errors=false;
	auto ft=cast(FunTy)f.type;
	if(!ft) return null;
	bool check=reverse.checkReverse;
	bool outerWanted=reverse.outerWanted;
	auto ft2=cast(FunTy)ft.cod;
	if(ft2&&ft.isSquare&&ft.isConst.all&&!ft2.isSquare){
		auto loc=f.loc;
		auto names=iota(ft.names.length).map!(i=>"`arg_"~(ft.names[i]?ft.names[i].str:text(i)));
		auto types=iota(ft.nargs).map!((i){
			auto type=ft.argTy(i);
			if(type==typeTy){
				bool checkType(Expression ty){
					if(ty.isQuantum) return true;
					return !ty.hasFreeVar(ft.names[i]);
				}
				bool ok=true;
				foreach(j;0..ft2.nargs){
					if(ft2.isConstForReverse[j]) continue;
					ok&=checkType(ft2.argTy(j));
					if(!ok) break;
				}
				if(ok) ok&=checkType(ft2.cod);
				if(!ok) type=qtypeTy;
			}
			return type;
		});
		auto params=makeParams(ft.isConst,names,types,loc);
		auto narg=lookupParams(params,ft.isTuple,loc);
		auto ce1=new CallExp(f.copy,narg,true,false);
		ce1.loc=loc;
		auto ce2=makeReverseCall(ce1,Annotation.mfree,check,sc,loc,outerWanted);
		auto body_=makeLambdaBody(ce2,loc);
		auto le=makeLambda(params,ft.isTuple,ft.isSquare,ft.annotation,body_,loc);
		return le;
	}
	if(check && ft.annotation<Annotation.mfree){
		sc.error("reversed function must be 'mfree'",f.loc);
		f.sstate=SemState.error;
		errors=true;
	}
	if(check && !ft.isClassical_){
		sc.error("reversed function must be classical",f.loc);
		f.sstate=SemState.error;
		errors=true;
	}
	if(ft.cod.hasAnyFreeVar(ft.names)){
		sc.error("arguments of reversed function call cannot appear in result type",f.loc);
		f.sstate=SemState.error;
		errors=true;
	}
	if(!errors){
		auto loc=f.loc;
		auto r=reverseCallRewriter(ft,loc);
		if(!r.innerNeeded){
			if(!check){
				if(equal(ft.isConst,only(true,false))){
					auto τ=ft.argTy(0),χ=ft.argTy(1),φ=ft.cod;
					auto arg=new TupleExp([τ,χ,φ]);
					arg.loc=reverse.loc;
					arg.type=tupleTy([τ.type,χ.type,φ.type]);
					arg.sstate=SemState.completed;
					auto nce=new CallExp(reverse,arg,true,false);
					nce.loc=reverse.loc;
					auto rtype=funTy([true,false],tupleTy([τ,φ]),χ,ft.isSquare,true,ft.annotation,ft.isClassical);
					nce.type=funTy([true],f.type,rtype,false,false,Annotation.qfree,ft.isClassical);
					nce.sstate=SemState.completed;
					auto res=new CallExp(nce,f,isSquare,isClassical);
					res.type=rtype;
					res.sstate=SemState.completed;
					return res;
				}
			}
			return null;
		}
		if(check&&r.movedType.hasClassicalComponent()){
			sc.error("reversed function cannot have classical components in 'moved' arguments", f.loc);
			errors=true;
		}
		if(check&&r.returnType.hasClassicalComponent()){
			sc.error("reversed function cannot have classical components in return value", f.loc);
			errors=true;
		}
		if(errors) return null;
		auto le=r.wrapInner(f);
		auto rev=makeReverseCall(le,ft.annotation,check,sc,loc,outerWanted);
		if(!r.outerNeeded||!reverse.outerWanted) return rev;
		auto le2=r.wrapOuter(rev,simplify);
		return le2;
	}
	return null;
}

Expression tryReverseSemantic(CallExp ce,ExpSemContext context){
	auto reverse=cast(Identifier)ce.e;
	assert(reverse&&isReverse(reverse));
	ce.arg=expressionSemantic(ce.arg,/+context.nest((rft.isConst.length?rft.isConst[0]:true)?ConstResult.yes:ConstResult.no)+/context.nestConst);
	enum simplify=true;
	auto r=tryReverse(reverse,ce.arg,ce.isSquare,ce.isClassical,context.sc,simplify);
	if(ce.arg.sstate==SemState.error)
		return null;
	if(!r) return null;
	r=expressionSemantic(r,context);
	if(r.sstate==SemState.error){
		ce.sstate=SemState.error;
		return ce;
	}
	return r;
}

}

Expression callSemantic(bool isPresemantic=false,T)(CallExp ce,T context)if(is(T==ExpSemContext)&&!isPresemantic||is(T==DefineLhsContext)){
	enum isRhs=is(T==ExpSemContext);
	static argSemantic(Expression e,T context)in{
		assert(!!e);
	}do{
		static if(!isRhs){
			if(context.constResult) return expressionSemantic(e,context.expSem);
			return defineLhsSemantic!isPresemantic(e,context);
		}else return expressionSemantic(e,context);
	}
	if(auto id=cast(Identifier)ce.e) id.calledDirectly=true;
	static if(isRhs) ce.e=expressionSemantic(ce.e,context.nestConsumed);
	else ce.e=expressionSemantic(ce.e,context.expSem.nestConsumed);
	propErr(ce.e,ce);
	if(ce.sstate==SemState.error)
		return ce;
	auto sc=context.sc, constResult=context.constResult, inType=context.inType;
	scope(success){
		if(ce&&ce.sstate!=SemState.error&&sc){ // (sc can be null when called from combineTypes)
			if(auto ft=cast(FunTy)ce.e.type){
				if(inType){
					static if(language==silq){
						if(ft.annotation<Annotation.qfree){
							sc.error(format("function called within type must be 'qfree'"),ce.loc);
							ce.sstate=SemState.error;
						}
					}else static if(language==psi){
						if(ft.annotation<Annotation.pure_){
							sc.error(format("function called within type must be 'pure'"),ce.loc);
							ce.sstate=SemState.error;
						}
					}
				}
				FunctionDef reason=null;
				auto restriction=Annotation.none;
				if(sc) restriction=sc.restriction(reason);
				if(sc&&ft.annotation<restriction){
					bool fixed=false;
					if(reason&&reason.inferAnnotation&&ft.annotation<reason.annotation){
						if(reason.sealed) reason.unseal();
						reason.annotation=min(reason.annotation,ft.annotation);
						reason.ftype=null;
						setFtype(reason,true);
						fixed=true;
					}
					if(!fixed){
						if(ft.annotation==Annotation.none){
							sc.error(format("cannot call function '%s' in '%s' context", ce.e, annotationToString(restriction)), ce.loc);
						}else{
							sc.error(format("cannot call '%s' function '%s' in '%s' context", ft.annotation, ce.e, annotationToString(restriction)), ce.loc);
						}
						// TODO: inference trace
						ce.sstate=SemState.error;
					}
				}
				static if(language==silq && isRhs){
					if((isType(ce)||isQNumeric(ce))&&ce.isClassical_)
						ce.type=getClassicalTy(ce.type);
					if(ce.e.type.isClassical()&&ce.arg.type.isClassical()&&ft.annotation>=Annotation.qfree){
						if(auto classical=ce.type.getClassical())
							ce.type=classical;
					}
					if(constResult&&!ce.isLifted(sc)&&!ce.type.isClassical()){
						sc.error("non-'lifted' quantum expression must be consumed", ce.loc);
						ce.sstate=SemState.error;
					}
				}
			}
		}
	}
	auto fun=ce.e;
	bool matchArg(FunTy ft){
		void checkArg(size_t i,Expression exp)in{
			assert(exp.sstate==SemState.error||exp.type,text(exp));
		}do{
			if(exp.sstate==SemState.error) return;
			static if(language==silq){
				bool classical=exp.type.isClassical(), qfree=exp.isQfree();
				if((!classical||!qfree)&&i<ft.names.length&&ft.cod.hasFreeVar(ft.names[i])){
					if(classical){ // TODO: could just automatically deduce existential type
						sc.error(format("argument must be 'qfree' (return type '%s' depends on parameter '%s')",ft.cod,ft.names[i]),exp.loc);
						sc.note(format("perhaps store it in a local variable before passing it as an argument"),exp.loc);
					}else{
						sc.error(format("argument must be classical (return type '%s' depends on parameter '%s')",ft.cod,ft.names[i]),exp.loc);
					}
					exp.sstate=SemState.error;
				}
			}else static if(language==psi){
				bool pure_=exp.isPure();
				if(!pure_&&i<ft.names.length&&ft.cod.hasFreeVar(ft.names[i])){
					sc.error(format("argument must be 'pure' (return type '%s' depends on parameter '%s')",ft.cod,ft.names[i]),exp.loc);
					sc.note(format("perhaps store it in a local variable before passing it as an argument"),exp.loc);
					exp.sstate=SemState.error;
				}
			}
		}
		if(ft.isTuple){
			if(auto tpl=cast(TupleExp)ce.arg){
				void wrongNumberOfArgs(){
					static if(isRhs) enum msg="wrong number of arguments for function (%s instead of %s)";
					else enum msg="wrong number of arguments for reversed function call (%s instead of %s)";
					sc.error(format(msg,tpl.length,ft.nargs),ce.loc);
					tpl.sstate=SemState.error;
				}
				bool defaultIsConst=true;
				if(ft.nargs!=tpl.length){
					if(ft.isConst.any!(c=>c!=ft.isConst[0])){
						wrongNumberOfArgs();
					}else{
						defaultIsConst=ft.isConst.all;
					}
				}
				if(tpl.sstate!=SemState.error){
					foreach(i,ref exp;tpl.e){
						static if(isRhs){
							auto isConst=(ft.nargs==tpl.e.length?ft.isConst[i]:defaultIsConst);
							auto ncontext=context.nest(isConst?ConstResult.yes:ConstResult.no);
						}else{
							auto isConst=(ft.nargs==tpl.e.length?ft.isConstForReverse[i]:defaultIsConst);
							auto aty=ft.nargs==tpl.e.length?ft.argTy(i):null;
							auto ncontext=context.nest(isConst?ConstResult.yes:ConstResult.no,aty,null);
						}
						exp=argSemantic(exp,ncontext);
						static if(isRhs) checkArg(i,exp);
						propErr(exp,tpl);
					}
				}
				if(tpl.sstate!=SemState.error){
					if(ft.nargs!=tpl.length){
						wrongNumberOfArgs();
					}else{
						static if(!isRhs){
							foreach(i,ref exp;tpl.e){
								if(ft.isConstForReverse[i])
									continue;
								if(auto id=cast(Identifier)exp){
									if(!id.type)
										id.type=ft.argTy(i);
								}
							}
						}
					}
				}
				if(tpl.sstate!=SemState.error&&(isRhs||tpl.e.all!(e=>!!e.type))) // TODO: ensure type is always set
					tpl.type=tupleTy(tpl.e.map!(e=>e.type).array);
			}else{
				static if(isRhs){
					auto isConst=(ft.isConst.length?ft.isConst[0]:true);
					auto ncontext=context.nest(isConst?ConstResult.yes:ConstResult.no);
				}else{
					auto isConst=(ft.isConst.length?ft.isConstForReverse[0]:true);
					auto aty=ft.dom;
					auto ncontext=context.nest(isConst?ConstResult.yes:ConstResult.no,aty,null);
				}
				ce.arg=argSemantic(ce.arg,ncontext);
				static if(isRhs) foreach(i;0..ft.names.length) checkArg(i,ce.arg);
				if(!ft.isConst.all!(x=>x==ft.isConst[0])){
					sc.error("cannot match single tuple to function with mixed 'const' and consumed parameters",ce.loc);
					ce.sstate=SemState.error;
					return true;
				}
			}
		}else{
			assert(ft.isConst.length==1);
			static if(isRhs){
				auto isConst=ft.isConst[0];
				auto ncontext=context.nest(isConst?ConstResult.yes:ConstResult.no);
			}else{
				auto isConst=ft.isConstForReverse[0];
				auto aty=ft.dom;
				auto ncontext=context.nest(isConst?ConstResult.yes:ConstResult.no,aty,null);
			}
			ce.arg=argSemantic(ce.arg,ncontext);
			assert(ft.names.length==1);
			static if(isRhs) checkArg(0,ce.arg);
		}
		return false;
	}
	Expression checkFunCall(FunTy ft){
		void checkArg(Expression arg,Expression paramTy){
			if(arg.type&&!isSubtype(arg.type,paramTy)){
				sc.error(format("cannot pass argument of type '%s' to parameter of type '%s'",arg.type,paramTy),arg.loc);
				arg.sstate=SemState.error;
				ce.sstate=SemState.error;
			}
		}
		bool tryCall(){
			if(!ce.isSquare && ft.isSquare){
				auto nft=ft;
				if(auto id=cast(Identifier)fun){
					if(auto decl=cast(DatDecl)id.meaning){
						if(auto constructor=decl.constructor){
							if(auto cty=cast(FunTy)typeForDecl(constructor)){
								assert(isTypeTy(ft.cod));
								nft=productTy(ft.isConst,ft.names,ft.dom,cty,ft.isSquare,ft.isTuple,ft.annotation,true);
							}
						}
					}
				}
				if(auto codft=cast(ProductTy)nft.cod){
					if(codft.isSquare) return false;
					if(matchArg(codft)) return true;
					propErr(ce.arg,ce);
					if(ce.arg.sstate==SemState.error) return true;
					if(isRhs||codft.isConstForReverse.all){
						Expression garg;
						auto tt=nft.tryMatch(ce.arg,garg);
						if(!tt) return false;
						Expression.CopyArgs cargs={ preserveMeanings: true };
						auto nce=new CallExp(ce.e,garg.copy(cargs),true,false);
						nce.loc=ce.loc;
						auto nnce=new CallExp(nce,ce.arg,false,false);
						nnce.loc=ce.loc;
						static if(isRhs) nnce=cast(CallExp)callSemantic(nnce,context.nestConsumed);
						else nnce=cast(CallExp)callSemantic(nnce,context.expSem.nestConsumed);
						assert(!!nnce);
						ce=nnce;
						return true;
					}else{
						// TODO: analyze arguments?
						return true;
					}
				}
			}
			if(ft.isSquare!=ce.isSquare) return false;
			if(matchArg(ft)) return true;
			propErr(ce.arg,ce);
			if(ce.arg.sstate==SemState.error) return true;
			static if(isRhs){
				ce.type=ft.tryApply(ce.arg,ce.isSquare);
				return !!ce.type;
			}else{
				if(ce.sstate!=SemState.error){
					if(ft.isTuple){
						if(auto tpl=cast(TupleExp)ce.arg){
							assert(ft.nargs==tpl.length);
							foreach(i,arg;tpl.e) checkArg(arg,ft.argTy(i));
						}
					}
					if(ft.isConstForReverse.all){
						checkArg(ce.arg,ft.dom);
					}else assert(ft.isTuple||!ft.isConstForReverse.any);
				}
				if(ft.cod.hasAnyFreeVar(ft.names)){
					sc.error("arguments of reversed function call cannot appear in result type",ce.loc);
					ce.sstate=SemState.error;
					return true;
				}else{
					ce.type=ft.cod;
					return true;
				}
			}
		}
		static if(language==silq && isRhs){ // TODO: probably this can work on lhs
			auto calledId=cast(Identifier)ce.e;
			switch(isPreludeSymbol(calledId)){
				default: break;
				case PreludeSymbol.reverse:
					if(auto r=tryReverseSemantic(ce,context))
						return r;
					break;
			}
		}
		if(ce.sstate!=SemState.error&&!tryCall()){
			auto aty=ce.arg.type;
			if(isEmpty(aty)) return ce.arg;
			if(ft.isSquare&&!ce.isSquare&&isEmpty(ft.cod)){
				auto lit=LiteralExp.makeBoolean(false);
				lit.loc=ce.e.loc;
				auto garg=new AssertExp(lit); // TODO: detect and error out if this makes it past type checking?
				garg.loc=ce.e.loc;
				auto ne=new CallExp(ce.e,garg,true,false);
				ne.loc=ce.e.loc;
				ce.e=ne;
				return callSemantic(ce,context);
			}
			if(!aty) aty=ce.arg;
			if(ce.isSquare!=ft.isSquare)
				sc.error(text("function of type ",ft," cannot be called with arguments ",ce.isSquare?"[":"",aty,ce.isSquare?"]":""),ce.loc);
			else sc.error(format("expected argument types %s, but %s was provided",ft.dom,aty),ce.loc);
			ce.sstate=SemState.error;
		}
		return ce;
	}
	Expression r=ce;
	if(auto ft=cast(FunTy)fun.type){
		r=checkFunCall(ft);
		if(r !is ce) ce=null;
	}else if(auto at=isRhs?isDataTyId(fun):null){
		auto decl=at.decl;
		assert(isType(fun));
		auto constructor=decl.constructor;
		auto ty=cast(FunTy)typeForDecl(constructor);
		if(ty&&decl.hasParams){
			auto nce=cast(CallExp)fun;
			assert(!!nce);
			auto subst=decl.getSubst(nce.arg);
			ty=cast(ProductTy)ty.substitute(subst);
			assert(!!ty);
		}
		if(!constructor||!ty){
			sc.error(format("no constructor for type %s",at),ce.loc);
			ce.sstate=SemState.error;
		}else{
			ce=cast(CallExp)checkFunCall(ty);
			assert(!!ce);
			if(ce&&ce.sstate!=SemState.error){
				auto id=new Identifier(constructor.getId);
				id.loc=fun.loc;
				id.scope_=sc;
				id.meaning=constructor;
				id.scope_=sc;
				id.type=ty;
				id.sstate=SemState.completed;
				if(auto fe=cast(FieldExp)fun){
					assert(fe.e.sstate==SemState.completed);
					ce.e=new FieldExp(fe.e,id);
					ce.e.type=id.type;
					ce.e.loc=fun.loc;
					ce.e.sstate=SemState.completed;
				}else ce.e=id;
			}
		}
	}else if(isRhs&&isBuiltIn(cast(Identifier)ce.e)){
		static if(isRhs){
			auto id=cast(Identifier)ce.e;
			switch(id.name){
				static if(language==silq){
					case "__primitive":
						return handlePrimitive(ce, context);
					case "__show":
						ce.arg=expressionSemantic(ce.arg,context.nestConst);
						auto lit=cast(LiteralExp)ce.arg;
						if(lit&&lit.lit.type==Tok!"``") sc.message(lit.lit.str,ce.loc);
						else sc.message(text(ce.arg),ce.loc);
						ce.type=unit;
						break;
					case "__query":
						return handleQuery(ce,context);
				}else static if(language==psi){
					case "Marginal":
						ce.arg=expressionSemantic(ce.arg,context.nestConst);
						propErr(ce.arg,ce);
						if(ce.arg.type) ce.type=distributionTy(ce.arg.type,sc);
						break;
					case "sampleFrom":
						return handleSampleFrom(ce,sc,inType);
				}
				default: assert(0,text("TODO: ",id.name));
			}
		}else assert(0);
	}else if(isType(fun.type)&&isEmpty(fun.type)){
		// TODO: treat as const those arguments that are used again
		if(!isPresemantic){
			static if(isRhs){
				ce.arg=expressionSemantic(ce.arg,context.nestConsumed);
			}else{
				auto ncontext=context.nest(ConstResult.no,bottom,null);
				ce.arg=defineLhsSemantic!isPresemantic(ce.arg,ncontext);
			}
			propErr(ce.arg,ce);
			//imported!"util.io".writeln(ce.arg," ",ce.arg.type);
			auto argTy=ce.arg.type;
			if(!argTy) argTy=bottom;
			auto nfunTy=new BinaryExp!(Tok!"→")(argTy,bottom,Annotation.qfree,false);
			nfunTy.loc=ce.e.loc;
			auto cnfunTy=new UnaryExp!(Tok!"¬")(nfunTy);
			cnfunTy.loc=nfunTy.loc;
			auto nfun=new TypeAnnotationExp(ce.e,cnfunTy,TypeAnnotationType.annotation);
			nfun.loc=ce.e.loc;
			ce.e=nfun;
			return callSemantic(ce,context);
		}
	}else{
		sc.error(format("cannot call expression of type %s",fun.type),ce.loc);
		ce.sstate=SemState.error;
	}
	return r;
}

enum ConstResult:bool{
	no,
	yes,
}
enum InType:bool{
	no,
	yes,
}

Expression unwrap(Expression e){
	if(auto tae=cast(TypeAnnotationExp)e)
		return unwrap(tae.e);
	return e;
}

bool unrealizable(Expression e){
	return !isType(e);
}

struct ExpSemContext{
	Scope sc;
	ConstResult constResult;
	InType inType;
}
auto expSemContext(Scope sc,ConstResult constResult,InType inType){
	return ExpSemContext(sc,constResult,inType);
}
auto nest(ref ExpSemContext context,ConstResult newConstResult){
	with(context) return expSemContext(sc,newConstResult,inType);
}
auto nestConst(ref ExpSemContext context){
	return context.nest(ConstResult.yes);
}
auto nestConsumed(ref ExpSemContext context){
	return context.nest(ConstResult.no);
}

Expression conditionSemantic(bool allowQuantum=false)(Expression e,Scope sc,InType inType){
	e=expressionSemantic(e,expSemContext(sc,ConstResult.yes,inType));
	static if(language==silq) sc.clearConsumed();
	auto ty=e.sstate==SemState.completed&&e.type?e.type.eval():null;
	if(e.sstate==SemState.completed && !isSubtype(ty,Bool(!allowQuantum))){
		static if(language==silq){
			static if(allowQuantum) sc.error(format("type of condition should be !𝔹 or 𝔹, not %s",e.type),e.loc);
			else sc.error(format("type of condition should be !𝔹, not %s",e.type),e.loc);
		}else sc.error(format("type of condition should be 𝔹, not %s",e.type),e.loc);
		e.sstate=SemState.error;
	}
	return e;
}

Expression branchSemantic(Expression branch,ExpSemContext context,bool quantumControl){ // TODO: actually introduce a bottom type?
	auto sc=context.sc, inType=context.inType;
	if(inType) return expressionSemantic(branch,context);
	branch=expressionSemantic(branch,context);
	if(quantumControl){
		if(branch.type&&branch.type.hasClassicalComponent()){
			if(auto qtype=branch.type.getQuantum()){
				if(isType(qtype)){
					auto nbranch=new TypeAnnotationExp(branch,qtype,TypeAnnotationType.annotation);
					nbranch.loc=branch.loc;
					branch=nbranch;
					branch=expressionSemantic(branch,context);
				}
			}
		}
	}
	return branch;
}

Expression expressionSemanticImpl(IteExp ite,ExpSemContext context){
	auto sc=context.sc, inType=context.inType;
	ite.cond=conditionSemantic!true(ite.cond,sc,inType);
	if(ite.cond.type) ite.cond.type=ite.cond.type.eval();
	if(ite.then.s.length!=1||ite.othw&&ite.othw.s.length!=1){
		sc.error("branch of if expression must be single expression",ite.then.s.length!=1?ite.then.loc:ite.othw.loc);
		ite.sstate=SemState.error;
		return ite;
	}
	static if(language==silq){
		auto quantumControl=ite.cond.type&&!ite.cond.type.isClassical();
		auto restriction_=quantumControl?Annotation.mfree:Annotation.none;
	}else{
		enum quantumControl=false;
		enum restriction_=Annotation.none;
	}
	// initialize scopes, to allow captures to be inserted
	if(!ite.then.blscope_) ite.then.blscope_=new BlockScope(sc,restriction_);
	if(ite.othw&&!ite.othw.blscope_) ite.othw.blscope_=new BlockScope(sc,restriction_);
	ite.then.s[0]=branchSemantic(ite.then.s[0],ExpSemContext(ite.then.blscope_,context.constResult,inType),quantumControl);
	static if(language==silq) ite.then.blscope_.clearConsumed();
	propErr(ite.then.s[0],ite.then);
	if(!ite.othw){
		sc.error("missing else for if expression",ite.loc);
		ite.sstate=SemState.error;
		return ite;
	}
	ite.othw.s[0]=branchSemantic(ite.othw.s[0],ExpSemContext(ite.othw.blscope_,context.constResult,inType),quantumControl);
	static if(language==silq) ite.othw.blscope_.clearConsumed();
	propErr(ite.othw.s[0],ite.othw);
	propErr(ite.cond,ite);
	propErr(ite.then,ite);
	propErr(ite.othw,ite);
	if(ite.sstate!=SemState.error){
		auto t1=ite.then.s[0].type;
		auto t2=ite.othw.s[0].type;
		ite.type=joinTypes(t1,t2);
		if(t1 && t2 && !ite.type){
			sc.error(format("incompatible types %s and %s for branches of if expression",t1,t2),ite.loc);
			ite.sstate=SemState.error;
		}
		if(quantumControl&&ite.type&&ite.type.hasClassicalComponent()){
			sc.error(format("type '%s' of if expression with quantum control has classical components",ite.type),ite.loc);
			ite.sstate=SemState.error;
		}
	}
	if(sc.merge(quantumControl,ite.then.blscope_,ite.othw.blscope_)){
		sc.note("consumed in one branch of if expression", ite.loc);
		ite.sstate=SemState.error;
	}
	if(inType){
		if(ite.then) ite.then.blscope_=null;
		if(ite.othw) ite.othw.blscope_=null;
	}
	if(ite.sstate!=SemState.error) ite.sstate=SemState.completed;
	return ite;
}

Expression expressionSemanticImpl(AssertExp ae,ExpSemContext context){
	auto sc=context.sc,inType=context.inType;
	ae.e=conditionSemantic(ae.e,sc,inType);
	propErr(ae.e,ae);
	ae.type=isFalse(ae.e)?bottom:unit;
	return ae;
}

Expression expressionSemanticImpl(LiteralExp le,ExpSemContext context){
	switch(le.lit.type){
		case Tok!"0",Tok!".0":
			if(!le.type)
				le.type=util.among(le.lit.str,"0","1")?Bool(true):le.lit.str.canFind(".")?ℝ(true):le.lit.str.canFind("-")?ℤt(true):ℕt(true); // TODO: type inference
			return le;
		case Tok!"``":
			le.type=stringTy(true);
			return le;
		default:
			return expressionSemanticImplDefault(le,context);
	}
}

Expression expressionSemanticImpl(LambdaExp le,ExpSemContext context){
	auto sc=context.sc, inType=context.inType;
	FunctionDef nfd=le.fd;
	if(!le.fd.scope_){
		le.fd.scope_=context.sc;
		nfd=cast(FunctionDef)presemantic(nfd,sc);
	}else assert(le.fd.scope_ is sc);
	assert(!!nfd);
	le.fd=functionDefSemantic(nfd,sc);
	assert(!!le.fd);
	propErr(le.fd,le);
	if(le.fd.sstate==SemState.passive)
		le.fd.sstate=SemState.completed; // TODO: ok?
	le.type=typeForDecl(le.fd);
	if(!le.type){
		sc.error("invalid forward reference",le.loc);
		le.sstate=SemState.error;
	}else if(!subscribeToTypeUpdates(le.fd,sc,le.loc))
		le.sstate=SemState.error;
	if(le.sstate!=SemState.error){
		le.sstate=SemState.completed;
	}
	if(inType) le.fd.scope_=null;
	return le;
}

Expression expressionSemanticImpl(CallExp ce,ExpSemContext context){
	return callSemantic(ce,context);
}

static if(language==psi)
Expression expressionSemanticImpl(PlaceholderExp pl,ExpSemContext context){
	pl.type = ℝ;
	pl.sstate = SemState.completed;
	return pl;
}

Expression expressionSemanticImpl(ForgetExp fe,ExpSemContext context){
	auto sc=context.sc, inType=context.inType;
	bool checkImplicitForget(Expression var){
		if(auto tpl=cast(TupleExp)var) return tpl.e.all!checkImplicitForget;
		auto id=cast(Identifier)var;
		if(!id) return false;
		static if(language==silq){
			if(auto meaning=sc.lookup(id,false,true,Lookup.probing)){
				if(!sc.dependencyTracked(meaning)) return false;
				return sc.canForget(meaning);
			}else return false;
		}else return true;
	}
	auto canForgetImplicitly=checkImplicitForget(fe.var);
	void setByRef(Expression var){
		if(auto tpl=cast(TupleExp)var)
			tpl.e.each!setByRef;
		if(auto id=cast(Identifier)var)
			id.byRef=true;
	}
	setByRef(fe.var);
	fe.var=expressionSemantic(fe.var,context.nestConsumed);
	propErr(fe.var,fe);
	void classicalForget(Expression var){
		if(auto tpl=cast(TupleExp)var){
			tpl.e.each!classicalForget;
			return;
		}
		auto id=cast(Identifier)var;
		if(!id) return;
		auto meaning=id.meaning;
		if(!meaning) return;
		if(!checkNonConstVar!("forget","forgetting")(meaning,id.loc,sc)){
			fe.sstate=SemState.error;
			return;
		}
	}
	classicalForget(fe.var);
	if(fe.val){
		if(fe.var.type){
			auto nval=new TypeAnnotationExp(fe.val,fe.var.type,TypeAnnotationType.coercion);
			nval.loc=fe.val.loc;
			fe.val=nval;
		}
		fe.val=expressionSemantic(fe.val,context.nestConst);
		propErr(fe.val,fe);
		static if(language==silq) if(fe.sstate!=SemState.error&&!fe.val.isLifted(sc)){
			sc.error("forget expression must be 'lifted'",fe.val.loc);
			fe.sstate=SemState.error;
		}
		if(fe.sstate!=SemState.error&&fe.var.type&&fe.val.type)
			assert(fe.var.type==fe.val.type);
		static if(language!=silq){
			if(!canForgetImplicitly){
				sc.error("forget expression should be variable or tuple of variables",fe.var.loc);
				fe.sstate=SemState.error;
			}
		}
	}else if(!canForgetImplicitly&&fe.sstate!=SemState.error){
		static if(language==silq){
			sc.error(format("cannot synthesize forget expression for '%s'",fe.var),fe.loc);
		}else{
			sc.error("forget expression should be variable or tuple of variables",fe.var.loc);
		}
		fe.sstate=SemState.error;
	}
	fe.type=unit;
	return fe;
}

Declaration lookupMeaning(Identifier id,Lookup lookup,Scope sc,bool ignoreExisting=false){
	if(!ignoreExisting&&id.meaning) return id.meaning;
	int nerr=sc.handler.nerrors; // TODO: this is a bit hacky
	id.meaning=sc.lookup(id,false,true,lookup);
	if(nerr!=sc.handler.nerrors&&id.sstate!=SemState.error){ // TODO: still needed?
		sc.note("looked up here",id.loc);
		id.sstate=SemState.error;
	}
	return id.meaning;
}

Expression expressionSemanticImpl(Identifier id,ExpSemContext context){
	auto sc=context.sc;
	id.scope_=sc;
	if(id.sstate==SemState.error) return id;
	if(id.sstate==SemState.started){
		sc.error("invalid forward reference",id.loc);
		id.sstate=SemState.error;
		return id;
	}
	assert(id.sstate!=SemState.started);
	id.constLookup=context.constResult;
	id.sstate=SemState.started;
	auto meaning=id.meaning;
	bool implicitDup=false;
	Expression dupIfNeeded(Identifier result){
		static if(language==silq){
			if(implicitDup){
				result.constLookup=true;
				if(result.calledDirectly||result.indexedDirectly) return result;
				if(result.sstate!=SemState.error) result.sstate=SemState.completed;
				auto nresult=expressionSemantic(dupExp(result,result.loc,context.sc),context);
				return nresult;
			}
		}
		return result;
	}
	if(!meaning){
		id.meaning=lookupMeaning(id,Lookup.probing,sc);
		auto nonLinear=id.meaning&&(!id.byRef&&!id.meaning.isLinear()||id.meaning.isConst);
		if(id.meaning)
			implicitDup=!id.byRef&&!context.constResult&&!id.meaning.isLinear(); // TODO: last-use analysis
		auto lookup=nonLinear||context.constResult||implicitDup?Lookup.constant:Lookup.consuming;
		meaning=lookupMeaning(id,lookup,sc,true);
		if(id.sstate==SemState.error) return id;
		if(!meaning){
			if(auto r=builtIn(id,sc)){
				if(!id.calledDirectly&&util.among(id.name,"Expectation","Marginal","sampleFrom","__query","__show")){
					sc.error("special operator must be called directly",id.loc);
					id.sstate=r.sstate=SemState.error;
				}
				return r;
			}
			sc.error(format("undefined identifier %s",id.name),id.loc);
			id.sstate=SemState.error;
			return dupIfNeeded(id);
		}else{
			static if(language==silq){
				if(!id.indexedDirectly&&meaning.sstate!=SemState.error){
					auto crepls=sc.componentReplacements(meaning);
					if(crepls.length){
						sc.error(format("cannot access aggregate '%s' while its components are being replaced",meaning.getName),id.loc);
						if(crepls[0].write) sc.note("replaced component is here",crepls[0].write.loc);
						id.sstate=SemState.error;
					}
				}
			}
		}
		id.meaning=meaning;
	}else if(sc) sc.recordAccess(id,meaning);
	id.id=meaning.getId;
	propErr(meaning,id);
	id.type=id.typeFromMeaning;
	if(!id.type&&id.sstate!=SemState.error){
		auto fd=cast(FunctionDef)meaning;
		if(fd){
			fd.ret=bottom;
			setFtype(fd,true);
			id.type=id.typeFromMeaning;
		}
		if(!id.type){
			sc.error("invalid forward reference",id.loc);
			if(fd&&!fd.rret)
				sc.note("possibly caused by missing return type annotation for recursive function",fd.loc);
			id.sstate=SemState.error;
		}
	}
	if(id.type){
		if(!subscribeToTypeUpdates(meaning,sc,id.loc))
			id.sstate=SemState.error;
	}
	if(!isType(id)){
		if(auto dsc=isInDataScope(meaning.scope_)){
			if(auto decl=sc.getDatDecl()){
				if(decl is dsc.decl){
					auto this_=new Identifier("this");
					this_.loc=id.loc;
					this_.scope_=sc;
					auto fe=new FieldExp(this_,id);
					fe.loc=id.loc;
					return expressionSemantic(fe,context.nestConsumed);
				}
			}
		}
	}
	return dupIfNeeded(id);
}

Expression expressionSemanticImpl(FieldExp fe,ExpSemContext context){
	auto sc=context.sc, inType=context.inType;
	fe.e=expressionSemantic(fe.e,context.nestConst);
	propErr(fe.e,fe);
	if(fe.sstate==SemState.error)
		return fe;
	auto noMember(){
		sc.error(format("no member %s for type %s",fe.f,fe.e.type),fe.loc);
		fe.sstate=SemState.error;
		return fe;
	}
	DatDecl aggrd=null;
	if(auto aggrty=cast(AggregateTy)fe.e.type) aggrd=aggrty.decl;
	else if(auto id=cast(Identifier)fe.e.type) if(auto dat=cast(DatDecl)id.meaning) aggrd=dat;
	Expression arg=null;
	if(auto ce=cast(CallExp)fe.e.type){
		if(auto id=cast(Identifier)ce.e){
			if(auto decl=cast(DatDecl)id.meaning){
				aggrd=decl;
				arg=ce.arg;
			}
		}
	}
	if(aggrd){
		if(aggrd.body_.ascope_){
			auto meaning=aggrd.body_.ascope_.lookupHere(fe.f,false,Lookup.consuming);
			if(!meaning) return noMember();
			fe.f.meaning=meaning;
			fe.f.id=meaning.getId;
			fe.f.scope_=sc;
			fe.f.type=fe.f.typeFromMeaning;
			if(fe.f.type&&aggrd.hasParams){
				auto subst=aggrd.getSubst(arg);
				fe.f.type=fe.f.type.substitute(subst);
			}
			fe.f.sstate=SemState.completed;
			fe.type=fe.f.type;
			if(!fe.type){
				fe.sstate=SemState.error;
				fe.f.sstate=SemState.error;
			}
			return fe;
		}else return noMember();
	}else if(auto r=builtIn(fe,sc)){
		bool hasSideEffect(){
			static if(language==silq) return !fe.e.isQfree();
			else return false;
		}
		if(fe.f.name=="length"&&!hasSideEffect){
			if(auto vt=cast(VectorTy)fe.e.type){
				Expression.CopyArgs cargs={ preserveMeanings: true };
				auto len=vt.num.copy(cargs);
				len.loc=fe.loc;
				return expressionSemantic(len,context);
			}else if(auto tt=cast(TupleTy)fe.e.type){
				auto len=LiteralExp.makeInteger(tt.length);
				len.loc=fe.loc;
				return expressionSemantic(len,context);
			}
		}
		return r;
	}
	else return noMember();
}

Expression expressionSemanticImpl(IndexExp idx,ExpSemContext context){
	auto sc=context.sc, inType=context.inType;
	if(auto id=cast(Identifier)idx.e) id.indexedDirectly=true;
	if(idx.byRef){
		if(auto cid=getIdFromIndex(idx)){
			cid.meaning=lookupMeaning(cid,Lookup.probingWithCapture,sc);
			if(cid.meaning) cid.meaning=sc.split(cid.meaning);
		}
	}
	idx.e=expressionSemantic(idx.e,context.nestConst);
	propErr(idx.e,idx);
	if(auto ft=cast(FunTy)idx.e.type){
		auto ce=new CallExp(idx.e,idx.a,true,false);
		ce.loc=idx.loc;
		return callSemantic(ce,context);
	}
	if(isType(idx.e)||isQNumeric(idx.e)){
		if(auto tpl=cast(TupleExp)idx.a){
			if(tpl.length==0){
				if(auto tty=typeSemantic(idx,sc,true))
					return tty;
			}
		}
	}
	idx.a=expressionSemantic(idx.a,context.nestConst);
	propErr(idx.a,idx);
	if(idx.sstate==SemState.error)
		return idx;
	static if(language==silq){
		bool replaceIndex=false;
		size_t replaceIndexLoc=size_t.max;
	}
	static if(language==silq)
	if(auto cid=getIdFromIndex(idx)) if(cid.meaning){
		auto crepls=sc.componentReplacements(cid.meaning);
		foreach(i,crepl;crepls){
			static assert(is(typeof(crepl):T*,T));
			if(crepl.write&&!crepl.read&&guaranteedSameLocations(crepl.write,idx,idx.loc,sc,inType)){
				auto rid=getIdFromIndex(crepl.write);
				assert(rid && rid.meaning);
				assert(rid.name==cid.name);
				assert(cid.meaning is rid.meaning);
				replaceIndex=true;
				replaceIndexLoc=i;
				break;
			}
		}
		if(!replaceIndex){
			foreach(i,crepl;crepls){
				if(crepl.write){
					auto rid=getIdFromIndex(crepl.write);
					assert(rid && rid.meaning);
					if(rid.meaning is cid.meaning && cid.scope_ && rid.scope_ is cid.scope_){
						cid.constLookup=true;
						assert(cid.type==rid.type);
						assert(cid.meaning is rid.meaning);
						if(!guaranteedDifferentLocations(crepl.write,idx,idx.loc,sc,inType)){
							if(guaranteedSameLocations(crepl.write,idx,idx.loc,sc,inType)){
								sc.error("lookup of index refers to consumed value",idx.loc);
							}else sc.error("lookup of index may refer to consumed value",idx.loc);
							if(crepl.read) // should always be non-null
								sc.note("consumed here",crepl.read.loc);
							else sc.note("reassigned here",crepl.write.loc);
							idx.sstate=SemState.error;
							break;
						}
					}
				}
			}
		}
	}
	Expression check(Expression next,Expression index,Expression indexTy,Location indexLoc){
		if(isBasicIndexType(indexTy)){
			if(!indexTy.isClassical()&&next.hasClassicalComponent()){
				if(auto qty=next.getQuantum()){
					return qty;
				}else{
					sc.error(format("cannot use quantum index to index array whose elements of type '%s' have classical components",next),indexLoc);
					idx.sstate=SemState.error;
				}
			}
			return next;
		}
		if(auto tpl=cast(TupleExp)index){
			auto types=tpl.e.map!(e=>check(next,e,e.type,e.loc)).array;
			if(types.all!(e=>e!is null)) return tupleTy(types);
			return null;
		}
		if(auto at=cast(ArrayTy)indexTy){
			auto type=check(next,null,at.next,indexLoc);
			if(type) return arrayTy(type);
			return null;
		}
		if(auto vt=cast(VectorTy)indexTy){
			auto type=check(next,null,vt.next,indexLoc);
			if(type) return vectorTy(type,vt.num);
			return null;
		}
		if(auto tt=cast(TupleTy)indexTy){
			auto types=tt.types.map!(ty=>check(next,null,ty,indexLoc)).array;
			if(types.all!(e=>e!is null)) return tupleTy(types);
			return null;
		}
		if(isEmpty(indexTy)) return bottom;
		sc.error(format("index should be integer, not %s",indexTy),indexLoc);
		idx.sstate=SemState.error;
		return null;
	}
	if(auto at=cast(ArrayTy)idx.e.type){
		idx.type=check(at.next, idx.a, idx.a.type, idx.a.loc);
	}else if(auto vt=cast(VectorTy)idx.e.type){
		idx.type=check(vt.next, idx.a, idx.a.type, idx.a.loc);
	}else if(auto idxInt=isFixedIntTy(idx.e.type)){
		idx.type=check(Bool(idxInt.isClassical), idx.a, idx.a.type, idx.a.loc);
	}else if(auto tt=cast(TupleTy)idx.e.type){
		Expression checkTpl(Expression index){
			if(auto lit=index.eval().asIntegerConstant()){
				auto c=lit.get();
				if(c<0||c>=tt.types.length){
					// TODO: technically this violates monotonicity of type checking w.r.t subtyping
					sc.error(format("index for type %s is out of bounds [0..%s)",tt,tt.types.length),index.loc);
					idx.sstate=SemState.error;
					return null;
				}else{
					return tt.types[cast(size_t)c.toLong()];
				}
			}
			if(auto tpl=cast(TupleExp)index){
				auto types=tpl.e.map!(e=>checkTpl(e)).array;
				if(types.all!(e=>e!is null)) return tupleTy(types);
				return null;
			}
			Expression next=bottom;
			foreach(i;0..tt.types.length) next=next?joinTypes(next,tt.types[i]):null;
			if(next) return check(next,index,index.type,index.loc);
			if(isEmpty(index.type)) return bottom;
			sc.error(format("index for type %s should be integer constant",tt),index.loc); // TODO: allow dynamic indexing if known to be safe?
			idx.sstate=SemState.error;
			return null;
		}
		idx.type=checkTpl(idx.a);
	}else if(isEmpty(idx.e.type)){
		return idx.e;
	}else{
		sc.error(format("type %s is not indexable",idx.e.type),idx.loc);
		if(isType(idx.e)||isQNumeric(idx.e)){
			if(!cast(TupleExp)idx.a)
				sc.note(format("did you mean to write '%s^%s'?",idx.e,idx.a),idx.loc);
		}
		idx.sstate=SemState.error;
	}
	static if(language==silq)
	if(replaceIndex){
		auto cid=getIdFromIndex(idx);
		assert(cid&&cid.meaning);
		auto crepls=sc.componentReplacements(cid.meaning);
		assert(replaceIndexLoc<crepls.length);
		if(context.constResult&&!sc.canForget(cid.meaning)){ // TODO: ok?
			sc.error("replaced component must be consumed",idx.loc);
			sc.note("replaced component is here",crepls[replaceIndexLoc].write.loc);
			idx.sstate=SemState.error;
		}
		if(!context.constResult){
			crepls[replaceIndexLoc].read=idx; // matched
			cid.byRef=true;
			idx.byRef=true;
		}
		auto id=new Identifier(crepls[replaceIndexLoc].name);
		id.loc=idx.loc;
		if(!context.constResult) id.byRef=true;
		return expressionSemantic(id,context);
	}
	static if(language==silq)
	if(!idx.byRef&&!context.constResult){ // implicitly duplicate index
		return expressionSemantic(dupExp(idx,idx.loc,context.sc),context);
	}
	return idx;
}

Expression expressionSemanticImpl(SliceExp sl,ExpSemContext context){
	auto sc=context.sc;
	sl.e=expressionSemantic(sl.e,context.nestConst);
	propErr(sl.e,sl);
	sl.l=expressionSemantic(sl.l,context.nestConst);
	propErr(sl.l,sl);
	sl.r=expressionSemantic(sl.r,context.nestConst);
	propErr(sl.r,sl);
	if(sl.sstate==SemState.error)
		return sl;
	// TODO: quantum slicing (at least when length is known)
	if(!isSubtype(sl.l.type,ℤt(true))){
		sc.error(format("lower bound should be classical integer, not %s",sl.l.type),sl.l.loc);
		sl.l.sstate=SemState.error;
	}
	if(!isSubtype(sl.r.type,ℤt(true))){
		sc.error(format("upper bound should be classical integer, not %s",sl.r.type),sl.r.loc);
		sl.r.sstate=SemState.error;
	}
	if(sl.sstate==SemState.error)
		return sl;
	auto at=cast(ArrayTy)sl.e.type;
	auto vt=cast(VectorTy)sl.e.type;
	auto lval=sl.l.eval(), rval=sl.r.eval();
	auto mlc=lval.asIntegerConstant();
	auto mrc=rval.asIntegerConstant();
	auto next=at?at.next:vt?vt.next:null;
	if(!next&&(!mlc||!mrc)){
		if(auto tt=cast(TupleTy)sl.e.type){
			next=bottom;
			foreach(i;0..tt.types.length) next=next?joinTypes(next,tt.types[i]):null;
		}
	}
	if(next){
		auto se=new NSubExp(rval,lval);
		se.type=nSubType(sl.r.type,sl.l.type);
		se.sstate=SemState.completed;
		sl.type=vectorTy(next,se.eval());
	}else if(auto tt=cast(TupleTy)sl.e.type){
		if(!mlc){
			sc.error(format("slice lower bound for type %s should be integer constant",cast(Expression)tt),sl.loc);
			sl.sstate=SemState.error;
		}
		if(!mrc){
			sc.error(format("slice upper bound for type %s should be integer constant",cast(Expression)tt),sl.loc);
			sl.sstate=SemState.error;
		}
		if(sl.sstate==SemState.error)
			return sl;
		auto lc=mlc.get(), rc=mrc.get();
		if(lc<0){
			sc.error(format("slice lower bound for type %s cannot be negative",tt),sl.loc);
			sl.sstate=SemState.error;
		}
		if(lc>rc){
			sc.error("slice lower bound exceeds slice upper bound",sl.loc);
			sl.sstate=SemState.error;
		}
		if(rc>tt.length){
			sc.error(format("slice upper bound for type %s exceeds %s",tt,tt.length),sl.loc);
			sl.sstate=SemState.error;
		}
		if(sl.sstate!=SemState.error){
			sl.type=tt[cast(size_t)lc..cast(size_t)rc];
		}
	}else if(isEmpty(sl.e.type)){
		return sl.e;
	}else{
		sc.error(format("type %s is not sliceable",sl.e.type),sl.loc);
		sl.sstate=SemState.error;
	}
	return sl;
}

Expression expressionSemanticImpl(TupleExp tpl,ExpSemContext context){
	foreach(ref exp;tpl.e){
		exp=expressionSemantic(exp,context);
		propErr(exp,tpl);
	}
	if(tpl.sstate!=SemState.error){
		tpl.type=tupleTy(tpl.e.map!(e=>e.type).array);
	}
	return tpl;
}

Expression expressionSemanticImpl(VectorExp vec,ExpSemContext context){
	auto sc=context.sc;
	Expression t; bool tok=true;
	foreach(i,ref exp;vec.e){
		exp=expressionSemantic(exp,context);
		propErr(exp,vec);
		auto nt = joinTypes(t, exp.type);
		if(!nt&&tok){
			Expression texp;
			foreach(j,oexp;vec.e[0..i]){
				if(!joinTypes(oexp, exp)){
					texp=oexp;
					break;
				}
			}
			if(texp){
				sc.error(format("incompatible types %s and %s in vector literal",t,exp.type),texp.loc);
				sc.note("incompatible entry",exp.loc);
			}
			vec.sstate=SemState.error;
			tok=false;
		}else t=nt;
	}
	if(vec.e.length && t){
		if(vec.e[0].type) vec.type=vectorTy(t,LiteralExp.makeInteger(vec.e.length));
	}else{
		vec.type=vectorTy(bottom,LiteralExp.makeInteger(0));
	}
	return vec;
}

Expression expressionSemanticImpl(TypeAnnotationExp tae,ExpSemContext context){
	auto sc=context.sc;
	tae.e=expressionSemantic(tae.e,context);
	if(tae.e.type)
		if(auto r=resolveWildcards(tae.t,tae.e.type))
			tae.t=r;
	tae.type=typeSemantic(tae.t,sc);
	propErr(tae.e,tae);
	propErr(tae.t,tae);
	if(tae.type) tae.t=tae.type;
	else tae.sstate=SemState.error;
	if(tae.sstate==SemState.error)
		return tae;
	if(auto ce=cast(CallExp)tae.e){
		if(auto id=cast(Identifier)ce.e){
			if(id.name=="sampleFrom"||id.name=="readCSV"&&tae.type==arrayTy(arrayTy(ℝ(true))))
				ce.type=tae.type;
		}
	}
	if(!explicitConversion(tae.e,tae.type,tae.annotationType)){
		final switch(tae.annotationType){
			case TypeAnnotationType.annotation:
				sc.error(format("type is %s, not %s",tae.e.type,tae.type),tae.loc);
				if(explicitConversion(tae.e,tae.type,TypeAnnotationType.conversion))
					sc.note(format("explicit conversion possible, use '%s as %s'",tae.e,tae.type),tae.loc);
				else if(explicitConversion(tae.e,tae.type,TypeAnnotationType.coercion))
					sc.note(format("(unsafe type coercion possible)"),tae.loc);
				break;
			case TypeAnnotationType.conversion:
				sc.error(format("cannot convert from type %s to %s",tae.e.type,tae.type),tae.loc);
				if(explicitConversion(tae.e,tae.type,TypeAnnotationType.coercion))
					sc.note(format("(unsafe type coercion possible)"),tae.loc);
				break;
			case TypeAnnotationType.coercion:
				sc.error(format("cannot coerce type %s to %s",tae.e.type,tae.type),tae.loc);
				break;
			case TypeAnnotationType.punning:
				sc.error(format("punning type %s to %s not supported",tae.e.type,tae.type),tae.loc);
				break;
		}
		tae.sstate=SemState.error;
	}
	return tae;
}

Expression arithmeticType(bool preserveBool)(Expression t1, Expression t2){
	auto int1 = isFixedIntTy(t1);
	auto int2 = isFixedIntTy(t2);
	if(int1 && int1.isSigned && isSubtype(t2,ℤt(false))) return t2.isClassical()?t1:t1.getQuantum();
	if(int2 && int2.isSigned && isSubtype(t1,ℤt(false))) return t1.isClassical()?t2:t2.getQuantum();
	if(int1 && !int1.isSigned && isSubtype(t2,ℤt(false))) return t2.isClassical()?t1:t1.getQuantum();
	if(int2 && !int2.isSigned && isSubtype(t1,ℤt(false))) return t1.isClassical()?t2:t2.getQuantum();
	if(int1 || int2)
		return joinTypes(t1,t2);
	if(!(isNumeric(t1)||isEmpty(t1))||!(isNumeric(t2)||isEmpty(t2))) return null;
	auto r=joinTypes(t1,t2);
	if((isEmpty(t1)||isEmpty(t2))&&isSubtype(r,ℤt(false))) return bottom; // 1+(_:⊥) may become 1+(0:int[n])
	static if(!preserveBool){
		if(r==Bool(true)) return ℕt(true);
		if(r==Bool(false)) return ℕt(false);
	}
	return r;
}
Expression subtractionType(Expression t1, Expression t2){
	auto r=arithmeticType!false(t1,t2);
	return r==ℕt(true)?ℤt(true):r==ℕt(false)?ℤt(false):r;
}
Expression divisionType(Expression t1, Expression t2){
	auto r=arithmeticType!false(t1,t2);
	if(isFixedIntTy(r)) return null; // TODO: add a special operator for float and rat?
	return util.among(r,Bool(true),ℕt(true),ℤt(true))?ℚt(true):
		util.among(r,Bool(false),ℕt(false),ℤt(false))?ℚt(false):r;
}
Expression iDivType(Expression t1, Expression t2){
	auto r=arithmeticType!true(t1,t2);
	if((isEmpty(t1)||isEmpty(t2))&&!isFixedIntTy(r)) return bottom;
	auto isFixed1=isFixedIntTy(t1), isNumeric1=isNumeric(t1);
	auto isFixed2=isFixedIntTy(t2), isNumeric2=isNumeric(t2);
	if(isFixed1&&isNumeric2&&!isSubtype(t2,ℤt(false))) return null; // TODO: int/uint div ℚ/ℝ seems useful
	if(isFixed2&&isNumeric1&&!isSubtype(t1,ℤt(false))) return null; // TODO?
	auto isSigned1=isFixed1&&isFixed1.isSigned||isNumeric1&&!isSubtype(t1,ℕt(t1.isClassical()));
	auto isSigned2=isFixed2&&isFixed2.isSigned||isNumeric2&&!isSubtype(t2,ℕt(t2.isClassical()));
	if(isFixed2&&isSigned1&&!isSigned2) return null;
	if(isFixedIntTy(r)) return r;
	if(isFixed1||isFixed2) return null;
	if(cast(ℂTy)t1||cast(ℂTy)t2) return null;
	bool classical=t1.isClassical()&&t2.isClassical();
	if(cast(BoolTy)t1&&cast(BoolTy)t2) return Bool(classical);
	return (cast(BoolTy)t1||cast(ℕTy)t1)&&(cast(BoolTy)t2||cast(ℕTy)t2)?ℕt(classical):ℤt(classical);
}
Expression nSubType(Expression t1, Expression t2){
	if(!isEmpty(t1)&&!isEmpty(t2)){
		if(isSubtype(t1,Bool(false))&&isSubtype(t2,ℕt(false)))
			return Bool(t1.isClassical()&&t2.isClassical());
	}
	auto r=arithmeticType!true(t1,t2);
	if(auto fi=isFixedIntTy(r)){
		if(!fi.isSigned) return r;
		auto ce=cast(CallExp)r;
		assert(!!ce);
		auto id=cast(Identifier)ce.e;
		assert(!!id);
		auto ut=getFixedIntTy(fi.bits,false,fi.isClassical,r.loc,id.scope_); // TODO: do not require scope
		if(ut.sstate!=SemState.completed) return null;
		return ut;
	}
	if(isSubtype(r,ℕt(false))) return r;
	if(isSubtype(r,ℤt(false))) return ℕt(r.isClassical());
	return null;
}
Expression moduloType(Expression t1, Expression t2){
	if(!isEmpty(t1)&&!isEmpty(t2)){
		if(isSubtype(t1,Bool(false))&&isSubtype(t2,ℕt(true)))
			return Bool(t1.isClassical()&&t2.isClassical());
		if(isSubtype(t1,ℤt(true))&&isSubtype(t2,Bool(false)))
			return Bool(t1.isClassical()&&t2.isClassical());
	}
	auto r=arithmeticType!true(t1,t2);
	if(!r) return null;
	auto isFixed1=isFixedIntTy(t1), isNumeric1=isNumeric(t1);
	auto isFixed2=isFixedIntTy(t2), isNumeric2=isNumeric(t2);
	auto isSigned1=isFixed1&&isFixed1.isSigned||isNumeric1&&!isSubtype(t1,ℕt(t1.isClassical()));
	auto isSigned2=isFixed2&&isFixed2.isSigned||isNumeric2&&!isSubtype(t2,ℕt(t2.isClassical()));
	if(isFixed1&&!isSigned1&&isSigned2) return null;
	if(isSubtype(t1,ℤt(true))&&isSubtype(t2,ℕt(false)))
		return t2;
	return r;
}
Expression powerType(Expression t1, Expression t2){
	bool classical=t1.isClassical()&&t2.isClassical();
	if(!(isNumeric(t1)||isEmpty(t1))||!(isNumeric(t2)||isEmpty(t2))) return null;
	if(isEmpty(t1)) return bottom;
	if(cast(BoolTy)t1&&isSubtype(t2,ℕt(classical))) return Bool(classical);
	if(cast(ℕTy)t1&&isSubtype(t2,ℕt(classical))) return ℕt(classical);
	if(cast(ℤTy)t1&&isSubtype(t2,ℕt(classical))) return ℤt(classical);
	if(cast(ℂTy)t1||cast(ℂTy)t2) return ℂ(classical);
	if(util.among(t1,Bool(true),ℕt(true),ℤt(true),ℚt(true))&&isSubtype(t2,ℤt(false))) return ℚt(t2.isClassical);
	if(util.among(t1,Bool(false),ℕt(false),ℤt(false),ℚt(false))&&isSubtype(t2,ℤt(false))) return ℚt(false);
	return ℝ(classical); // TODO: good?
}
Expression minusType(Expression t){
	if(isFixedIntTy(t)) return t;
	if(!(isNumeric(t)||isEmpty(t))) return null;
	if(cast(BoolTy)t||cast(ℕTy)t) return ℤt(t.isClassical());
	return t;
}
Expression bitNotType(Expression t){
	if(isFixedIntTy(t)) return t;
	if(!(isNumeric(t)||isEmpty(t))) return null;
	if(cast(ℕTy)t) return ℤt(t.isClassical());
	return t;
}
Expression notType(Expression t){
	if(!t||!(cast(BoolTy)t||isEmpty(t))) return null;
	return t;
}
Expression logicType(Expression t1,Expression t2){
	if(!(cast(BoolTy)t1||isEmpty(t1))||!(cast(BoolTy)t2||isEmpty(t2))) return null;
	return Bool(t1.isClassical()&&t2.isClassical());
}
Expression bitwiseType(Expression t1,Expression t2){
	auto r=arithmeticType!true(t1,t2);
	if(isEmpty(r)) return r;
	if(!isFixedIntTy(r)&&!isSubtype(r,ℤt(false))) // TODO?
	   return null;
	return r;
}

Expression bitAndType(Expression t1,Expression t2){
	auto isClassical=t1.isClassical()&&t2.isClassical();
	if(cast(BoolTy)t1&&isSubtype(t2,ℤt(true))||isSubtype(t1,ℤt(true))&&cast(BoolTy)t2)
		return Bool(isClassical);
	auto r=bitwiseType(t1,t2);
	if(!r) return null;
	if(isNumeric(r)&&(cast(ℕTy)t1||cast(ℕTy)t2))
		return ℕt(r.isClassical());
	return r;
}
Expression cmpType(Expression t1,Expression t2){
	if(isEmpty(t1)&&isEmpty(t2)) return bottom;
	if(isEmpty(t1)||isEmpty(t2)) t1=t2=joinTypes(t1,t2);
	if(isFixedIntTy(t1) || isFixedIntTy(t2)){
		if(!(joinTypes(t1,t2)||isNumeric(t1)||isNumeric(t2)))
			return null;
	}else{
		auto a1=cast(ArrayTy)t1,a2=cast(ArrayTy)t2;
		auto v1=cast(VectorTy)t1,v2=cast(VectorTy)t2;
		Expression n1=a1?a1.next:v1?v1.next:null,n2=a2?a2.next:v2?v2.next:null;
		if(n1&&n2) return cmpType(n1,n2);
		auto tpl1=t1.isTupleTy();
		auto tpl2=t2.isTupleTy();
		if(tpl1&&tpl2){
			Expression r=Bool(true);
			// different tuple length has canonical
			// meaning (just like for arrays)
			// TODO: this may be confusing?
			// if(tpl1.length!=tpl2.length) return null;
			foreach(i;0..min(tpl1.length,tpl2.length)){
				auto ct=cmpType(tpl1[i],tpl2[i]);
				if(!ct) return null;
				r=logicType(r,ct);
				if(!r) return null;
			}
			return r;
		}
		if(tpl1&&n2){
			Expression r=Bool(true);
			foreach(i;0..tpl1.length){
				auto ct=cmpType(tpl1[i],n2);
				if(!ct) return null;
				r=logicType(r,ct);
				if(!r) return null;
			}
			return r;
		}
		if(n1&&tpl2){
			Expression r=Bool(true);
			foreach(i;0..tpl2.length){
				auto ct=cmpType(n1,tpl2[i]);
				if(!ct) return null;
				r=logicType(r,ct);
				if(!r) return null;
			}
			return r;
		}
		if(!isNumeric(t1)||!isNumeric(t2)||cast(ℂTy)t1||cast(ℂTy)t2) return null;
	}
	return Bool(t1.isClassical()&&t2.isClassical());
}

private Expression handleUnary(alias determineType)(string name,Expression e,ref Expression e1,ExpSemContext context){
	e1=expressionSemantic(e1,context.nestConst);
	propErr(e1,e);
	if(e.sstate==SemState.error)
		return e;
	e.type=determineType(e1.type?e1.type.eval():null);
	if(!e.type){
		context.sc.error(format("incompatible type %s for %s",e1.type,name),e.loc);
		e.sstate=SemState.error;
	}
	if(e.sstate!=SemState.error) e.sstate=SemState.completed;
	return e;
}

Expression expressionSemanticImpl(UMinusExp ume,ExpSemContext context){
	return handleUnary!minusType("minus",ume,ume.e,context);
}
Expression expressionSemanticImpl(UNotExp une,ExpSemContext context){
	auto sc=context.sc;
	une.e=expressionSemantic(une.e,context.nestConst);
	static if(language==silq){
		if(auto id=cast(Identifier)une.e)
			if(isPreludeSymbol(id)==PreludeSymbol.Z)
				return ℤt(true);
	}
	static if(language==silq) if(isType(une.e)||isQNumeric(une.e)){
		if(auto ty=isQNumeric(une.e)?une.e:typeSemantic(une.e,sc)){
			if(ty.sstate==SemState.completed){
				if(auto r=ty.getClassical()){
					return typeSemantic(r,sc);
				}else{
					// TODO: have explicit ClassicalTy
					sc.error(format("cannot make type %s classical",une.e),une.loc);
					une.sstate=SemState.error;
					return une;
				}
			}
		}
	}
	return handleUnary!notType("not",une,une.e,context);
}
Expression expressionSemanticImpl(UBitNotExp ubne,ExpSemContext context){
	return handleUnary!bitNotType("bitwise not",ubne,ubne.e,context);
}

private Expression handleBinary(alias determineType)(string name,Expression e,ref Expression e1,ref Expression e2,ExpSemContext context){
	auto sc=context.sc;
	e1=expressionSemantic(e1,context.nestConst);
	e2=expressionSemantic(e2,context.nestConst);
	propErr(e1,e);
	propErr(e2,e);
	if(e.sstate==SemState.error)
		return e;
	if((isType(e1)||isQNumeric(e1))&&name=="power"){
		if(isEmpty(e1)) return bottom;
		if(!isSubtype(e2.type,ℕt(true))){
			sc.error(format("vector length should be of type !ℕ, not %s",e2.type), e2.loc);
			e.sstate=SemState.error;
		}else return vectorTy(e1,e2);
	}else{
		e.type = determineType(e1.type?e1.type.eval():null,e2.type?e2.type.eval():null);
		if(!e.type){
			if(e1.type&&e2.type)
				sc.error(format("incompatible types %s and %s for %s",e1.type,e2.type,name),e.loc);
			e.sstate=SemState.error;
		}
	}
	if(e.sstate!=SemState.error) e.sstate=SemState.completed;
	return e;
}

Expression expressionSemanticImpl(AddExp ae,ExpSemContext context){
	return handleBinary!(arithmeticType!false)("addition",ae,ae.e1,ae.e2,context);
}
Expression expressionSemanticImpl(SubExp se,ExpSemContext context){
	return handleBinary!subtractionType("subtraction",se,se.e1,se.e2,context);
}
Expression expressionSemanticImpl(NSubExp nse,ExpSemContext context){
	return handleBinary!nSubType("natural subtraction",nse,nse.e1,nse.e2,context);
}
Expression expressionSemanticImpl(MulExp me,ExpSemContext context){
	return handleBinary!(arithmeticType!true)("multiplication",me,me.e1,me.e2,context);
}
Expression expressionSemanticImpl(DivExp de,ExpSemContext context){
	return handleBinary!divisionType("division",de,de.e1,de.e2,context);
}
Expression expressionSemanticImpl(IDivExp ide,ExpSemContext context){
	return handleBinary!iDivType("integer division",ide,ide.e1,ide.e2,context);
}
Expression expressionSemanticImpl(ModExp me,ExpSemContext context){
	return handleBinary!moduloType("modulo",me,me.e1,me.e2,context);
}
Expression expressionSemanticImpl(PowExp pe,ExpSemContext context){
	return handleBinary!powerType("power",pe,pe.e1,pe.e2,context);
}
Expression expressionSemanticImpl(BitOrExp boe,ExpSemContext context){
	return handleBinary!bitwiseType("bitwise or",boe,boe.e1,boe.e2,context);
}
Expression expressionSemanticImpl(BitXorExp bxe,ExpSemContext context){
	return handleBinary!bitwiseType("bitwise xor",bxe,bxe.e1,bxe.e2,context);
}
Expression expressionSemanticImpl(BitAndExp bae,ExpSemContext context){
	return handleBinary!bitAndType("bitwise and",bae,bae.e1,bae.e2,context);
}

Expression handleLogic(string name,ALogicExp e,ref Expression e1,ref Expression e2,ExpSemContext context){
	auto sc=context.sc, inType=context.inType;
	e1=expressionSemantic(e1,context.nestConst);
	static if(language==silq){
		auto quantumControl=e1.type&&!e1.type.eval().isClassical();
		auto restriction_=quantumControl?Annotation.mfree:Annotation.none;
	}else{
		enum quantumControl=false;
		enum restriction_=Annotation.none;
	}
	// initialize scopes, to allow captures to be inserted
	e.blscope_=new BlockScope(sc,restriction_);
	e.forgetScope=new BlockScope(sc,restriction_);
	e2=branchSemantic(e2,ExpSemContext(e.blscope_,ConstResult.yes,inType),quantumControl);
	static if(language==silq) e.blscope_.clearConsumed();
	propErr(e1,e);
	propErr(e2,e);
	if(e.sstate!=SemState.error){
		e.type = logicType(e1.type?e1.type.eval():null,e2.type?e2.type.eval():null);
		if(!e.type){
			if(e1.type&&e2.type)
				sc.error(format("incompatible types %s and %s for %s",e1.type,e2.type,name),e.loc);
			e.sstate=SemState.error;
		}
	}
	if(sc.merge(quantumControl,e.blscope_,e.forgetScope)){
		sc.note(text("consumed in one branch of ",name), e.loc);
		e.sstate=SemState.error;
	}
	if(inType){
		e.blscope_=null;
		e.forgetScope=null;
	}
	if(e.sstate!=SemState.error) e.sstate=SemState.completed;
	return e;
}

Expression expressionSemanticImpl(AndExp ae,ExpSemContext context){
	return handleLogic("conjunction",ae,ae.e1,ae.e2,context);
}
Expression expressionSemanticImpl(OrExp oe,ExpSemContext context){
	return handleLogic("disjunction",oe,oe.e1,oe.e2,context);
}

Expression expressionSemanticImpl(LtExp le,ExpSemContext context){
	return handleBinary!cmpType("'<'",le,le.e1,le.e2,context);
}
Expression expressionSemanticImpl(LeExp le,ExpSemContext context){
	return handleBinary!cmpType("'≤'",le,le.e1,le.e2,context);
}
Expression expressionSemanticImpl(GtExp ge,ExpSemContext context){
	return handleBinary!cmpType("'>'",ge,ge.e1,ge.e2,context);
}
Expression expressionSemanticImpl(GeExp ge,ExpSemContext context){
	return handleBinary!cmpType("'≥'",ge,ge.e1,ge.e2,context);
}
Expression expressionSemanticImpl(EqExp eq,ExpSemContext context){
	return handleBinary!cmpType("'='",eq,eq.e1,eq.e2,context);
}
Expression expressionSemanticImpl(NeqExp ne,ExpSemContext context){
	return handleBinary!cmpType("'≠'",ne,ne.e1,ne.e2,context);
}

Expression concatType(Expression t1,Expression t2){
	if(isEmpty(t1)&&isEmpty(t2)) return bottom;
	if(isEmpty(t1)){
		if(cast(ArrayTy)t2) return t2;
		return bottom;
	}
	if(isEmpty(t2)){
		if(cast(ArrayTy)t1) return t1;
		return bottom;
	}
	if(t1==unit||t2==unit){
		auto ntype=t1==unit?t2:t1;
		if(cast(ArrayTy)ntype||cast(VectorTy)ntype||cast(TupleTy)ntype)
			return ntype;
	}else{
		auto tt1=t1.isTupleTy(),tt2=t2.isTupleTy();
		if(tt1&&tt2){
			return tupleTy(chain(iota(tt1.length).map!(i=>tt1[i]),
			                     iota(tt2.length).map!(i=>tt2[i])).array);
		}
		auto vt1=cast(VectorTy)t1,vt2=cast(VectorTy)t2;
		if(vt1&&vt2){
			if(auto netype=joinTypes(vt1.next,vt2.next)){
				auto add=new AddExp(vt1.num,vt2.num);
				add.type=ℕt(true);
				add.sstate=SemState.completed;
				return vectorTy(netype,add.eval()); // TODO: evaluation context
			}
		}
		if(vt1&&tt2){
			if(auto at=cast(ArrayTy)joinTypes(arrayTy(vt1.next),t2)){
				auto add=new AddExp(vt1.num,LiteralExp.makeInteger(tt2.length));
				add.type=ℕt(true);
				add.sstate=SemState.completed;
				return vectorTy(at.next,add);
			}
		}
		if(tt1&&vt2){
			if(auto at=cast(ArrayTy)joinTypes(t1,arrayTy(vt2.next))){
				auto add=new AddExp(LiteralExp.makeInteger(tt1.length),vt2.num);
				add.type=ℕt(true);
				add.sstate=SemState.completed;
				return vectorTy(at.next,add);
			}
		}
		if(auto at=cast(ArrayTy)joinTypes(t1,t2))
			return at;
	}
	return null;
}

Expression expressionSemanticImpl(CatExp ce,ExpSemContext context){
	auto sc=context.sc;
	ce.e1=expressionSemantic(ce.e1,context);
	ce.e2=expressionSemantic(ce.e2,context);
	propErr(ce.e1,ce);
	propErr(ce.e2,ce);
	if(ce.sstate==SemState.error)
		return ce;
	assert(!ce.type);
	ce.type=concatType(ce.e1.type.eval(),ce.e2.type.eval());
	if(!ce.type){
		sc.error(format("incompatible types %s and %s for ~",ce.e1.type,ce.e2.type),ce.loc);
		ce.sstate=SemState.error;
	}
	return ce;
}

Expression resolveWildcards(Expression wildcards,Expression analyzed){
	// TODO: improve
	if(auto pow=cast(PowExp)wildcards){
		if(cast(WildcardExp)pow.e1){
			Expression elemTy=null;
			if(auto aty=cast(ArrayTy)analyzed)
				elemTy=aty.next;
			if(auto vty=cast(VectorTy)analyzed)
				elemTy=vty.next;
			if(auto tpl=analyzed.isTupleTy){
				import util.maybe:mfold;
				if(new EqExp(pow.e2,LiteralExp.makeInteger(tpl.length)).eval().asIntegerConstant.mfold!(z=>z==1,()=>false)){
					return analyzed; // TODO: revisit
				}
				foreach(i;0..tpl.length){
					elemTy=joinTypes(elemTy, tpl[i]);
					if(!elemTy) break;
				}
			}
			if(!elemTy) return null;
			auto npow=new PowExp(elemTy,pow.e2);
			npow.loc=pow.loc;
			return npow;
		}
	}
	return null;
}

Expression expressionSemanticImpl(WildcardExp we,ExpSemContext context){
	if(we.sstate!=SemState.error){
		context.sc.error("unable to determine type",we.loc);
		we.sstate=SemState.error;
	}
	return we;
}

Expression expressionSemanticImpl(TypeofExp ty,ExpSemContext context){
	auto sc=context.sc;
	auto scopeState=sc.getStateSnapshot(true);
	scope(exit) sc.restoreStateSnapshot(scopeState);
	auto ncontext=context;
	ncontext.inType=InType.no;
	ty.e=expressionSemantic(ty.e,ncontext.nestConsumed);
	propErr(ty.e,ty);
	if(ty.sstate==SemState.error)
		return ty;
	assert(ty.e.type&&ty.e.type.sstate==SemState.completed);
	return ty.e.type;
}

Expression expressionSemanticImpl(BinaryExp!(Tok!"×") pr,ExpSemContext context){
	auto sc=context.sc;
	// TODO: allow nested declarations
	pr.type=typeTy; // TODO: ok?
	auto t1=typeSemantic(pr.e1,sc,true);
	auto t2=typeSemantic(pr.e2,sc,true);
	if(!t1||!t2){
		pr.sstate=SemState.error;
		return pr;
	}
	auto l=t1.isTupleTy(),r=t2.isTupleTy();
	auto merge1=!pr.e1.brackets&&l&&l.length&&cast(BinaryExp!(Tok!"×"))pr.e1;
	auto merge2=!pr.e2.brackets&&r&&r.length&&cast(BinaryExp!(Tok!"×"))pr.e2;
	if(merge1 && merge2)
		return tupleTy(chain(iota(l.length).map!(i=>l[i]),iota(r.length).map!(i=>r[i])).array);
	if(merge1) return tupleTy(chain(iota(l.length).map!(i=>l[i]),only(t2)).array);
	if(merge2) return tupleTy(chain(only(t1),iota(r.length).map!(i=>r[i])).array);
	return tupleTy([t1,t2]);
}

Expression expressionSemanticImpl(BinaryExp!(Tok!"→") ex,ExpSemContext context){
	auto sc=context.sc;
	ex.type=typeTy; // TODO: ok?
	Q!(bool[],Expression) getConstAndType(Expression e){
		Q!(bool[],Expression) base(Expression e){
			static if(language==silq){
				if(auto ce=cast(UnaryExp!(Tok!"const"))e){
					return q([true],typeSemantic(ce.e,sc));
				}
				if(auto ce=cast(UnaryExp!(Tok!"moved"))e){
					return q([false],typeSemantic(ce.e,sc));
				}
			}
			auto ty=typeSemantic(e,sc);
			return q([ex.isLifted],ty);
		}
		if(auto pr=cast(BinaryExp!(Tok!"×"))e){
			auto merge1=!pr.e1.brackets&&cast(BinaryExp!(Tok!"×"))pr.e1;
			auto t1=merge1?getConstAndType(pr.e1):base(pr.e1);
			auto merge2=!pr.e2.brackets&&cast(BinaryExp!(Tok!"×"))pr.e2;
			auto t2=merge2?getConstAndType(pr.e2):base(pr.e2);
			if(!t1[1]||!t2[1]){
				e.sstate=SemState.error;
				return q((bool[]).init,Expression.init);
			}
			auto l=t1[1].isTupleTy(),r=t2[1].isTupleTy();
			merge1&=l&&l.length;
			merge2&=r&&r.length;
			if(merge1 && merge2)
				return q(t1[0]~t2[0],cast(Expression)tupleTy(chain(iota(l.length).map!(i=>l[i]),iota(r.length).map!(i=>r[i])).array));
			if(merge1) return q(t1[0]~t2[0],cast(Expression)tupleTy(chain(iota(l.length).map!(i=>l[i]),only(t2[1])).array));
			if(merge2) return q(t1[0]~t2[0],cast(Expression)tupleTy(chain(only(t1[1]),iota(r.length).map!(i=>r[i])).array));
			return q(t1[0]~t2[0],cast(Expression)tupleTy([t1[1],t2[1]]));
		}
		return base(e);
	}
	auto t1=getConstAndType(ex.e1);
	auto t2=typeSemantic(ex.e2,sc);
	if(!t1[1]||!t2){
		ex.sstate=SemState.error;
		return ex;
	}
	return funTy(t1[0],t1[1],t2,false,!!t1[1].isTupleTy()&&t1[0].length!=1,ex.annotation,false);
}

Expression expressionSemanticImpl(RawProductTy fa,ExpSemContext context){
	auto sc=context.sc;
	fa.type=typeTy; // TODO: ok?
	auto fsc=new RawProductScope(sc,fa.annotation);
	scope(exit) fsc.forceClose();
	declareParameters(fa,fa.isSquare,fa.params,fsc); // parameter variables
	auto cod=typeSemantic(fa.cod,fsc);
	propErr(fa.cod,fa);
	if(fa.sstate==SemState.error) return fa;
	auto const_=fa.params.map!(p=>p.isConst).array;
	auto names=fa.params.map!(p=>p.getId).array;
	auto types=fa.params.map!(p=>p.vtype).array;
	assert(fa.isTuple||types.length==1);
	auto dom=fa.isTuple?tupleTy(types):types[0];
	return productTy(const_,names,dom,cod,fa.isSquare,fa.isTuple,fa.annotation,false);
}

Expression expressionSemanticImpl(RawVariadicTy va,ExpSemContext context){
	auto sc=context.sc;
	va.type=typeTy; // TODO: ok?
	auto next=expressionSemantic(va.next,expSemContext(context.sc,ConstResult.yes,InType.yes));
	if(auto tpl=cast(TupleTy)next.type){
		if(!tpl.types.all!(t=>isType(t)||isQNumeric(t))){
			sc.error("argument to variadic type must be a tuple of types",va.loc);
			sc.note(format("type of argument is '%s'",next.type),va.next.loc);
			sc.note(format("a '%s' is not a type",tpl.types.filter!(t=>!(isType(t)||isQNumeric(t)))),va.loc);
			va.sstate=SemState.error;
			return va;
		}
	}else if(auto et=elementType(next.type)){
		if(!(isType(et)||isQNumeric(et))){
			sc.error("argument to variadic type must have element type that is a type",va.loc);
			sc.note(format("type of argument is '%s'",next.type),va.next.loc);
			sc.note(format("a '%s' is not a type",et),va.loc);
			va.sstate=SemState.error;
			return va;
		}
	}else{
		sc.error("argument to variadic type must be a tuple, vector, or array",va.loc);
		sc.note(format("type of argument is '%s'",next.type),va.next.loc);
		va.sstate=SemState.error;
		return va;
	}
	return variadicTy(next,false);
}

Expression expressionSemanticImplDefault(Expression expr,ExpSemContext context){
	auto sc=context.sc;
	bool ok=false;
	if(auto ce=cast(CommaExp)expr){
		sc.error("nested comma expressions are disallowed",ce.loc);
		ok=true;
	}
	static if(language==silq){
		if(!ok){
			if(auto ce=cast(UnaryExp!(Tok!"const"))expr){
				sc.error("invalid 'const' annotation (note that 'const' goes before parameter names)", ce.loc);
				ok=true;
			}
			if(auto ce=cast(UnaryExp!(Tok!"moved"))expr){
				sc.error("invalid 'moved' annotation (note that 'moved' goes before parameter names)", ce.loc);
				ok=true;
			}
		}
	}
	if(!ok){
		if(expr.kind=="expression"){ sc.error("not supported as an expression",expr.loc); }
		else sc.error(expr.kind~" cannot appear within an expression",expr.loc);
	}
	expr.sstate=SemState.error;
	return expr;
}

Expression expressionSemantic(Expression expr,ExpSemContext context){
	auto sc=context.sc;
	if(expr.sstate==SemState.completed||expr.sstate==SemState.error) return expr;
	assert(expr.sstate==SemState.initial||cast(Identifier)expr&&expr.sstate==SemState.started);
	auto constSave=sc.saveConst(); // TODO: make this faster?
	scope(success){
		static if(language==silq){
			if(!context.constResult||!expr.type||expr.type.isClassical())
				sc.resetConst(constSave); // TODO: tie to forgettability
			if(expr.sstate!=SemState.error){
				assert(!!expr.type,text(expr," ",expr.type));
				if(auto id=cast(Identifier)expr){
					auto consumesIdentifier=!id.constLookup&&id.meaning;
					if(context.inType&&consumesIdentifier){
						sc.error("cannot consume variables within types",expr.loc);
						expr.sstate=SemState.error;
					}
				}else{
					expr.constLookup=context.constResult;
					if(expr.constLookup&&!expr.isLifted(sc)&&!expr.type.isClassical()){
						sc.error("non-'lifted' quantum expression must be consumed",expr.loc);
						expr.sstate=SemState.error;
					}
				}
				if(expr.sstate!=SemState.error) expr.sstate=SemState.completed;
			}else expr.constLookup=context.constResult;
			if(expr.type&&unrealizable(expr.type)){
				sc.error(format("instances of type '%s' not realizable (did you mean to use '!%s'?)",expr.type,expr.type),expr.loc);
				expr.sstate=SemState.error;
			}
		}else{
			if(expr&&expr.sstate!=SemState.error){
				assert(!!expr.type);
				expr.sstate=SemState.completed;
			}
		}
	}
	return expr=expr.dispatchExp!(expressionSemanticImpl,expressionSemanticImplDefault,true)(context);
}


bool setFtype(FunctionDef fd,bool force){
	if(fd.ftype&&fd.ftypeFinal) return true;
	if(fd.isNested&&!force&&!fd.sealed)
		return false;
	if(fd.sstate!=SemState.error&&(!fd.fscope_||fd.params.any!(p=>!p.vtype)))
		return false;
	bool[] pc;
	Id[] pn;
	Expression[] pty;
	foreach(p;fd.params){
		if(!p.vtype){
			assert(fd.sstate==SemState.error);
			return false;
		}
		pc~=p.isConst;
		pn~=p.getId;
		pty~=p.vtype;
	}
	assert(fd.isTuple||pty.length==1);
	auto pt=fd.isTuple?tupleTy(pty):pty[0];
	auto ftypeBefore=fd.ftype;
	fd.ftype=productTy(pc,pn,pt,fd.ret?fd.ret:bottom,fd.isSquare,fd.isTuple,fd.annotation,!fd.context||fd.context.vtype==contextTy(true));
	fd.seal();
	if(fd.retNames.length!=fd.numReturns)
		fd.retNames = new string[](fd.numReturns);
	if(ftypeBefore!=fd.ftype){
		//imported!"util.io".writeln("CALLING FTYPE CALLBACKS FOR: ",fd," ",fd.ftype," ",ftypeBefore," ",fd.ftypeCallbacks.length);
		foreach(callback;fd.ftypeCallbacks)
			callback(fd.ftype);
	}
	if(fd.ftypeFinal)
		fd.ftypeCallbacks=[];
	return true;
}

bool subscribeToTypeUpdates(Declaration meaning,Scope sc,Location loc){
	if(!sc) return false;
	if(auto fd=cast(FunctionDef)meaning){
		if(!fd.ftypeFinal){
			auto cfd=sc.getFunction();
			if(!cfd){
				sc.error("invalid forward reference",loc);
				if(fd&&!fd.rret)
					sc.note("possibly caused by missing return type annotation",fd.loc);
				return false;
			}else{
				if(cfd.scope_.isNestedIn(fd.fscope_)) cfd=fd; // TODO: ok?
				//imported!"util.io".writeln("adding ",cfd," to ",fd);
				if(!fd.functionDefsToUpdate.canFind(cfd)){ // TODO: make more efficient?
					fd.functionDefsToUpdate~=cfd;
					cfd.numUpdatesPending+=1;
				}
				cfd.unsealed=true;
			}
		}
	}
	return true;
}


FunctionDef functionDefSemantic(FunctionDef fd,Scope sc){
	if(fd.sstate==SemState.completed||fd.sstate==SemState.error) return fd;
	if(!fd.fscope_) fd=cast(FunctionDef)presemantic(fd,sc); // TODO: why does checking for fd.scope_ not work? (test3.slq)
	if(fd.sstate==SemState.completed||fd.body_&&fd.body_.sstate==SemState.completed) return fd;
	if(fd.sstate==SemState.started) return fd; // only one active semantic analysis at one time
	if(fd.sstate!=SemState.error) fd.sstate=SemState.started;
	auto ftypeBefore=fd.ftype;
	auto numCapturesBefore=fd.capturedDecls.filter!(d=>d.isLinear).walkLength; // TODO: really needed?
	fd.inferringReturnType|=!fd.ret;
	//imported!"util.io".writeln("STARTING: ",fd," ",fd.ftype," ",fd.ret," ",fd.rret," ",fd.inferringReturnType);
	if(!fd.ret){
		fd.ret=bottom;
		setFtype(fd,true);
	}
	if(fd.inferringReturnType){
		if(fd.rret&&!fd.origRret) fd.origRret=fd.rret.copy();
	}
	if(fd.body_&&!fd.origBody_) fd.origBody_=fd.body_.copy();
	auto fsc=fd.fscope_;
	assert(!!fsc,text(fd));
	assert(fsc.allowsLinear());
	auto bdy=fd.body_?compoundExpSemantic(fd.body_,fsc):null;
	fd.body_=bdy;
	fd.type=unit;
	if(bdy){
		propErr(bdy,fd);
		if(!definitelyReturns(bdy)){
			if(!fd.ret || fd.ret == unit || fd.inferringReturnType&&fd.ret==bottom){
				auto tpl=new TupleExp([]);
				tpl.loc=fd.loc;
				auto rete=new ReturnExp(tpl);
				rete.loc=fd.loc;
				fd.body_.s~=returnExpSemantic(rete,fd.body_.blscope_);
			}else{
				sc.error("control flow might reach end of function (add return or assert(false) statement)",fd.loc);
				fd.sstate=SemState.error;
			}
		}
	}
	if(!fd.ret){
		fd.ret=bottom;
		if(fd.rret) fd.unsealed=true;
	}
	if(!setFtype(fd,true))
		fd.sstate=SemState.error;
	static if(language==silq) fsc.clearConsumed();
	if(fd.ftype&&fd.sstate!=SemState.error){
		foreach(id;fd.ftype.freeIdentifiers){
			assert(!!id.meaning,text(id));
			if(cast(DatDecl)id.meaning) continue; // allow nested types to be returned from functions
			if(id.meaning.scope_.isNestedIn(fsc)){
				fsc.error(format("local variable '%s' appears in return type '%s'%s (maybe declare '%s' in the enclosing scope?)", id.name, fd.ftype.cod, fd.name?format(" of function '%s'",fd.name):"",id.name), fd.loc);
				fd.sstate=SemState.error;
			}
			typeConstBlock(id.meaning,fd,sc);
		}
	}
	if(bdy){
		if(fsc.merge(false,bdy.blscope_)||fsc.closeUnreachable(null)) fd.sstate=SemState.error;
	}else{
		fsc.forceClose();
	}
	if(!fd.sealed) fd.seal();
	if(fd.unsealed||fd.numUpdatesPending!=0){
		fd.sealed=false;
		fd.unsealed=false;
	}else{
		fd.ftypeFinal=true;
		fd.inferringReturnType=false;
		fd.inferAnnotation=false;
	}
	if(fd.ftypeFinal){
		foreach(ref n;fd.retNames){
			if(n is null) n="r";
			else n=n.stripRight('\'');
		}
		void[0][string] vars;
		foreach(p;fd.params) vars[p.getName]=[];
		int[string] counts1,counts2;
		foreach(n;fd.retNames)
			++counts1[n];
		foreach(ref n;fd.retNames){
			if(counts1[n]>1)
				n~=lowNum(++counts2[n]);
			while(n in vars) n~="'";
			vars[n]=[];
		}
		if(fd.sstate!=SemState.error)
			fd.sstate=SemState.completed;
	}
	static void resetFunction(FunctionDef fd,FunctionDef cause)in{
		//imported!"util.io".writeln("RESETTING: ",fd," FROM ",cause);
		assert(fd.sstate!=SemState.completed);
		assert(fd.sstate!=SemState.error);
	}do{
		auto crepls=fd.scope_.allComponentReplacements();
		foreach(i,crepl;crepls){ // reset component replacements
			static assert(is(typeof(crepl):T*,T));
			if(!crepl.read) continue;
			if(auto id=getIdFromIndex(crepl.read)){
				if(id.scope_&&id.scope_.isNestedIn(fd.fscope_))
					crepl.read=null;
			}
		}
		if(fd.sealed) fd.unseal();
		if(fd.origRret) fd.rret=fd.origRret.copy();
		assert(!!fd.origBody_);
		fd.body_=fd.origBody_.copy();
		auto oldfscope_=fd.fscope_;
		fd.fscope_=new FunctionScope(fd.scope_,fd);
		fd.sstate=SemState.initial;
		foreach(p;fd.params){
			p.splitInto=[];
			assert(p.scope_ is oldfscope_);
			p.scope_=null;
			fd.fscope_.insert(p);
		}
		Declaration[] ncapturedDecls;
		Identifier[][Declaration] ncaptures;
		foreach(capture;fd.capturedDecls){ // undo consumption of captures
			auto ocapture=capture;
			while(ocapture.scope_.isNestedIn(oldfscope_)){
				ocapture=ocapture.splitFrom;
			}
			ocapture.splitInto=ocapture.splitInto.filter!(x=>!x.scope_.isNestedIn(oldfscope_)).array;
			if(capture.isLinear&&!fd.scope_.lookupHere(capture.name,false,Lookup.probing)){
				assert(ocapture.scope_ is fd.scope_); // TODO: ok?
				//imported!"util.io".writeln("INSERTING: ",capture);
				ocapture.scope_=null;
				fd.scope_.unconsume(ocapture);
				fd.fscope_.symtabInsert(ocapture);
			}
			auto loc=fd.captures[capture][0].loc;
			auto id=new Identifier(capture.getName);
			id.loc=loc;
			id.meaning=capture.isLinear?fd.fscope_.split(ocapture):ocapture;
			id.type=id.typeFromMeaning;
			id.constLookup=false;
			id.sstate=id.type?SemState.completed:SemState.error;
			propErr(id,fd);
			if(id.meaning){
				ncapturedDecls~=id.meaning;
				ncaptures[id.meaning]~=id;
			}
		}
		fd.captures=ncaptures;
		fd.capturedDecls=ncapturedDecls;
		fd.context=null;
		fd.thisVar=null;
		prepareFunctionDef(fd,fd.scope_);
		if(fd.capturedDecls.any!(d=>d.isLinear)){
			assert(!!fd.context);
			fd.context.vtype=contextTy(false);
		}
	}
	auto functionDefsToUpdate=fd.functionDefsToUpdate;
	auto numCapturesAfter=fd.capturedDecls.filter!(d=>d.isLinear).walkLength;
	static void resetFunctionDefsToUpdate()(FunctionDef fd){
		foreach(ofd;fd.functionDefsToUpdate)
			notify(ofd,fd);
		fd.functionDefsToUpdate=[];
	}
	static void finalize()(FunctionDef fd){
		if(fd.sstate==SemState.error) return;
		//ximported!"util.io".writeln("FINALIZING: ",fd," ",fd.ftype," ",fd.functionDefsToUpdate.length," ",fd.numUpdatesPending);
		if(fd.ftypeFinal){
			fd.sstate=SemState.completed;
			resetFunctionDefsToUpdate(fd);
		}else fd.sstate=SemState.passive;
	}
	static void notify(FunctionDef fd,FunctionDef ufd){
		assert(fd.numUpdatesPending>0);
		if(--fd.numUpdatesPending==0){
			if(fd.sstate!=SemState.started){ // semantic analysis is still active
				fd.ftypeFinal=true;
				fd.inferringReturnType=false;
				fd.inferAnnotation=false;
				finalize(fd);
			}
		}
	}
	if(fd.sstate!=SemState.error&&(fd.ftype!=ftypeBefore&&(ftypeBefore||functionDefsToUpdate.length)||numCapturesAfter!=numCapturesBefore)){
		//imported!"util.io".writeln("NOTIFYING: ",fd," ",ftypeBefore," ⇒ ",fd.ftype," ",numCapturesBefore," ⇒ ",numCapturesAfter);
		if(fd.sstate!=SemState.completed) resetFunction(fd,fd);
		//imported!"util.io".writeln("end of ",fd," ftypeBefore: ",ftypeBefore," ftype: ",fd.ftype," equal: ",ftypeBefore==fd.ftype," to update: ",functionDefsToUpdate);
		if(fd.ftype!=ftypeBefore) foreach(ufd;functionDefsToUpdate){
			if(ufd.sstate==SemState.error) continue;
			if(ufd is fd) continue;
			while(ufd&&ufd.sstate==SemState.completed)
				ufd=ufd.scope_.getFunction();
			if(!ufd||!ufd.inferringReturnType&&!ufd.inferAnnotation) continue; // TODO: needed?
			assert(!ufd.ftypeFinal);
			assert(!!ufd.scope_);
			resetFunction(ufd,fd);
			//imported!"util.io".writeln("REANALYZING: ",ufd," ",ufd.ftype," BECAUSE OF ",fd," ",fd.ftype," ",ftypeBefore," ",functionDefsToUpdate.length);
			auto nufd=functionDefSemantic(ufd,ufd.scope_);
			assert(nufd is ufd);
		}
		return functionDefSemantic(fd,sc);
	}
	finalize(fd);
	return fd;
}

DatDecl datDeclSemantic(DatDecl dat,Scope sc){
	bool success=true;
	if(!dat.dscope_) presemantic(dat,sc);
	auto bdy=compoundDeclSemantic(dat.body_,dat.dscope_);
	assert(!!bdy);
	dat.body_=bdy;
	dat.type=unit;
	if(dat.sstate!=SemState.error) dat.sstate=SemState.completed;
	return dat;
}

void determineType(ref Expression e,ExpSemContext context,void delegate(Expression) future,bool force,Location loc){
	if(e.type) return future(e.type);
	void handleFunctionDef(FunctionDef fd)in{
		assert(fd&&fd.scope_);
	}do{
		setFtype(fd,force);
		if(fd.ftype) return future(fd.ftype);
		if(!fd.ftypeFinal){
			fd.ftypeCallbacks~=future;
			//imported!"util.io".writeln("CALLBACK ADDED TO: ",fd," ",fd.ftype," ",fd.ftypeFinal," ",e.loc);
		}
	}
	if(auto le=cast(LambdaExp)e){
		assert(!!le.fd);
		if(!le.fd.scope_&&context.sc){
			le.fd.scope_=context.sc;
			le.fd=cast(FunctionDef)presemantic(le.fd,context.sc);
			assert(!!le.fd);
		}
		return handleFunctionDef(le.fd);
	}
	if(auto id=cast(Identifier)e)
		if(auto fd=cast(FunctionDef)id.meaning)
			if(fd.scope_)
				return handleFunctionDef(fd);
	if(!context.sc) return;
	e=expressionSemantic(e,context);
	return future(e.type);
}

ReturnExp returnExpSemantic(ReturnExp ret,Scope sc){
	if(ret.sstate==SemState.completed) return ret;
	if(ret.sstate==SemState.started) return ret;
	ret.sstate=SemState.started;
	auto fd=sc.getFunction();
	if(!fd){
		sc.error("return statement must be within function",ret.loc);
		ret.sstate=SemState.error;
		return ret;
	}
	auto context=expSemContext(sc,ConstResult.no,InType.no);
	static if(language==silq) auto bottom=Dependency(); // variable is a workaround for DMD regression

	bool widenReturnType(Expression type){
		if(fd.ret&&isSubtype(type,fd.ret))
			return true;
		if(!fd.inferringReturnType){
			//imported!"util.io".writeln("NOT INFERRING: ",fd);
			return false;
		}
		if(!fd.ret){
			fd.ret=type;
			setFtype(fd,true);
			return true;
		}
		if(auto nret=joinTypes(fd.ret,type)){
			//imported!"util.io".writeln("WIDENTYPE: ",fd," ",fd.ret," ",type," ",nret);
			if(fd.sealed) fd.unseal();
			fd.ret=nret;
			fd.ftype=null;
			setFtype(fd,true);
			return true;
		}
		return false;
	}
	if(fd.inferringReturnType){
		determineType(ret.e,context,(ty){
			static if(language==silq){
				if(ty.hasClassicalComponent()&&sc.controlDependency!=bottom){
					if(auto qty=ty.getQuantum())
						ty=qty;
				}
			}
			//imported!"util.io".writeln("WIDENING: ",fd," ",fd.ftype," ",ty);
			widenReturnType(ty);
			//imported!"util.io".writeln("WIDENED: ",fd," ",fd.ftype);
		},false,ret.e.loc);
	}
	ret.e=expressionSemantic(ret.e,context);
	propErr(ret.e,ret);
	if(cast(CommaExp)ret.e){
		sc.error("use parentheses for multiple return values",ret.e.loc);
		ret.sstate=SemState.error;
	}
	static if(language==silq){
		auto convertTy=fd.ret?fd.ret:ret.e.type;
		if(sc.controlDependency!=bottom){
			bool ok=true;
			if(convertTy&&convertTy.hasClassicalComponent()){
				ok=false;
				if(auto qtype=convertTy.getQuantum()){
					if(isType(qtype)){
						auto nrete=new TypeAnnotationExp(ret.e,qtype,TypeAnnotationType.annotation);
						nrete.loc=ret.e.loc;
						ret.e=nrete;
						ret.e=expressionSemantic(ret.e,context);
						ok=true;
					}
				}
				if(!ok){
					sc.error("cannot return quantum-controlled classical value",ret.e.loc);
					ret.sstate=SemState.error;
				}
			}
			if(ok) subscribeToTypeUpdates(fd,sc,ret.loc);
		}
	}
	if(ret.sstate==SemState.error)
		return ret;
	static if(language==silq) sc.clearConsumed();
	if(sc.close(ret)){
		sc.note("at function return",ret.loc);
		ret.sstate=SemState.error;
		return ret;
	}
	if(fd.ret){
		assert(!!ret.e.type);
		if(!widenReturnType(ret.e.type)){
			sc.error(format("%s is incompatible with return type %s",ret.e.type,fd.ret),ret.e.loc);
			ret.sstate=SemState.error;
			return ret;
		}
	}else{
		ret.sstate=SemState.error;
		return ret;
	}
	ret.type=.bottom;
	Expression[] returns;
	if(auto tpl=cast(TupleExp)ret.e) returns=tpl.e;
	else returns = [ret.e];
	static string getName(Expression e){
		string candidate(Expression e,bool allowNum=false){
			if(auto id=cast(Identifier)e) return id.name;
			if(auto fe=cast(FieldExp)e) return fe.f.name;
			if(auto ie=cast(IndexExp)e){
				auto idx=candidate(ie.a,true);
				if(!idx) idx="i";
				auto low=toLow(idx);
				if(!low) low="_"~idx;
				auto a=candidate(ie.e);
				if(!a) return null;
				return a~low;
			}
			if(allowNum){
				if(auto le=cast(LiteralExp)e){
					if(le.lit.type==Tok!"0")
						return le.lit.str;
				}
			}
			return null;
		}
		auto r=candidate(e);
		if(util.among(r.stripRight('\''),"delta","sum","abs","log","lim","val","⊥","case","e","π","pi")) return null;
		return r;
	}
	if(returns.length==fd.retNames.length){
		foreach(i,e;returns)
			if(auto n=getName(e)) fd.retNames[i]=n;
	}else if(returns.length==1){
		if(auto name=getName(returns[0]))
			foreach(ref n;fd.retNames) n=name;
	}
	return ret;
}


Expression typeSemantic(Expression expr,Scope sc,bool allowQNumeric=false)in{assert(!!expr&&!!sc);}do{
	if(isType(expr)||(allowQNumeric&&isQNumeric(expr))) return unwrap(expr);
	if(auto lit=cast(LiteralExp)expr){
		if(lit.lit.type==Tok!"0"){
			if(lit.lit.str=="0"){
				lit.type=etypeTy;
				return bottom;
			}
			if(lit.lit.str=="1"){
				lit.type=utypeTy;
				return unit;
			}
		}
	}
	if(auto at=cast(IndexExp)expr){
		if(auto tpl=cast(TupleExp)at.a){
			if(tpl.length==0){
				auto next=typeSemantic(at.e,sc,allowQNumeric);
				propErr(at.e,expr);
				if(!next) return null;
				expr.type=next.type;
				return arrayTy(next);
			}
		}
	}
	auto context=expSemContext(sc,ConstResult.yes,InType.yes);
	auto e=expressionSemantic(expr,context.nestConst);
	if(!e||e.sstate==SemState.error) return null;
	if(!isType(e)&&!(allowQNumeric&&isQNumeric(e))){
		if(!allowQNumeric&&isQNumeric(e)){
			sc.error(format("quantum '%s' cannot be used as a type",e),expr.loc);
			if(auto ce=e.getClassical())
				sc.note(format("did you mean to write '%s'?",ce),expr.loc);
		}else{
			auto id=cast(Identifier)expr;
			if(id&&id.meaning){
				auto decl=id.meaning;
				sc.error(format("%s '%s' is not a type",decl.kind,decl.name),id.loc);
				sc.note("declared here",decl.loc);
			}else{
				sc.error(format("expression of type '%s' cannot be used as a type",expr.type),expr.loc);
				if(auto tpl=cast(TupleExp)expr){
					if(tpl.e.all!(e=>(isType(e)||isQNumeric(e)))){
						auto ne=tpl.e.map!(e=>isQNumeric(e)?e.getClassical():e).array;
						if(ne.all!(e=>!!e))
							sc.note(format("did you mean to write '%s'?",tupleTy(ne)),expr.loc);
					}
				}
			}
		}
		expr.sstate=SemState.error;
		return null;
	}else return unwrap(e);
}

Expression typeForDecl(Declaration decl){
	if(auto dat=cast(DatDecl)decl){
		if(!dat.dtype&&dat.scope_&&dat.sstate!=SemState.started) dat=cast(DatDecl)presemantic(dat,dat.scope_);
		assert(cast(AggregateTy)dat.dtype);
		static if(language==silq){
			assert(dat.isQuantum);
			auto ttype=qtypeTy;
		}else auto ttype=typeTy;
		if(!dat.hasParams) return ttype;
		foreach(p;dat.params) if(!p.vtype) return unit; // TODO: ok?
		assert(dat.isTuple||dat.params.length==1);
		auto pt=dat.isTuple?tupleTy(dat.params.map!(p=>p.vtype).array):dat.params[0].vtype;
		return productTy(dat.params.map!(p=>p.isConst).array,dat.params.map!(p=>p.getId).array,pt,ttype,true,dat.isTuple,pure_,true);
	}
	if(auto vd=cast(VarDecl)decl){
		return vd.vtype;
	}
	if(auto fd=cast(FunctionDef)decl){
		if(!fd.ftype||!fd.ftypeFinal) setFtype(fd,true);
		if((!fd.ftype||!fd.ftypeFinal)&&fd.scope_&&fd.sstate!=SemState.started) fd=functionDefSemantic(fd,fd.scope_);
		assert(!!fd);
		return fd.ftype;
	}
	return unit; // TODO
}

bool isZero(Expression e){
	if(auto tae=cast(TypeAnnotationExp)e)
		return isZero(tae.e);
	if(auto le=cast(LiteralExp)e)
		if(le.lit.type==Tok!"0")
			if(le.lit.str=="0")
				return true;
	return false;
}
alias isFalse=isZero;
bool isTrue(Expression e){
	if(auto le=cast(LiteralExp)e)
		if(le.lit.type==Tok!"0")
			return le.lit.str!="0";
	return false;
}
bool isPositive(Expression e){
	if(isZero(e)) return false;
	if(auto le=cast(LiteralExp)e)
		if(le.lit.type==Tok!"0")
			return le.lit.str[0]!='-';
	return false;
}

bool definitelyReturns(Expression e){
	if(e.type) return isEmpty(e.type);
	if(auto ret=cast(ReturnExp)e)
		return true;
	if(auto ae=cast(AssertExp)e)
		return isFalse(ae.e);
	if(auto oe=cast(ObserveExp)e)
		return isFalse(oe.e);
	if(auto ce=cast(CompoundExp)e)
		return ce.s.any!(x=>definitelyReturns(x));
	if(auto ite=cast(IteExp)e)
		return definitelyReturns(ite.then) && definitelyReturns(ite.othw);
	if(auto fe=cast(ForExp)e){
		/+auto lle=cast(LiteralExp)fe.left;
		auto rle=cast(LiteralExp)fe.right;
		if(lle && rle && lle.lit.type==Tok!"0" && rle.lit.type==Tok!"0"){ // TODO: parse values correctly
			ℤ l=ℤ(lle.lit.str), r=ℤ(rle.lit.str);
			l+=cast(long)fe.leftExclusive;
			r-=cast(long)fe.rightExclusive;
			return l<=r && definitelyReturns(fe.bdy);
		}+/
		return false;
	}
	if(auto we=cast(WhileExp)e)
		return isTrue(we.cond);
	if(auto re=cast(RepeatExp)e)
		return isPositive(re.num) && definitelyReturns(re.bdy);
	return false;
}

ReturnExp mayReturn(Expression e){
	if(auto ret=cast(ReturnExp)e)
		return ret;
	if(auto ce=cast(CompoundExp)e){
		foreach(s;ce.s)
			if(auto ret=mayReturn(s))
				return ret;
	}
	if(auto ite=cast(IteExp)e){
		if(auto ret=mayReturn(ite.then)) return ret;
		if(auto ret=mayReturn(ite.othw)) return ret;
	}
	if(auto fe=cast(ForExp)e){
		if(auto ret=mayReturn(fe.bdy)) return ret;
	}
	if(auto we=cast(WhileExp)e){
		if(!isFalse(we.cond)){
			if(auto ret=mayReturn(we.bdy)) return ret;
		}
	}
	if(auto re=cast(RepeatExp)e){
		if(!isZero(re.num)){
			if(auto ret=mayReturn(re.bdy)) return ret;
		}
	}
	if(auto we=cast(WithExp)e){
		if(auto ret=mayReturn(we.bdy)) return ret;
	}
	return null;
}

static if(language==psi){
import sym.dexpr;
struct VarMapping{
	DNVar orig;
	DNVar tmp;
}
struct SampleFromInfo{
	bool error;
	VarMapping[] retVars;
	DNVar[] paramVars;
	DExpr newDist;
}

import distrib; // TODO: separate concerns properly, move the relevant parts back to analysis.d
SampleFromInfo analyzeSampleFrom(CallExp ce,ErrorHandler err,Distribution dist=null){ // TODO: support for non-real-valued distributions
	Expression[] args;
	if(auto tpl=cast(TupleExp)ce.arg) args=tpl.e;
	else args=[ce.arg];
	if(args.length==0){
		err.error("expected arguments to sampleFrom",ce.loc);
		return SampleFromInfo(true);
	}
	auto literal=cast(LiteralExp)args[0];
	if(!literal||literal.lit.type!=Tok!"``"){
		err.error("first argument to sampleFrom must be string literal",args[0].loc);
		return SampleFromInfo(true);
	}
	VarMapping[] retVars;
	DNVar[] paramVars;
	DExpr newDist;
	import util.hashtable;
	HSet!(string,(a,b)=>a==b,a=>typeid(string).getHash(&a)) names;
	try{
		import sym.dparse;
		auto parser=DParser(literal.lit.str);
		parser.skipWhitespace();
		parser.expect('(');
		for(bool seen=false;parser.cur()!=')';){
			parser.skipWhitespace();
			if(parser.cur()==';'){
				seen=true;
				parser.next();
				continue;
			}
			auto orig=cast(DNVar)parser.parseDVar();
			if(!orig) throw new Exception("TODO");
			if(orig.name in names){
				err.error(text("multiple variables of name \"",orig.name,"\""),args[0].loc);
				return SampleFromInfo(true);
			}
			if(!seen){
				auto tmp=dist?dist.getTmpVar("__tmp"~orig.name):null; // TODO: this is a hack
				retVars~=VarMapping(orig,tmp);
			}else paramVars~=orig;
			parser.skipWhitespace();
			if(!";)"[seen..$].canFind(parser.cur())) parser.expect(',');
		}
		parser.next();
		parser.skipWhitespace();
		if(parser.cur()=='⇒') parser.next();
		else{ parser.expect('='); parser.expect('>'); }
		parser.skipWhitespace();
		newDist=parser.parseDExpr();
	}catch(Exception e){
		err.error(e.msg,args[0].loc);
		return SampleFromInfo(true);
	}
	if(dist){
		foreach(var;retVars){
			if(!newDist.hasFreeVar(var.orig)){
				err.error(text("pdf must depend on variable ",var.orig.name,")"),args[0].loc);
				return SampleFromInfo(true);
			}
		}
		newDist=newDist.substituteAll(retVars.map!(x=>cast(DVar)x.orig).array,retVars.map!(x=>cast(DExpr)x.tmp).array);
	}
	if(args.length!=1+paramVars.length){
		err.error(text("expected ",paramVars.length," additional arguments to sampleFrom"),ce.loc);
		return SampleFromInfo(true);
	}
	return SampleFromInfo(false,retVars,paramVars,newDist);
}

Expression handleSampleFrom(CallExp ce,Scope sc,InType inType){
	auto context=ExpSemContext(sc,ConstResult.yes,inType);
	if(inType){
		sc.error("cannot use sampleFrom directly within type",ce.loc);
		ce.sstate=SemState.error;
		return ce;
	}
	auto info=analyzeSampleFrom(ce,sc.handler);
	if(info.error){
		ce.sstate=SemState.error;
	}else{
		 // TODO: this special casing is not very nice:
		ce.type=info.retVars.length==1?ℝ(true):tupleTy((cast(Expression)ℝ(true)).repeat(info.retVars.length).array);
	}
	if(auto tpl=cast(TupleExp)ce.arg){
		foreach(ref arg;tpl.e[1..$]){
			arg=expressionSemantic(arg,context.nestConst);
			propErr(arg,ce.arg);
		}
	}
	propErr(ce.arg,ce);
	return ce;
}
}else static if(language==silq){

Expression handlePrimitive(CallExp ce, ExpSemContext context){
	Scope sc=context.sc;
	ce.arg=expressionSemantic(ce.arg,context.nestConst);
	Expression[] args;
	if(auto tpl=cast(TupleExp)ce.arg) args=tpl.e;
	else {
		sc.error("expected literal arguments to __primitive",ce.loc);
		ce.sstate=SemState.error;
		return ce;
	}
	if(args.length!=2){
		sc.error("expected two arguments to __primitive",ce.loc);
		ce.sstate=SemState.error;
		return ce;
	}
	auto literal=cast(LiteralExp)args[0];
	if(!literal||literal.lit.type!=Tok!"``"){
		sc.error("first argument to __primitive must be string literal",args[0].loc);
		ce.sstate=SemState.error;
		return ce;
	}
	if(!isType(args[1])){
		sc.error("second argument to __primitive must be a type",args[0].loc);
		ce.sstate=SemState.error;
		return ce;
	}
	ce.type=args[1];
	propErr(ce.type,ce);
	return ce;
}

Expression handleQuery(CallExp ce,ExpSemContext context){
	auto sc=context.sc;
	Expression[] args;
	if(auto tpl=cast(TupleExp)ce.arg) args=tpl.e;
	else args=[ce.arg];
	if(args.length==0){
		sc.error("expected argument to __query",ce.loc);
		ce.sstate=SemState.error;
		return ce;
	}
	auto literal=cast(LiteralExp)args[0];
	if(!literal||literal.lit.type!=Tok!"``"){
		sc.error("first argument to __query must be string literal",args[0].loc);
		ce.sstate=SemState.error;
		return ce;
	}
	auto makeStrLit(string s){
		Token tok;
		tok.type=Tok!"``";
		tok.str=s;
		auto nlit=New!LiteralExp(tok);
		nlit.loc=ce.loc;
		nlit.type=stringTy(true);
		nlit.sstate=SemState.completed;
		return nlit;
	}
	switch(literal.lit.str){
		case "dep":
			if(args.length!=2||!cast(Identifier)args[1]){
				sc.error("expected single variable as argument to 'dep' query", ce.loc);
				ce.sstate=SemState.error;
				break;
			}else{
				args[1]=expressionSemantic(args[1],context.nestConst);
				auto dep="{}";
				if(auto id=cast(Identifier)args[1]){
					if(id.sstate==SemState.completed){
						auto dependency=sc.getDependency(id);
						if(dependency.isTop) dep="⊤";
						else dep=dependency.dependencies.to!string;
					}
				}
				return makeStrLit(dep);
			}
		case "type":
			if(args.length!=2){
				sc.error("expected single expression as argument to 'type' query", ce.loc);
				ce.sstate=SemState.error;
				break;
			}else{
				args[1]=expressionSemantic(args[1],context.nestConst);
				return makeStrLit(text(args[1].type));
			}
		case "conversion":
			if(args.length!=3){
				sc.error("expected two expressions as arguments to 'conversion' query", ce.loc);
				ce.sstate=SemState.error;
				break;
			}else{
				args[1]=typeSemantic(args[1], sc, true);
				args[2]=typeSemantic(args[2], sc, true);
				return makeStrLit(text(typeExplicitConversion!true(args[1], args[2], TypeAnnotationType.coercion)));
			}
		default:
			sc.error(format("unknown query '%s'",literal.lit.str),literal.loc);
			ce.sstate=SemState.error;
			break;
	}
	return ce;
}

}
