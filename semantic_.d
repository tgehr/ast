// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.semantic_;
import astopt;

import std.array,std.algorithm,std.range,std.exception;
import std.format, std.conv, util.tuple:Q=Tuple,q=tuple;
import ast.lexer,ast.scope_,ast.expression,ast.type,ast.declaration,ast.error,ast.reverse,util;

string freshName(){ // TODO: improve mechanism for generating temporaries
	static int counter=0;
	return text("__tmp",counter++);
}

Expression moveExp(Expression e){
	// TODO: implement
	return e;
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
	}
}

VarDecl addVar(string name,Expression ty,Location loc,Scope sc){
	auto id=new Identifier(name);
	id.loc=loc;
	auto var=new VarDecl(id);
	var.loc=loc;
	var.vtype=ty;
	var=varDeclSemantic(var,sc);
	assert(!!var && var.sstate==SemState.completed);
	return var;
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
		if(cast(NestedScope)sc) dat.context = addVar("`outer",contextTy(true),dat.loc,dsc);
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
			if(!setFtype(fd)) fd.sstate=SemState.error;
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
		assert(!fd.body_.blscope_);
		fd.body_.blscope_=new BlockScope(fsc);
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
				assert(!!fd.body_.blscope_);
				auto thisVar=addVar("this",ctxty,fd.loc,fd.body_.blscope_); // the 'this' variable
				fd.isConstructor=true;
				if(fd.rret){
					sc.error("constructor cannot have return type annotation",fd.loc);
					fd.sstate=SemState.error;
				}else{
					assert(dsc.decl.dtype);
					fd.ret=ctxty;
				}
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
				if(dsc.decl.context){
					fd.context=dsc.decl.context; // TODO: ok?
					fd.contextVal=dsc.decl.context; // TODO: ok?
				}
				fd.thisVar=thisVar;
			}else{
				fd.contextVal=addVar("this",unit,fd.loc,fsc); // the 'this' value
				assert(!!fd.body_.blscope_);
				assert(fsc.allowMerge);
				fsc.allowMerge=false; // TODO: this is hacky
				fd.context=addVar("this",ctxty,fd.loc,fd.body_.blscope_);
				fsc.allowMerge=true;
				assert(fd.context.getName!=fd.contextVal.getName);
			}
			assert(dsc.decl.dtype);
		}else if(auto nsc=cast(NestedScope)sc){
			fd.contextVal=addVar("`outer",contextTy(true),fd.loc,fsc); // TODO: replace contextTy by suitable record type; make name 'outer' available
			fd.context=fd.contextVal;
		}
	}
	return expr;
}

import util.tuple: tuple,Tuple;
static Tuple!(Expression[],TopScope)[string] modules;
TopScope prsc=null;
int importModule(string path,ErrorHandler err,out Expression[] exprs,out TopScope sc,Location loc=Location.init){
	if(path in modules){
		auto exprssc=modules[path];
		exprs=exprssc[0],sc=exprssc[1];
		if(!sc){
			if(loc.line) err.error("circular imports not supported",loc);
			else stderr.writeln("error: circular imports not supported");
			return 1;
		}
		return 0;
	}
	modules[path]=tuple(Expression[].init,TopScope.init);
	scope(success) modules[path]=tuple(exprs,sc);
	Expression[] prelude;
	import ast.parser;
	if(!prsc && path != preludePath())
		if(auto r=importModule(preludePath,err,prelude,prsc))
			return r;
	if(auto r=parseFile(getActualPath(path),err,exprs,loc))
		return r;
	sc=new TopScope(err);
	if(prsc) sc.import_(prsc);
	int nerr=err.nerrors;
	exprs=semantic(exprs,sc);
	if(nerr!=err.nerrors){
		if(loc.line) sc.error("errors in imported file",loc);
		return 1;
	}
	return 0;
}

bool isInPrelude(Declaration decl){
	auto ppath=preludePath();
	if(ppath !in modules) return false;
	auto psc=modules[ppath];
	return decl.scope_.isNestedIn(psc[1]);
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
			if(be.e2.sstate!=SemState.error||!sc.lookupHere(nid,false,Lookup.probing))
				success&=sc.insert(vd);
			id.meaning=vd;
			id.name=vd.getName;
			id.scope_=sc;
			return vd;
		}
		if(auto id=cast(Identifier)be.e1){
			auto vd=makeVar(id);
			auto de=new SingleDefExp(vd,be);
			de.loc=be.loc;
			propErr(vd,de);
			return de;
		}else if(auto tpl=cast(TupleExp)be.e1){
			VarDecl[] vds;
			foreach(exp;tpl.e){
				if(auto id=cast(Identifier)exp) vds~=makeVar(id);
				else goto LbadDefLhs;
			}
			auto de=new MultiDefExp(vds,be);
			de.loc=be.loc;
			foreach(vd;vds) if(vd) propErr(vd,de);
			return de;
		}else if(auto ce=cast(CallExp)be.e1){
			auto f=ce.e,ft=cast(ProductTy)f.type;
			if(!ft||ft.isSquare!=ce.isSquare)
				goto LbadDefLhs;
			bool allConst=iota(ft.nargs).all!(i=>ft.isConstForReverse[i]);
			if(allConst){
				auto d=new MultiDefExp([],be);
				d.loc=be.loc;
				return d;
			}
			bool allMoved=iota(ft.nargs).all!(i=>!ft.isConstForReverse[i]);
			if(auto tpl=cast(TupleExp)ce.arg){
				if(allMoved) goto LbadDefLhs;
				assert(!tpl.length||ft.isTuple&&ft);
				auto movedIndices=iota(tpl.length).filter!(i=>!ft.isConstForReverse[i]);
				VarDecl[] vds;
				foreach(exp;movedIndices.map!(i=>tpl.e[i])){
					if(auto id=cast(Identifier)exp) vds~=makeVar(id);
					else goto LbadDefLhs;
				}
				auto de=new MultiDefExp(vds,be);
				de.loc=be.loc;
				propErr(be,de);
				foreach(vd;vds) if(vd) propErr(vd,de);
				return de;
			}
			if(!allMoved) goto LbadDefLhs;
			if(auto id=cast(Identifier)ce.arg){
				auto vd=makeVar(id);
				auto de=new SingleDefExp(vd,be);
				de.loc=be.loc;
				propErr(be,de);
				propErr(vd,de);
				return de;
			}else goto LbadDefLhs;
		}else if(cast(IndexExp)be.e1){
			auto de=new SingleDefExp(null,be);
			de.loc=be.loc;
			return de;
		}else LbadDefLhs:{
			if(be.sstate!=SemState.error){
				sc.error("invalid definition left-hand side",be.e1.loc);
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
			id.name=vd.getName;
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
Expression toplevelSemanticImpl(DefExp expr,Scope sc){
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
	quantumPrimitive,
	show,
	query,
	typeTy,
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
			case "quantumPrimitive":
				return BuiltIn.quantumPrimitive;
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
		case "𝟙":
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
	if(preludePath() !in modules) return PreludeSymbol.none;
	auto exprssc=modules[preludePath()];
	auto sc=exprssc[1];
	if(!decl||decl.scope_ !is sc) return PreludeSymbol.none;
	if(!decl.name) return PreludeSymbol.none;
	switch(decl.getName){
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
string isQuantumPrimitive(Expression e){
	auto ce=cast(CallExp)e;
	if(!ce) return null;
	auto id=cast(Identifier)ce.e;
	if(!id) return null;
	if(id.meaning || id.name != "quantumPrimitive") return null;
	auto args=cast(TupleExp)ce.arg;
	enforce(!!args&&args.e.length==2);
	auto opLit=cast(LiteralExp)args.e[0];
	enforce(!!opLit&&opLit.lit.type==Tok!"``");
	return opLit.lit.str;
}

bool isInPrelude(){
	auto exprssc=modules[preludePath()];
	return exprssc[1] is null;
}

Identifier getPreludeSymbol(string name,Location loc,Scope isc){
	import ast.semantic_: modules;
	if(preludePath() !in modules) return null;
	auto exprssc=modules[preludePath()];
	auto sc=exprssc[1];
	assert(!!sc);
	auto res=new Identifier(name);
	res.loc=loc;
	res.scope_=isc;
	res.meaning=sc.lookup(res,false,false,Lookup.consuming);
	if(!res.meaning){
		res.sstate=SemState.error;
	}else{
		res.type=res.typeFromMeaning;
		res.constLookup=false;
		res.sstate=SemState.completed;
	}
	return res;
}

Expression getDistribution(Location loc,Scope sc){
	return getPreludeSymbol("Distribution",loc,sc);
}

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
			case "quantumPrimitive","__query","__show":
				t=unit;
				break; // those are actually magic polymorphic functions
		}
		static if(language==psi){
			case "Expectation": t=funTy(ℝ(false),ℝ(false),false,false,true); break; // TODO: should be lifted
		}
		static if(language==silq){
			case "type","ctype","qtype","qnumeric":
				goto case;
		}
		case "*","𝟙","𝟚","B","𝔹","N","ℕ","Z","ℤ","Q","ℚ","R","ℝ","C","ℂ":
			id.type=ctypeTy;
			if(id.name=="*"||id.name=="type") return typeTy;
			if(id.name=="ctype") return ctypeTy;
			if(id.name=="qtype") return qtypeTy;
			static if(language==silq)
				if(id.name=="qnumeric") return qnumericTy;
			if(id.name=="𝟙") return unit;
			if(id.name=="𝟚"||id.name=="B"||id.name=="𝔹") return Bool(false);
			if(id.name=="N"||id.name=="ℕ") return ℕt(false);
			if(id.name=="Z"||id.name=="ℤ") return ℤt(false);
			if(id.name=="Q"||id.name=="ℚ") return ℚt(false);
			if(id.name=="R"||id.name=="ℝ") return ℝ(false);
			if(id.name=="C"||id.name=="ℂ") return ℂ(false);
			return null;
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
	scope(exit) if(--asc.getDatDecl().semanticDepth==0&&!asc.close()) cd.sstate=SemState.error; // TODO: fix
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

Expression statementSemanticImpl(CompoundExp ce,Scope sc){
	foreach(ref s;ce.s){
		s=statementSemantic(s,sc);
		propErr(s,ce);
	}
	return ce;
}

Expression statementSemanticImpl(IteExp ite,Scope sc){
	ite.cond=conditionSemantic!true(ite.cond,sc,InType.no);
	static if(language==silq){
		auto quantumControl=ite.cond.type!=Bool(true);
		auto restriction_=quantumControl?Annotation.mfree:Annotation.none;
	}else{
		enum quantumControl=false;
		enum restriction_=Annotation.none;
	}
	// initialize scopes, to allow captures to be inserted
	ite.then.blscope_=new BlockScope(sc,restriction_);
	if(!ite.othw){
		ite.othw=New!CompoundExp((Expression[]).init);
		ite.othw.loc=ite.loc;
	}
	ite.othw.blscope_=new BlockScope(sc,restriction_);
	ite.then=controlledCompoundExpSemantic(ite.then,sc,ite.cond,restriction_);
	ite.othw=controlledCompoundExpSemantic(ite.othw,sc,ite.cond,restriction_);
	propErr(ite.cond,ite);
	propErr(ite.then,ite);
	propErr(ite.othw,ite);
	NestedScope[] scs;
	if(!quantumControl){
		if(definitelyReturns(ite.then)) scs=[ite.othw.blscope_];
		else if(definitelyReturns(ite.othw)) scs=[ite.then.blscope_];
		else scs=[ite.then.blscope_,ite.othw.blscope_];
	}else scs=[ite.then.blscope_,ite.othw.blscope_];
	if(sc.merge(quantumControl,scs)){
		sc.note("consumed in one branch of if expression", ite.loc);
		ite.sstate=SemState.error;
	}
	ite.type=unit;
	return ite;
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

// TODO: supertypes for define and assign?
Expression statementSemanticImpl(ForExp fe,Scope sc){
	auto context=expSemContext(sc,ConstResult.yes,InType.no);
	assert(!fe.bdy.blscope_);
	fe.left=expressionSemantic(fe.left,context.nestConst);
	propErr(fe.left,fe);
	static if(language==silq) sc.pushConsumed();
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
	static if(language==silq) sc.pushConsumed();
	if(fe.right.sstate==SemState.completed && !isSubtype(fe.right.type, ℝ(true))){
		sc.error(format("upper bound for loop variable should be a classical number, not %s",fe.right.type),fe.right.loc);
		fe.sstate=SemState.error;
	}
	bool converged=false;
	CompoundExp bdy;
	while(!converged){ // TODO: limit number of iterations?
		auto prevStateSnapshot=sc.getStateSnapshot();
		auto forgetScope=new BlockScope(sc);
		Expression.CopyArgs cargs={preserveSemantic: true};
		bdy=fe.bdy.copy(cargs);
		auto fesc=bdy.blscope_=new BlockScope(sc);
		auto vd=new VarDecl(fe.var);
		vd.vtype=fe.left.type && fe.right.type ? joinTypes(fe.left.type, fe.right.type) : ℤt(true);
		assert(fe.sstate==SemState.error||vd.vtype.isClassical());
		if(fe.sstate==SemState.error){
			if(!vd.vtype) vd.vtype=ℤt(true);
			vd.vtype=vd.vtype.getClassical();
		}
		vd.loc=fe.var.loc;
		fe.fescope_=fesc;
		fe.var.name=vd.getName;
		fe.loopVar=vd;
		if(vd.name.name!="_"&&!fesc.insert(vd))
			fe.sstate=vd.sstate=SemState.error;
		if(vd.sstate!=SemState.error)
			vd.sstate=SemState.completed;
		bdy=compoundExpSemantic(bdy,sc);
		assert(!!bdy);
		propErr(bdy,fe);
		static if(language==silq){
			if(sc.merge(false,fesc,forgetScope)){
				sc.note("possibly consumed in for loop", fe.loc);
				fe.sstate=SemState.error;
				converged=true;
			}
			if(forgetScope.forgottenVars.length){
				sc.error("variables potentially consumed multiple times in for loop",fe.loc);
				foreach(decl;forgetScope.forgottenVars)
					sc.note(format("variable '%s'",decl.name),decl.loc);
				fe.sstate=SemState.error;
				converged=true;
			}
		}else sc.merge(false,fesc,forgetScope);
		converged|=bdy.sstate==SemState.error||sc.getStateSnapshot()==prevStateSnapshot;
	}
	fe.bdy=bdy;
	fe.type=unit;
	return fe;
}

Expression statementSemanticImpl(WhileExp we,Scope sc){
	bool converged=false;
	Expression.CopyArgs cargs={preserveSemantic: true};
	auto cond=we.cond.copy(cargs);
	cond=conditionSemantic(cond,sc,InType.no);
	propErr(cond,we);
	static if(language==silq) sc.pushConsumed();
	CompoundExp bdy;
	while(!converged){ // TODO: limit number of iterations?
		auto prevStateSnapshot=sc.getStateSnapshot();
		auto forgetScope=new BlockScope(sc);
		bdy=we.bdy.copy(cargs);
		auto wesc=bdy.blscope_=new BlockScope(sc);
		bdy=compoundExpSemantic(bdy,sc);
		propErr(bdy,we);
		auto ncond=we.cond.copy(cargs);
		ncond=conditionSemantic(ncond,wesc,InType.no);
		static if(language==silq) wesc.pushConsumed();
		propErr(ncond,we);
		if(cond.sstate==SemState.completed&&ncond.sstate==SemState.error)
			sc.note("variable declaration may be missing in while loop body", we.loc);
		static if(language==silq){
			if(sc.merge(false,bdy.blscope_,forgetScope)){
				sc.note("possibly consumed in while loop", we.loc);
				we.sstate=SemState.error;
				converged=true;
			}
			if(forgetScope.forgottenVars.length){
				sc.error("variables potentially consumed multiple times in while loop", we.loc);
				foreach(decl;forgetScope.forgottenVars)
					sc.note(format("variable '%s'",decl.name),decl.loc);
				we.sstate=SemState.error;
				converged=true;
			}
		}else sc.merge(false,bdy.blscope_,forgetScope);
		converged|=bdy.sstate==SemState.error||sc.getStateSnapshot()==prevStateSnapshot;
	}
	we.cond=cond;
	we.bdy=bdy;
	we.type=unit;
	return we;
}

Expression statementSemanticImpl(RepeatExp re,Scope sc){
	auto context=expSemContext(sc,ConstResult.yes,InType.no);
	re.num=expressionSemantic(re.num,context.nestConst);
	static if(language==silq) sc.pushConsumed();
	propErr(re.num,re);
	if(re.num.sstate==SemState.completed && !isSubtype(re.num.type, ℤt(true))){
		sc.error(format("number of iterations should be a classical integer, not %s",re.num.type),re.num.loc);
		re.sstate=SemState.error;
	}
	bool converged=false;
	Expression.CopyArgs cargs={preserveSemantic: true};
	CompoundExp bdy;
	while(!converged){ // TODO: limit number of iterations?
		auto prevStateSnapshot=sc.getStateSnapshot();
		auto forgetScope=new BlockScope(sc);
		bdy=re.bdy.copy(cargs);
		bdy=compoundExpSemantic(bdy,sc);
		propErr(bdy,re);
		static if(language==silq){
			if(sc.merge(false,bdy.blscope_,forgetScope)){
				sc.note("possibly consumed in repeat loop", re.loc);
				re.sstate=SemState.error;
				converged=true;
			}
			if(forgetScope.forgottenVars.length){
				sc.error("variables potentially consumed multiple times in repeat loop", re.loc);
				foreach(decl;forgetScope.forgottenVars)
					sc.note(format("variable '%s'",decl.name),decl.loc);
				re.sstate=SemState.error;
				converged=true;
			}
		}else sc.merge(false,bdy.blscope_,forgetScope);
		converged|=bdy.sstate==SemState.error||sc.getStateSnapshot()==prevStateSnapshot;
	}
	re.bdy=bdy;
	re.type=unit;
	return re;
}

Expression statementSemanticImpl(ObserveExp oe,Scope sc){
	oe.e=conditionSemantic(oe.e,sc,InType.no);
	propErr(oe.e,oe);
	oe.type=unit;
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
	ae.type=unit;
	return ae;
}

Expression statementSemanticImpl(ForgetExp fe,Scope sc){
	auto context=expSemContext(sc,ConstResult.yes,InType.no);
	return expressionSemantic(fe,context.nestConst);
}

Expression statementSemanticImplDefault(Expression e,Scope sc){
	sc.error("not supported at this location",e.loc);
	e.sstate=SemState.error;
	return e;
}

Expression statementSemantic(Expression e,Scope sc)in{
	assert(sc.allowsLinear());
}do{
	if(e.sstate==SemState.completed) return e;
	scope(success) if(e.sstate!=SemState.error) e.sstate=SemState.completed;
	static if(language==silq){
		scope(exit){
			sc.pushConsumed();
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
			else ce.blscope_.addControlDependency(Dependency(true,SetX!string.init));
		}
	}
	return compoundExpSemantic(ce,sc,restriction_);
}

CompoundExp compoundExpSemantic(CompoundExp ce,Scope sc,Annotation restriction_=Annotation.none){
	if(!ce.blscope_) ce.blscope_=new BlockScope(sc,restriction_);
	foreach(ref e;ce.s){
		//writeln("before: ",e," ",typeid(e)," ",e.sstate," ",ce.blscope_.getStateSnapshot());
		e=statementSemantic(e,ce.blscope_);
		//writeln("after: ",e," ",typeid(e)," ",e.sstate," ",ce.blscope_.getStateSnapshot());
		propErr(e,ce);
	}
	ce.type=unit;
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
			if(!sc.dependencyTracked(id)) // for variables captured in closure
				return Dependency(true);
			result.dependencies.insert(id.name);
			if(!id.constLookup){
				auto vd=cast(VarDecl)id.meaning;
				if(!vd||!(vd.isConst||sc.isConst(vd))) result.replace(id.name,sc.getDependency(id),sc.controlDependency);
			}
		}
	}
	return result;
}

bool consumes(Expression e){
	if(auto id=cast(Identifier)e) if(auto m=cast(VarDecl)id.meaning) if(m.isConst) return false;
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
	if(cast(AddExp)e||cast(SubExp)e||cast(NSubExp)e||cast(MulExp)e||cast(DivExp)e||cast(IDivExp)e||cast(ModExp)e||cast(PowExp)e||cast(BitOrExp)e||cast(BitXorExp)e||cast(BitAndExp)e||cast(UMinusExp)e||cast(UNotExp)e||cast(UBitNotExp)e||cast(AndExp)e||cast(OrExp)e||cast(LtExp)e||cast(LeExp)e||cast(GtExp)e||cast(GeExp)e||cast(EqExp)e||cast(NeqExp)e)
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
	string nameIndex(IndexExp index){
		auto name=freshName();
		sc.nameIndex(index,name);
		return name;
	}
}
auto defineLhsContext(ExpSemContext expSem){
	return DefineLhsContext(expSem);
}
auto nest(DefineLhsContext context,ConstResult newConstResult){
	return defineLhsContext(context.expSem.nest(newConstResult),context.tupleof[1..$]);
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
Expression defineLhsSemanticImpl(CallExp e,DefineLhsContext context){
	return callSemantic!isPresemantic(e,context);
}

static if(language==psi)
Expression defineLhsSemanticImpl(PlaceholderExp pl,DefineLhsContext context){
	return defineLhsSemanticImplCurrentlyUnsupported(pl,context);
}

Expression defineLhsSemanticImpl(ForgetExp fe,DefineLhsContext context){
	fe.type=unit;
	// TODO: introduce variables here?
	return fe;
}
Expression defineLhsSemanticImpl(Identifier id,DefineLhsContext context){
	// id.type= // TODO?
	// TODO: introduce variable here?
	return id;
}
Expression defineLhsSemanticImpl(FieldExp fe,DefineLhsContext context){
	// TODO: add new fields to records?
	return defineLhsSemanticImplUnsupported(fe,context);
}

static if(language==silq){
Expression defineLhsSemanticImpl(IndexExp idx,DefineLhsContext context){
	Expression analyzeAggregate(IndexExp e,DefineLhsContext context){
		auto next=unwrap(e.e);
		if(auto id=cast(Identifier)next){
			id.indexedDirectly=true;
			id.scope_=context.sc;
			if(!id.meaning) id.meaning=lookupMeaning(id,Lookup.probing,context.sc);
			propErr(next,e);
			if(id.meaning){
				if(id.meaning.rename) id.name=id.meaning.rename.name;
				id.type=id.typeFromMeaning;
				if(auto ft=cast(FunTy)id.type){
					auto ce=new CallExp(id,e.a,true,false);
					ce.loc=idx.loc;
					return callSemantic!isPresemantic(ce,context);
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
			if(auto r=analyzeAggregate(idx,context.nestConst)){
				e.e=r;
				return e;
			}
		}
		if(next!is e.e) propErr(next,e.e);
		propErr(next,e);
		return null;
	}
	if(auto r=analyzeAggregate(idx,context)) return r;
	void analyzeIndex(IndexExp e){
		if(auto idx=cast(IndexExp)unwrap(e.e)) analyzeIndex(idx);
		e.a=expressionSemantic(e.a,context.expSem.nestConst);
		propErr(e.e,e);
	}
	analyzeIndex(idx);
	if(idx.byRef) return expressionSemantic(idx,context.expSem);
	auto sc=context.sc;
	if(idx.e.type&&idx.e.type.isClassical()){
		sc.error(format("use assignment statement '%s = ...;' to assign to classical array component",idx),idx.loc);
		idx.sstate=SemState.error;
		return idx;
	}
	bool checkReplaceable(IndexExp e){
		if(auto id=cast(Identifier)unwrap(e.e)){
			if(id.meaning) return checkAssignable(id.meaning,idx.e.loc,sc,true);
			assert(id.sstate==SemState.error);
			return true; // TODO: ok?
		}
		if(!e.a.isLifted(sc)||e.a.type&&!e.a.type.isClassical()){ // TODO: quantum index replacement
			sc.error("index for component replacement must be 'lifted' and classical",e.a.loc);
			return false;
		}
		if(e.a.type&&!isBasicIndexType(e.a.type)){
			sc.error(format("index for component replacement must be integer, not '%s'",e.a.type),e.a.loc);
			return false;
		}
		if(auto idx2=cast(IndexExp)unwrap(e.e)) return checkReplaceable(idx2);
		return true;
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
	foreach(ref e;tpl.e){
		e=defineLhsSemantic!isPresemantic(e,context);
		propErr(e,tpl);
	}
	return tpl;
}
Expression defineLhsSemanticImpl(ArrayExp arr,DefineLhsContext context){
	// TODO: do we even keep this?
	foreach(ref e;arr.e){
		e=defineLhsSemantic!isPresemantic(e,context);
		propErr(e,arr);
	}
	return arr;
}

Expression defineLhsSemanticImpl(TypeAnnotationExp tae,DefineLhsContext context){
	auto sc=context.sc;
	tae.e=defineLhsSemantic!isPresemantic(tae.e,context);
	// tae.type=typeSemantic(tae.t,sc); // (can't do this here at the moment due to how expressionSemantic works)
	// TODO: need to do anything else?
	return tae;
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
	ce.e1=defineLhsSemantic!isPresemantic(ce.e1,context);
	propErr(ce.e1,ce);
	ce.e2=defineLhsSemantic!isPresemantic(ce.e2,context);
	propErr(ce.e2,ce);
	// TODO: determine type?
	return ce;
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


Expression defineLhsSemanticImplLifted(Expression e,DefineLhsContext context){
	return expressionSemantic(e,context.expSem); // TODO: analyze later instead?
}

Expression defineLhsSemanticImplCurrentlyUnsupported(Expression e,DefineLhsContext context){
	auto sc=context.sc;
	sc.error("currently not supported as definition left-hand side",e.loc);
	e.sstate=SemState.error;
	return e;
}
Expression defineLhsSemanticImplUnsupported(Expression e,DefineLhsContext context){
	auto sc=context.sc;
	sc.error("not supported as definition left-hand side",e.loc);
	e.sstate=SemState.error;
	return e;
}

Expression defineLhsSemanticImplDefault(Expression e,DefineLhsContext context){
	return defineLhsSemanticImplUnsupported(e,context);
}

}

alias defineLhsSemanticImpl(bool isPresemantic)=defineLhsSemanticImpls!isPresemantic.defineLhsSemanticImpl;
alias defineLhsSemanticImplDefault(bool isPresemantic)=defineLhsSemanticImpls!isPresemantic.defineLhsSemanticImplDefault;


Expression defineLhsSemantic(bool isPresemantic=false)(Expression lhs,DefineLhsContext context){
	if(context.constResult) return expressionSemantic(lhs,context.expSem);
	return dispatchExp!(defineLhsSemanticImpl!isPresemantic,defineLhsSemanticImplDefault!isPresemantic)(lhs,context);
}

Expression defineLhsPresemantic(Expression lhs,DefineLhsContext context){
	return defineLhsSemantic!true(lhs,context);
}

static if(language==silq)
Expression swapSemantic(DefineExp be,Scope sc){ // TODO: placeholder. fix this
	bool isSwap=false;
	auto tpl1=cast(TupleExp)unwrap(be.e1);
	auto tpl2=cast(TupleExp)unwrap(be.e2);
	if(!tpl1||!tpl2) return null;
	if(tpl1.length!=2||tpl2.length!=2) return null;
	IndexExp[2] idx1=[cast(IndexExp)tpl1.e[0],cast(IndexExp)tpl1.e[1]];
	IndexExp[2] idx2=[cast(IndexExp)tpl2.e[0],cast(IndexExp)tpl2.e[1]];
	if(!idx1[0]||!idx1[1]||!idx2[0]||!idx2[1]) return null;
	assert(!sc.toPush.length,text(be));
	auto preState=sc.getStateSnapshot(true);
	foreach(i;0..2){
		if(!guaranteedSameLocations(idx1[i],idx2[$-1-i],be.loc,sc,InType.no)){
			sc.restoreStateSnapshot(preState);
			return null;
		}
	}
	be.isSwap=true;
	auto econtext=expSemContext(sc,ConstResult.no,InType.no);
	be.e2=expressionSemantic(be.e2,econtext);
	be.sstate=SemState.completed;
	return be;
}

Expression defineSemantic(DefineExp be,Scope sc){
	auto econtext=expSemContext(sc,ConstResult.no,InType.no);
	Expression prologue=null,epilogue=null;
	Expression finish(Expression r){
		static if(language==silq) sc.pushConsumed();
		if(!prologue&&!epilogue) return r;
		assert(!prologue||util.among(prologue.sstate,SemState.completed,SemState.error));
		Expression[] s;
		if(prologue) s~=prologue;
		assert(r&&util.among(r.sstate,SemState.completed,SemState.error));
		s~=r;
		if(epilogue){
			propErr(prologue,epilogue);
			epilogue=statementSemantic(epilogue,sc);
			s~=epilogue;
		}
		auto res=new CompoundExp(s);
		res.loc=be.loc;
		res.sstate=SemState.completed;
		foreach(e;s) propErr(e,res);
		return res;
	}
	static if(language==silq)
	if(sc.allowsLinear){
		if(auto r=swapSemantic(be,sc)) return r;
		auto dcontext=defineLhsContext(econtext);
		auto creplsCtx=sc.moveLocalComponentReplacements(); // TODO: get rid of this
		be.e1=defineLhsPresemantic(be.e1,dcontext);
		//writeln("{",indicesToReplace.map!(x=>text(x[0]?x[0].toString:"null",",",x[1],",",x[2]?x[2].toString():"null")).join(";"),"}");
		auto crepls=sc.localComponentReplacements();
		if(crepls.length){
			Expression[] reads;
			foreach(ref crepl;crepls){
				if(!crepl.write) continue;
				auto id=new Identifier(crepl.name);
				id.loc=be.loc;
				auto idx=crepl.write.copy();
				idx.loc=crepl.write.loc;
				idx.byRef=true;
				auto read=new BinaryExp!(Tok!":=")(id,moveExp(idx));
				read.loc=crepl.write.loc;
				reads~=read;
			}
			auto creplsCtx2=sc.moveLocalComponentReplacements(); // TODO: get rid of this
			prologue=statementSemantic(new CompoundExp(reads),sc);
			sc.restoreLocalComponentReplacements(creplsCtx2); // TODO: get rid of this
			prologue.loc=be.loc;
			Expression[] writes;
			foreach(ref crepl;crepls){
				if(!crepl.write) continue;
				auto id=new Identifier(crepl.name);
				id.loc=be.loc;
				auto idx=crepl.write.copy();
				idx.loc=crepl.write.loc;
				idx.byRef=true;
				auto write=new BinaryExp!(Tok!":=")(moveExp(idx),id);
				write.loc=crepl.write.loc;
				writes~=write;
			}
			epilogue=new CompoundExp(writes);
			epilogue.loc=be.loc;
		}else sc.restoreLocalComponentReplacements(creplsCtx); // TODO: get rid of this
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
		static if(language==silq){
			assert(!sc.toPush.length,text(be));
		}
		auto preState=sc.getStateSnapshot(true);
		be.e2=expressionSemantic(be.e2,context.nestConsumed);
		propErr(be.e2,be);
		if(be.sstate!=SemState.error){
			enum flags=LowerDefineFlags.createFresh, unchecked=false;
			if(auto e=lowerDefine!flags(be,sc,unchecked)){
				if(e.sstate!=SemState.error){
					static if(language==silq){
						sc.toPush=[];
					}
					sc.restoreStateSnapshot(preState);
					auto r=statementSemantic(e,sc);
					static if(language==silq)
						finishIndexReplacement(be,sc);
					if(be.sstate==SemState.error)
						return be;
					return finish(r);
				}
				static if(language==silq)
					finishIndexReplacement(be,sc);
				return finish(e);
			}
		}else{
			epilogue=null; // (avoids error messages)
			// TODO: clean up other temporaries
		}
		static if(language==silq)
			finishIndexReplacement(be,sc);
	}else{
		be.e2=expressionSemantic(be.e2,context.nestConsumed);
	}
	bool success=true;
	auto e2orig=be.e2;
	static if(language==silq) bool badUnpackLhs=false; // (to check that makeDeclaration will indeed produce an error)
	static if(language==silq){
		if(be.e2.sstate==SemState.completed&&sc.getFunction()){
			void addDependencies(Expression[] lhs,Expression[] rhs)in{
				assert(lhs.length==rhs.length);
			}do{
				Q!(string,Dependency)[] dependencies;
				foreach(i;0..lhs.length){
					if(auto id=getIdFromDefLhs(lhs[i])){
						auto renamed=sc.getRenamed(id);
						if(rhs[i].isQfree()){
							dependencies~=q(renamed.name,rhs[i].getDependency(sc));
						}else{
							dependencies~=q(renamed.name,Dependency(true));
						}
					}else badUnpackLhs=true;
				}
				sc.addDependencies(dependencies);
			}
			void addDependencyMulti(Expression[] lhs,Dependency dependency){
				Q!(string,Dependency)[] dependencies;
				foreach(i;0..lhs.length){
					if(auto id=getIdFromDefLhs(lhs[i])){
						auto renamed=sc.getRenamed(id);
						dependencies~=q(renamed.name,dependency);
					}else badUnpackLhs=true;
				}
				sc.addDependencies(dependencies);
			}
			bool ok=false;
			if(auto id=getIdFromDefLhs(be.e1)){
				addDependencies([id],[be.e2]);
			}else if(auto tpl1=cast(TupleExp)be.e1){
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
			}else badUnpackLhs=true;
		}
	}
	auto de=cast(DefExp)makeDeclaration(be,success,sc);
	static if(language==silq) if(badUnpackLhs) assert(!de||de.sstate==SemState.error);
	if(!de) be.sstate=SemState.error;
	assert(success && de && de.initializer is be || !de||de.sstate==SemState.error);
	auto tt=be.e2.type?be.e2.type.isTupleTy:null;
	if(be.e2.sstate==SemState.completed){
		auto tpl=cast(TupleExp)be.e1;
		if(tpl){
			if(tt){
				if(tpl.length!=tt.length){
					sc.error(text("inconsistent number of tuple entries for definition: ",tpl.length," vs. ",tt.length),de.loc);
					if(de){ de.setError(); be.sstate=SemState.error; }
				}
			}else if(!cast(ArrayTy)be.e2.type){
				sc.error(format("cannot unpack type %s as a tuple",be.e2.type),de.loc);
				if(de){ de.setError(); be.sstate=SemState.error; }
			}
		}else if(auto ce=cast(CallExp)be.e1){
			auto f=ce.e,ft=cast(ProductTy)f.type;
			if(ft){
				bool ok=true;
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
					be.e1.type=ft.cod;
					if(!isSubtype(be.e2.type,be.e1.type)){
						sc.error(format("cannot call reversed function with return type '%s' with a result type of '%s'",be.e1.type,be.e2.type),be.loc);
						ok=false;
					}
				}
				if(!ok&&de){ de.setError(); be.sstate=SemState.error; }
			}
		}
		if(de){
			de.setType(be.e2.type);
			de.setInitializer();
			if(de.sstate!=SemState.error){
				foreach(i,vd;de.decls){
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
			de.type=unit;
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
			if(auto sde=cast(SingleDefExp)blocker) if(sde.decl) blocker=sde.decl;
			typeConstBlock(id.meaning,blocker,sc);
		}
	}
	if(r.sstate!=SemState.error) r.sstate=SemState.completed;
	return finish(r);
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
	return isSubtype(ty,ℤt(true))||isSubtype(ty,Bool(false))||isInt(ty)||isUint(ty);
}

bool guaranteedDifferentValues(Expression e1,Expression e2,Location loc,Scope sc,InType inType){
	if(auto tpl1=cast(TupleExp)unwrap(e1)){
		if(auto tpl2=cast(TupleExp)unwrap(e2))
			return zip(tpl1.e,tpl2.e).any!(x=>guaranteedDifferentValues(x.expand,loc,sc,inType));
		return false;
	}
	e1=expressionSemantic(e1,expSemContext(sc,ConstResult.yes,inType));
	e2=expressionSemantic(e2,expSemContext(sc,ConstResult.yes,inType));
	if(!util.among(e1.type,ℕt(true),ℤt(true))||!util.among(e2.type,ℕt(true),ℤt(true)))
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
	e1=expressionSemantic(e1,expSemContext(sc,ConstResult.yes,inType));
	e2=expressionSemantic(e2,expSemContext(sc,ConstResult.yes,inType));
	if(e1.sstate==SemState.error||e2.sstate==SemState.error)
		return false;
	if(!util.among(e1.type,ℕt(true),ℤt(true))||!util.among(e2.type,ℕt(true),ℤt(true)))
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
	Tuple!(Expression,Declaration,SemState,Scope)[string] consumed;
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
				id.sstate=tpl[2];
				id.scope_=tpl[3];
				return;
			}
			if(id.meaning) id.name=id.meaning.name.name;
			auto oldMeaning=id.meaning;
			id.meaning=null;
			assert(id.sstate!=SemState.completed);
			e.e=expressionSemantic(e.e,context.nestConsumed); // consume array
			if(e.e.sstate!=SemState.completed)
				return;
			// assert(id.meaning is oldMeaning); // TODO. (id.meaning should already move into local scope earlier)
			assert(id.meaning is oldMeaning||oldMeaning.scope_!is context.sc&&id.meaning.scope_ is context.sc,text(id.meaning," ",oldMeaning," ",id.loc));
			assert(id.name==oldMeaning.getName);
			e.e.constLookup=true;
			id=cast(Identifier)unwrap(e.e);
			assert(!!id);
			ids~=id;
			consumed[id.name]=tuple(id.type,id.meaning,e.e.sstate,id.scope_);
		}
		doIt(e);
	}
	void redefineArrays(Location loc,Scope sc){
		SetX!string added;
		foreach(id;ids){
			if(id&&id.meaning&&id.type&&id.name !in added){
				auto var=addVar(id.meaning.name.name,id.type,loc,sc);
				added.insert(id.name);
			}
		}
	}
}
void finishIndexReplacement(DefineExp be,Scope sc){
	auto inType=InType.no;
	auto context=expSemContext(sc,ConstResult.yes,inType);

	auto crepls=sc.localComponentReplacements();
	scope(exit) sc.resetLocalComponentReplacements();
	auto indicesToReplace=crepls.map!(x=>x.write).array;
	assert(indicesToReplace.all!(x=>!!getIdFromIndex(x)));
	ArrayConsumer consumer;
	foreach(ref theIndex;indicesToReplace)
		consumer.consumeArray(theIndex,context);
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
		}
	}
	consumer.redefineArrays(be.loc,sc);
	foreach(theIndex;indicesToReplace)
		if(theIndex.sstate!=SemState.error)
			theIndex.sstate=SemState.completed;
	foreach(idx;indicesToReplace)
		if(auto id=getIdFromIndex(idx))
			if(id.meaning&&id.meaning.rename)
				id.name=id.meaning.rename.name;
}
}

void typeConstBlock(Declaration decl,Expression blocker,Scope sc){
	if(!isAssignable(decl,sc)) return;
	if(auto vd=cast(VarDecl)decl){
		vd.isConst=true;
		vd.typeConstBlocker=blocker;
	}
	assert(!isAssignable(decl,sc));
}

bool isAssignable(Declaration meaning,Scope sc){
	auto vd=cast(VarDecl)meaning;
	if(!vd||vd.isConst||sc.isConst(vd)) return false;
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

bool isNonConstVar(VarDecl vd,Scope sc){
	if(!vd||vd.isConst||sc.isConst(vd))
		return false;
	return true;
}

bool checkNonConstVar(string action,string continuous)(Declaration meaning,Location loc,Scope sc){
	auto vd=cast(VarDecl)meaning;
	if(isNonConstVar(vd,sc)) return true;
	if(vd&&(vd.isConst||sc.isConst(vd))){
		if(cast(Parameter)meaning&&(cast(Parameter)meaning).isConst)
			sc.error("cannot "~action~" 'const' parameters",loc);
		else sc.error("cannot "~action~" 'const' variables",loc);
		if(vd.typeConstBlocker) typeConstBlockNote(vd,sc);
		else if(auto read=sc.isConst(vd))
			sc.note("variable was made 'const' here", read.loc);
	}else if(meaning&&!vd) sc.error(continuous~" non-variables not supported",loc);
		else if(meaning) sc.error("cannot assign",loc);
	return false;
}

bool checkAssignable(Declaration meaning,Location loc,Scope sc,bool quantumAssign=false){
	if(!checkNonConstVar!("reassign","reassigning")(meaning,loc,sc))
		return false;
	auto vd=cast(VarDecl)meaning;
	static if(language==silq){
		if(!quantumAssign&&!vd.vtype.isClassical()&&!sc.canForget(meaning)){
			sc.error("cannot reassign quantum variable", loc);
			return false;
		}
	}
	if(isTypeTy(vd.vtype)){
		sc.error("cannot reassign type variables", loc);
		return false;
	}
	for(auto csc=sc;csc !is meaning.scope_;csc=(cast(NestedScope)csc).parent){
		if(auto fsc=cast(FunctionScope)csc){
			// TODO: what needs to be done to lift this restriction?
				// TODO: method calls are also implicit assignments.
			sc.error("cannot assign to variable in closure context (capturing by value)",loc);
			return false;
		}
	}
	return true;
}

AssignExp assignExpSemantic(AssignExp ae,Scope sc){
	auto context=expSemContext(sc,ConstResult.yes,InType.no);
	ae.type=unit;
	auto constSave=sc.saveConst();
	ae.e1=expressionSemantic(ae.e1,context.nestConst); // reassigned variable should not be consumed (otherwise, can use ':=')
	propErr(ae.e1,ae);
	auto lhsConst=sc.saveConst();
	sc.resetConst(constSave);
	if(ae.sstate==SemState.error)
		return ae;
	void checkLhs(Expression lhs){
		if(auto id=cast(Identifier)lhs){
			if(!checkAssignable(id.meaning,ae.loc,sc))
				ae.sstate=SemState.error;
		}else if(auto tpl=cast(TupleExp)lhs){
			foreach(exp;tpl.e)
				checkLhs(exp);
		}else if(auto idx=cast(IndexExp)lhs){
			checkLhs(idx.e);
		}else if(auto fe=cast(FieldExp)lhs){
			if(isBuiltIn(fe))
				goto LbadAssgnmLhs;
			checkLhs(fe.e);
		}else if(auto tae=cast(TypeAnnotationExp)lhs){
			checkLhs(tae.e);
		}else{
		LbadAssgnmLhs:
			sc.error(format("cannot assign to %s",lhs),ae.e1.loc);
			ae.sstate=SemState.error;
		}
	}
	checkLhs(ae.e1);
	sc.resetConst(lhsConst);
	ae.e2=expressionSemantic(ae.e2,context.nestConsumed);
	sc.resetConst(constSave);
	propErr(ae.e2,ae);
	void checkCompat(Expression lhs,Expression type){
		if(auto id=cast(Identifier)lhs)
			return; // strong update allowed
		if(auto tpl=cast(TupleExp)lhs){
			if(auto tt=type.isTupleTy){
				if(tpl.length!=tt.length){
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
			// TODO: allow strong component updates
			if(!isSubtype(type,lhs.type)){
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
		Dependency[string] dependencies;
		int curDependency;
	}
	void[0][string] consumed;
	void[0][string] defined;
	void updateVars(Expression lhs,Expression rhs,bool expandTuples,Stage stage,bool indexed){
		if(auto id=cast(Identifier)lhs){
			if(id&&id.meaning&&id.meaning.name){
				static if(language==psi){
					if(auto fd=sc.getFunction){
						if(id.meaning is fd.context)
							return; // TODO: this is a hack. treat "this" parameter as ref instead.
					}
				}
				auto rename=id.meaning.getName;
				final switch(stage){
					static if(language==silq){
						case Stage.collectDeps:
							if(rhs.isQfree()){
								auto dep=rhs.getDependency(sc);
								if(indexed) dep.joinWith(lhs.getDependency(sc)); // TODO: index-aware dependency tracking?
								if(rename in dependencies) dep.joinWith(dependencies[rename]);
								dependencies[rename]=dep;
							}
							break;
					}
					case Stage.consumeLhs:
						if(rename !in consumed){
							sc.consume(id.meaning);
							consumed[id.name]=[];
						}
						break;
					case Stage.defineVars:
						if(rename !in defined){
							static if(language==silq){
								if(rhs.isQfree()) sc.addDependency(id.meaning,dependencies[rename]);
							}
							auto name=id.meaning.name.name;
							auto var=addVar(name,indexed?id.type:rhs.type,lhs.loc,sc);
							defined[rename]=[];
						}
						break;
				}
			}
		}else if(auto tpll=cast(TupleExp)lhs){
			bool ok=false;
			if(expandTuples){
				if(auto tplr=cast(TupleExp)rhs){
					if(tpll.e.length==tplr.e.length){
						foreach(i;0..tpll.e.length)
							updateVars(tpll.e[i],tplr.e[i],true,stage,indexed);
						ok=true;
					}
				}
			}
			if(!ok) foreach(exp;tpll.e) updateVars(exp,rhs,false,stage,indexed);
		}else if(auto idx=cast(IndexExp)lhs){
			updateVars(idx.e,rhs,false,stage,true); // TODO: pass indices down?
		}else if(auto fe=cast(FieldExp)lhs){
			updateVars(fe.e,rhs,false,stage,true);
		}else if(auto tae=cast(TypeAnnotationExp)lhs){
			updateVars(tae.e,rhs,expandTuples,stage,indexed);
		}else assert(0);
	}
	if(ae.sstate!=SemState.error){
		static if(language==silq)
			updateVars(ae.e1,ae.e2,true,Stage.collectDeps,false);
		updateVars(ae.e1,ae.e2,true,Stage.consumeLhs,false);
		static if(language==silq){
			foreach(ref dependency;dependencies)
				foreach(name;sc.toPush)
					sc.pushUp(dependency, name);
			sc.pushConsumed();
		}
		updateVars(ae.e1,ae.e2,true,Stage.defineVars,false);
	}
	if(ae.sstate!=SemState.error) ae.sstate=SemState.completed;
	return ae;
}

bool isOpAssignExp(Expression e){
	return cast(OrAssignExp)e||cast(AndAssignExp)e||cast(AddAssignExp)e||cast(SubAssignExp)e||cast(NSubAssignExp)e||cast(MulAssignExp)e||cast(DivAssignExp)e||cast(IDivAssignExp)e||cast(ModAssignExp)e||cast(PowAssignExp)e||cast(CatAssignExp)e||cast(BitOrAssignExp)e||cast(BitXorAssignExp)e||cast(BitAndAssignExp)e;
}

bool isInvertibleOpAssignExp(Expression e){
	return cast(AddAssignExp)e||cast(SubAssignExp)e||cast(NSubAssignExp)e||cast(CatAssignExp)e||cast(BitXorAssignExp)e;
}

ABinaryExp opAssignExpSemantic(ABinaryExp be,Scope sc)in{
	assert(isOpAssignExp(be));
}do{
	auto context=expSemContext(sc,ConstResult.yes,InType.no);
	static if(language==silq){
		// TODO: assignments to fields
		auto semanticDone=false;
		if(auto id=cast(Identifier)be.e1){
			int nerr=sc.handler.nerrors; // TODO: this is a bit hacky
			auto meaning=sc.lookup(id,false,true,Lookup.probing);
			if(nerr!=sc.handler.nerrors){
				sc.note("looked up here",id.loc);
				return be;
			}
			if(meaning){
				id.meaning=meaning;
				id.name=meaning.getName;
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
	if(!semanticDone) be.e1=expressionSemantic(be.e1,context.nestConsumed);
	be.e2=expressionSemantic(be.e2,context.nest(cast(CatAssignExp)be?ConstResult.no:ConstResult.yes));
	propErr(be.e1,be);
	propErr(be.e2,be);
	if(be.sstate==SemState.error)
		return be;
	void checkULhs(Expression lhs){
		if(auto id=cast(Identifier)lhs){
			if(!checkAssignable(id.meaning,be.loc,sc,isInvertibleOpAssignExp(be)))
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
	Expression ce=null;
	import ast.parser;
	static foreach(op;binaryOps){
		static if(op.endsWith("←")){
			if(auto ae=cast(BinaryExp!(Tok!op))be){
				ce=new BinaryExp!(Tok!(op[0..$-"←".length]))(be.e1, be.e2);
				ce.loc=be.loc;
			}
		}
	}
	assert(!!ce);
	ce=expressionSemantic(ce,context.nestConsumed);
	propErr(ce, be);
	checkULhs(be.e1);
	static if(language==silq){
		if(be.sstate!=SemState.error&&!be.e1.type.isClassical()){
			auto id=cast(Identifier)be.e1;
			if(!id){
				sc.error(format("cannot update-assign to quantum expression %s",be.e1),be.e1.loc);
				be.sstate=SemState.error;
			}else if((!isInvertibleOpAssignExp(be)||be.e2.hasFreeIdentifier(id.name))&&id.meaning&&!sc.canForget(id.meaning)){
				sc.error("quantum update must be invertible",be.loc);
				be.sstate=SemState.error;
			}
		}
	}
	if(be.sstate!=SemState.error){
		auto id=cast(Identifier)be.e1;
		if(id&&id.meaning&&id.meaning.name){
			void consume(){
				sc.consume(id.meaning);
				static if(language==silq)
					sc.pushConsumed();
			}
			void define(){
				auto name=id.meaning.name.name;
				addVar(name,ce.type,be.loc,sc);
			}
			static if(language==silq){
				bool ok=false;
				if(be.e2.isQfree()){
					auto dependency=sc.getDependency(id.meaning);
					dependency.joinWith(be.e2.getDependency(sc));
					consume();
					sc.addDependency(id.meaning,dependency);
					define();
				}else{
					consume();
					define();
				}
			}else{
				consume();
				define();
			}
		}
	}
	be.type=unit;
	if(be.sstate!=SemState.error) be.sstate=SemState.completed;
	return be;
}

bool isAssignment(Expression e){
	return cast(AssignExp)e||isOpAssignExp(e);
}

Expression assignSemantic(Expression e,Scope sc)in{
	assert(isAssignment(e));
}do{
	if(auto ae=cast(AssignExp)e) return assignExpSemantic(ae,sc);
	if(isOpAssignExp(e)) return opAssignExpSemantic(cast(ABinaryExp)e,sc);
	assert(0);
}

bool isDefineOrAssign(Expression e){
	return isAssignment(e)||cast(DefineExp)e||cast(DefExp)e;
}

Expression defineOrAssignSemantic(Expression e,Scope sc)in{
	assert(isDefineOrAssign(e));
}do{
	if(isAssignment(e)) return assignSemantic(e,sc);
	if(auto be=cast(DefineExp)e) return defineSemantic(be,sc);
	if(auto de=cast(DefExp)e) return defineOrAssignSemantic(de.initializer,sc); // (for copied functions)
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

Identifier getReverse(Location loc,Scope isc,Annotation annotation,bool checked)in{
	assert(annotation>=Annotation.mfree);
}do{
	auto r=getPreludeSymbol(annotation==Annotation.qfree?"__reverse_qfree":"reverse",loc,isc);
	if(!checked) r.checkReverse=false; // TODO: is there a better solution than this for frontend reverse?
	return r;
}

bool isReverse(Identifier id){
	if(!id) return false;
	if(id.name!="reverse") return false;
	return id.meaning&&isReverse(id.meaning);
}

bool isReverse(Declaration decl){
	if(preludePath() !in modules) return false;
	auto exprssc=modules[preludePath()];
	auto sc=exprssc[1];
	if(!decl||decl.scope_ !is sc) return false;
	if(!decl.name) return false;
	return decl.getName=="reverse";
}

auto isConstForReverse(FunTy ft){
	return iota(ft.nargs).map!(i=>ft.isConst[i]||ft.argTy(i).isClassical&&!ft.argTy(i).isQuantum);
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

Expression[] makeIndexLookups(I)(string name,I indices,Location loc){
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
		auto id=new Identifier(p.name.name);
		id.meaning=p;
		id.loc=p.loc;
		Expression r=id;
		return r;
	}).array;
	auto narg=isTuple?new TupleExp(args):args[0];
	narg.loc=loc;
	return narg;
}

Expression makeReverseCall(Expression ce1,Annotation annotation,bool check,Scope sc,Location loc){
	auto ce2=new CallExp(getReverse(loc,sc,annotation,check),ce1,false,false);
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

Expression tryReverseSemantic(CallExp ce,ExpSemContext context){
	auto sc=context.sc;
	auto calledId=cast(Identifier)ce.e;
	assert(calledId&&isReverse(calledId));
	bool check=calledId.checkReverse;
	ce.arg=expressionSemantic(ce.arg,/+context.nest((rft.isConst.length?rft.isConst[0]:true)?ConstResult.yes:ConstResult.no)+/context.nestConst);
	auto f=ce.arg;
	auto ft=cast(FunTy)f.type;
	if(!ft) return null;
	auto ft2=cast(FunTy)ft.cod;
	if(ft2&&ft.isSquare&&ft.isConst.all&&!ft2.isSquare){
		auto loc=f.loc;
		auto names=iota(ft.names.length).map!(i=>"`arg_"~(ft.names[i]?ft.names[i]:text(i)));
		auto types=iota(ft.nargs).map!((i){
			auto type=ft.argTy(i);
			if(type==typeTy){
				bool check(Expression ty){
					if(ty.isQuantum) return true;
					return !ty.hasFreeVar(ft.names[i]);
				}
				bool ok=true;
				foreach(j;0..ft2.nargs){
					if(ft2.isConstForReverse[j]) continue;
					ok&=check(ft2.argTy(j));
					if(!ok) break;
				}
				if(ok) ok&=check(ft2.cod);
				if(!ok) type=qtypeTy;
			}
			return type;
		});
		auto params=makeParams(ft.isConst,names,types,loc);
		auto narg=lookupParams(params,ft.isTuple,loc);
		auto ce1=new CallExp(f.copy,narg,true,false);
		ce1.loc=loc;
		auto ce2=makeReverseCall(ce1,Annotation.mfree,check,sc,loc);
		auto body_=makeLambdaBody(ce2,loc);
		auto le=makeLambda(params,ft.isTuple,ft.isSquare,ft.annotation,body_,loc);
		return expressionSemantic(le,context);
	}
	if(check && ft.annotation<Annotation.mfree){
		sc.error("reversed function must be 'mfree'",f.loc);
		ce.sstate=SemState.error;
	}
	if(check && !ft.isClassical_){
		sc.error("reversed function must be classical",f.loc);
		ce.sstate=SemState.error;
	}
	if(ft.cod.hasAnyFreeVar(ft.names)){
		sc.error("arguments of reversed function call cannot appear in return value",f.loc);
		ce.sstate=SemState.error;
	}
	if(ce.sstate!=SemState.error){
		auto loc=f.loc;
		auto r=reverseCallRewriter(ft,loc);
		if(!r.innerNeeded){
			if(!calledId.checkReverse){
				if(equal(ft.isConst,only(true,false))){
					auto τ=ft.argTy(0),χ=ft.argTy(1),φ=ft.cod;
					auto arg=new TupleExp([τ,χ,φ]);
					arg.loc=ce.e.loc;
					arg.type=tupleTy([τ.type,χ.type,φ.type]);
					arg.sstate=SemState.completed;
					auto nce=new CallExp(ce.e,arg,true,false);
					nce.loc=ce.e.loc;
					auto rtype=funTy([true,false],tupleTy([τ,φ]),χ,ft.isSquare,true,ft.annotation,ft.isClassical);
					nce.type=funTy([true],ce.arg.type,rtype,false,false,Annotation.qfree,ft.isClassical);
					nce.sstate=SemState.completed;
					auto res=new CallExp(nce,ce.arg,ce.isSquare,ce.isClassical);
					res.type=rtype;
					res.sstate=SemState.completed;
					return res;
				}
			}
			return null;
		}
		if(check&&r.movedType.hasClassicalComponent()){
			sc.error("reversed function cannot have classical components in 'moved' arguments", f.loc);
			ce.sstate=SemState.error;
		}
		if(check&&r.returnType.hasClassicalComponent()){
			sc.error("reversed function cannot have classical components in return value", f.loc);
			ce.sstate=SemState.error;
		}
		if(ce.sstate==SemState.error)
			return ce;
		auto le=r.wrapInner(f);
		auto rev=makeReverseCall(le,ft.annotation,check,sc,loc);
		if(!r.outerNeeded) return expressionSemantic(rev,context);
		auto le2=r.wrapOuter(rev,true);
		return expressionSemantic(le2,context);
	}
	return null;
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
		if(ce&&ce.sstate!=SemState.error){
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
				if(ft.annotation<sc.restriction()){
					if(ft.annotation==Annotation.none){
						sc.error(format("cannot call function '%s' in '%s' context", ce.e, annotationToString(sc.restriction())), ce.loc);
					}else{
						sc.error(format("cannot call '%s' function '%s' in '%s' context", ft.annotation, ce.e, annotationToString(sc.restriction())), ce.loc);
					}
					ce.sstate=SemState.error;
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
						}else{
							auto isConst=(ft.nargs==tpl.e.length?ft.isConstForReverse[i]:defaultIsConst);
						}
						exp=argSemantic(exp,context.nest(isConst?ConstResult.yes:ConstResult.no));
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
				}else{
					auto isConst=(ft.isConst.length?ft.isConstForReverse[0]:true);
				}
				ce.arg=argSemantic(ce.arg,context.nest(isConst?ConstResult.yes:ConstResult.no));
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
			}else{
				auto isConst=ft.isConstForReverse[0];
			}
			ce.arg=argSemantic(ce.arg,context.nest(isConst?ConstResult.yes:ConstResult.no));
			assert(ft.names.length==1);
			static if(isRhs) checkArg(0,ce.arg);
		}
		return false;
	}
	Expression checkFunCall(FunTy ft){
		bool tryCall(){
			if(!ce.isSquare && ft.isSquare){
				auto nft=ft;
				if(auto id=cast(Identifier)fun){
					if(auto decl=cast(DatDecl)id.meaning){
						if(auto constructor=cast(FunctionDef)decl.body_.ascope_.lookup(decl.name,false,false,Lookup.consuming)){
							if(auto cty=cast(FunTy)typeForDecl(constructor)){
								assert(isTypeTy(ft.cod));
								nft=productTy(ft.isConst,ft.names,ft.dom,cty,ft.isSquare,ft.isTuple,ft.annotation,true);
							}
						}
					}
				}
				if(auto codft=cast(ProductTy)nft.cod){
					if(matchArg(codft)) return true;
					propErr(ce.arg,ce);
					if(ce.arg.sstate==SemState.error) return true;
					static if(isRhs){
						Expression garg;
						auto tt=nft.tryMatch(ce.arg,garg);
						if(!tt) return false;
						auto nce=new CallExp(ce.e,garg,true,false);
						nce.loc=ce.loc;
						auto nnce=new CallExp(nce,ce.arg,false,false);
						nnce.loc=ce.loc;
						nnce=cast(CallExp)callSemantic(nnce,context.nestConsumed);
						assert(!!nnce);
						ce=nnce;
						return true;
					}else{
						// TODO: need to analyze arguments!
						return true;
					}
				}
			}
			if(matchArg(ft)) return true;
			propErr(ce.arg,ce);
			if(ce.arg.sstate==SemState.error) return true;
			static if(isRhs){
				ce.type=ft.tryApply(ce.arg,ce.isSquare);
				return !!ce.type;
			}else{
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
		auto constructor=cast(FunctionDef)decl.body_.ascope_.lookup(decl.name,false,false,Lookup.consuming);
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
				auto id=new Identifier(constructor.name.name);
				id.loc=fun.loc;
				id.scope_=sc;
				id.meaning=constructor;
				id.name=constructor.getName;
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
					case "quantumPrimitive":
						return handleQuantumPrimitive(ce, context);
					case "__show":
						ce.arg=expressionSemantic(ce.arg,context.nestConst);
						auto lit=cast(LiteralExp)ce.arg;
						if(lit&&lit.lit.type==Tok!"``") stderr.writeln(lit.lit.str);
						else stderr.writeln(ce.arg);
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

bool unrealizable(Expression e){ // TODO: can we get rid of this concept?
	return util.among(e,ℕt(false),ℤt(false),ℚt(false),ℝ(false),ℂ(false));
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
auto nestConst(T)(ref T context){
	return context.nest(ConstResult.yes);
}
auto nestConsumed(T)(ref T context){
	return context.nest(ConstResult.no);
}

Expression conditionSemantic(bool allowQuantum=false)(Expression e,Scope sc,InType inType){
	e=expressionSemantic(e,expSemContext(sc,ConstResult.yes,inType));
	static if(language==silq) sc.pushConsumed();
	if(e.sstate==SemState.completed && (allowQuantum?!cast(BoolTy)e.type:e.type!=Bool(true))){
		static if(language==silq){
			static if(allowQuantum) sc.error(format("type of condition should be !𝔹 or 𝔹, not %s",e.type),e.loc);
			else sc.error(format("type of condition should be !𝔹, not %s",e.type),e.loc);
		}else sc.error(format("type of condition should be 𝔹, not %s",e.type),e.loc);
		e.sstate=SemState.error;
	}
	return e;
}

Expression expressionSemanticImpl(IteExp ite,ExpSemContext context){
	auto sc=context.sc, inType=context.inType;
	ite.cond=conditionSemantic!true(ite.cond,sc,inType);
	if(ite.then.s.length!=1||ite.othw&&ite.othw.s.length!=1){
		sc.error("branch of if expression must be single expression",ite.then.s.length!=1?ite.then.loc:ite.othw.loc);
		ite.sstate=SemState.error;
		return ite;
	}
	static if(language==silq){
		auto quantumControl=ite.cond.type!=Bool(true);
		auto restriction_=quantumControl?Annotation.mfree:Annotation.none;
	}else{
		enum quantumControl=false;
		enum restriction_=Annotation.none;
	}
	int numBottom=0; // TODO: actually introduce a bottom type?
	Expression branchSemantic(Expression branch,Scope sc){
		auto context=expSemContext(sc,context.constResult,context.inType);
		if(inType) return expressionSemantic(branch,context);
		if(auto ae=cast(AssertExp)branch){
			branch=statementSemantic(branch,sc);
			if(auto lit=cast(LiteralExp)ae.e)
				if(lit.lit.type==Tok!"0" && lit.lit.str=="0"){
					branch.type=null;
					++numBottom;
				}
		}else branch=expressionSemantic(branch,context);
		return branch;
	}
	// initialize scopes, to allow captures to be inserted
	ite.then.blscope_=new BlockScope(sc,restriction_);
	if(ite.othw) ite.othw.blscope_=new BlockScope(sc,restriction_);
	ite.then.s[0]=branchSemantic(ite.then.s[0],ite.then.blscope_);
	static if(language==silq) ite.then.blscope_.pushConsumed();
	propErr(ite.then.s[0],ite.then);
	if(!ite.othw){
		sc.error("missing else for if expression",ite.loc);
		ite.sstate=SemState.error;
		return ite;
	}
	ite.othw.s[0]=branchSemantic(ite.othw.s[0],ite.othw.blscope_);
	static if(language==silq) ite.othw.blscope_.pushConsumed();
	propErr(ite.othw.s[0],ite.othw);
	propErr(ite.cond,ite);
	propErr(ite.then,ite);
	propErr(ite.othw,ite);
	if(ite.sstate==SemState.error)
		return ite;
	if(!ite.then.s[0].type) ite.then.s[0].type = ite.othw.s[0].type;
	if(!ite.othw.s[0].type) ite.othw.s[0].type = ite.then.s[0].type;
	auto t1=ite.then.s[0].type;
	auto t2=ite.othw.s[0].type;
	ite.type=joinTypes(t1,t2);
	if(!t1 && !t2 && numBottom==2){
		ite.type=ite.then.s[0].type=ite.othw.s[0].type=unit;
	}
	if(t1 && t2 && !ite.type){
		sc.error(format("incompatible types %s and %s for branches of if expression",t1,t2),ite.loc);
		ite.sstate=SemState.error;
	}
	if(quantumControl&&ite.type&&ite.type.hasClassicalComponent()){
		// TODO: automatically promote to quantum if possible
		sc.error(format("type '%s' of if expression with quantum control has classical components",ite.type),ite.loc);
		ite.sstate=SemState.error;
	}
	if(sc.merge(quantumControl,ite.then.blscope_,ite.othw.blscope_)){
		sc.note("consumed in one branch of if expression", ite.loc);
		ite.sstate=SemState.error;
	}
	return ite;
}

Expression expressionSemanticImpl(LiteralExp le,ExpSemContext context){
	switch(le.lit.type){
		case Tok!"0",Tok!".0":
			if(!le.type)
				le.type=le.lit.str.canFind(".")?ℝ(true):le.lit.str.canFind("-")?ℤt(true):ℕt(true); // TODO: type inference
			return le;
		case Tok!"``":
			le.type=stringTy(true);
			return le;
		default:
			return expressionSemanticImplDefault(le,context);
	}
}

Expression expressionSemanticImpl(LambdaExp le,ExpSemContext context){
	auto sc=context.sc;
	FunctionDef nfd=le.fd;
	if(!le.fd.scope_){
		le.fd.scope_=context.sc;
		nfd=cast(FunctionDef)presemantic(nfd,sc);
	}else assert(le.fd.scope_ is sc);
	assert(!!nfd);
	le.fd=functionDefSemantic(nfd,sc);
	assert(!!le.fd);
	propErr(le.fd,le);
	if(le.fd.sstate==SemState.completed){
		le.type=typeForDecl(le.fd);
		le.sstate=SemState.completed;
	}
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
				auto name=meaning.rename?meaning.rename:meaning.name;
				if(!name||!sc.dependencyTracked(name)) return false;
				return sc.canForget(meaning);
			}else return false;
		}else return true;
	}
	auto canForgetImplicitly=checkImplicitForget(fe.var);
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
		if(id.type&&id.type.isClassical){
			if(!sc.consume(meaning)){
				sc.error("cannot forget variable from outer scope",id.loc);
				fe.sstate=SemState.error;
				return;
			}
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

Declaration lookupMeaning(Identifier id,Lookup lookup,Scope sc){
	if(id.meaning) return id.meaning;
	int nerr=sc.handler.nerrors; // TODO: this is a bit hacky
	id.meaning=sc.lookup(id,false,true,lookup);
	if(nerr!=sc.handler.nerrors){
		sc.note("looked up here",id.loc);
		id.sstate=SemState.error;
	}
	return id.meaning;
}

Expression expressionSemanticImpl(Identifier id,ExpSemContext context){
	auto sc=context.sc;
	id.scope_=sc;
	if(id.sstate==SemState.error) return id;
	auto meaning=id.meaning;
	if(!meaning){
		meaning=lookupMeaning(id,context.constResult?Lookup.constant:Lookup.consuming,sc);
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
			return id;
		}else{
			static if(language==silq){
				if(!id.indexedDirectly){
					auto crepls=sc.componentReplacements(meaning);
					if(crepls.length){
						sc.error(format("cannot access aggregate '%s' while its components are being replaced",meaning.getName),id.loc);
						if(crepls[0].write) sc.note("replaced component is here",crepls[0].write.loc);
						id.sstate=SemState.error;
					}
				}
			}
		}
		if(auto fd=cast(FunctionDef)meaning)
			if(auto asc=isInDataScope(fd.scope_))
				if(fd.name.name==asc.decl.name.name)
					meaning=asc.decl;
		id.meaning=meaning;
	}
	id.name=meaning.getName;
	propErr(meaning,id);
	id.type=id.typeFromMeaning;
	if(!id.type&&id.sstate!=SemState.error){
		sc.error("invalid forward reference",id.loc);
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
	auto vd=cast(VarDecl)meaning;
	if(vd){
		if(cast(TopScope)vd.scope_||isTypeTy(vd.vtype)&&vd.initializer){
			if(!vd.initializer||vd.initializer.sstate!=SemState.completed)
				id.sstate=SemState.error;
			id.substitute=true;
			return id;
		}
	}
	if(id.type&&meaning.scope_&&meaning.scope_.getFunction()){
		bool hasQuantumComponent=id.type.hasQuantumComponent();
		bool captureChecked=!hasQuantumComponent;
		assert(sc.isNestedIn(meaning.scope_));
		auto startScope=sc;
		for(auto csc=sc;csc !is meaning.scope_;csc=(cast(NestedScope)csc).parent){
			bool checkCapture(){
				static if(language==silq){
					if(id.meaning&&sc.componentReplacements(id.meaning).length){
						return false; // not captured, will be replaced
					}else if(!astopt.allowUnsafeCaptureConst){
						if(context.constResult){
							sc.error("cannot capture quantum variable as constant", id.loc);
							id.sstate=SemState.error;
							return false;
						}else if(vd&&(vd.isConst||sc.isConst(vd))){
							sc.error("cannot capture 'const' quantum variable", id.loc);
							if(auto read=sc.isConst(vd))
								sc.note("variable was made 'const' here", read.loc);
							id.sstate=SemState.error;
							return false;
						}
					}
				}
				return true;
			}
			if(auto fsc=cast(FunctionScope)csc){
				if(!captureChecked){
					captureChecked=true;
					if(!checkCapture()) break;
				}
				if(hasQuantumComponent){
					if(fsc.fd&&fsc.fd.context&&fsc.fd.context.vtype==contextTy(true)){
						if(!fsc.fd.ftype) fsc.fd.context.vtype=contextTy(false);
						else{
							assert(fsc.fd.ftype.isClassical_);
							sc.error("cannot capture quantum variable in classical function", id.loc);
							id.sstate=SemState.error;
							break;
						}
					}
				}
				fsc.addCapture(id,startScope);
				startScope=fsc;
			}
			if(auto dsc=cast(DataScope)csc){
				if(!captureChecked){
					captureChecked=true;
					if(!checkCapture()) break;
				}
				dsc.addCapture(id,startScope);
				startScope=dsc;
			}
		}
	}
	return id;
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
			fe.f.name=meaning.getName;
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
				auto len=vt.num.copy();
				len.loc=fe.loc;
				return expressionSemantic(len,context);// TODO: preserve semantic on clone
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
	idx.e=expressionSemantic(idx.e,context.nestConst);
	propErr(idx.e,idx);
	bool replaceIndex=false;
	size_t replaceIndexLoc=size_t.max;
	static if(language==silq)
	if(auto cid=getIdFromIndex(idx)) if(cid.meaning){
		auto crepls=sc.componentReplacements(cid.meaning);
		foreach(i,ref crepl;crepls){
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
							sc.error("'const' lookup of index may refer to consumed value",idx.loc);
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
	if(auto ft=cast(FunTy)idx.e.type){
		assert(!replaceIndex);
		auto ce=new CallExp(idx.e,idx.a,true,false);
		ce.loc=idx.loc;
		return callSemantic(ce,context);
	}
	if(isType(idx.e)||isQNumeric(idx.e)){
		assert(!replaceIndex);
		if(auto tty=typeSemantic(idx,sc,true))
			return tty;
	}
	idx.a=expressionSemantic(idx.a,context.nestConst);
	propErr(idx.a,idx);
	if(idx.sstate==SemState.error)
		return idx;
	Expression check(Expression next,Expression index,Expression indexTy,Location indexLoc){
		if(isBasicIndexType(indexTy)){
			if(!indexTy.isClassical()&&next.hasClassicalComponent()){
				sc.error(format("cannot use quantum index to index array whose elements of type '%s' have classical components",next),indexLoc);
				idx.sstate=SemState.error;
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
		sc.error(format("index should be integer, not %s",indexTy),indexLoc);
		idx.sstate=SemState.error;
		return null;
	}
	if(auto at=cast(ArrayTy)idx.e.type){
		idx.type=check(at.next, idx.a, idx.a.type, idx.a.loc);
	}else if(auto vt=cast(VectorTy)idx.e.type){
		idx.type=check(vt.next, idx.a, idx.a.type, idx.a.loc);
	}else if(isInt(idx.e.type)||isUint(idx.e.type)){
		idx.type=check(Bool(idx.e.type.isClassical()), idx.a, idx.a.type, idx.a.loc);
	}else if(auto tt=cast(TupleTy)idx.e.type){
		Expression checkTpl(Expression index){
			if(auto lit=cast(LiteralExp)index){
				if(lit.lit.type==Tok!"0"){
					auto c=ℤ(lit.lit.str);
					if(c<0||c>=tt.types.length){
						sc.error(format("index for type %s is out of bounds [0..%s)",tt,tt.types.length),index.loc);
						idx.sstate=SemState.error;
						return null;
					}else{
						return tt.types[cast(size_t)c.toLong()];
					}
				}
			}
			if(auto tpl=cast(TupleExp)index){
				auto types=tpl.e.map!(e=>checkTpl(e)).array;
				if(types.all!(e=>e!is null)) return tupleTy(types);
				return null;
			}
			sc.error(format("index for type %s should be integer constant",tt),index.loc); // TODO: allow dynamic indexing if known to be safe?
			idx.sstate=SemState.error;
			return null;
		}
		idx.type=checkTpl(idx.a);
	}else{
		sc.error(format("type %s is not indexable",idx.e.type),idx.loc);
		idx.sstate=SemState.error;
	}
	static if(language==silq)
	if(replaceIndex){
		idx.byRef=true;
		auto cid=getIdFromIndex(idx);
		assert(cid&&cid.meaning);
		auto crepls=sc.componentReplacements(cid.meaning);
		assert(replaceIndexLoc<crepls.length);
		if(context.constResult){
			sc.error("replaced component must be consumed",idx.loc);
			sc.note("replaced component is here",crepls[replaceIndexLoc].write.loc);
			idx.sstate=SemState.error;
		}
		crepls[replaceIndexLoc].read=idx; // matched
		auto id=new Identifier(crepls[replaceIndexLoc].name);
		id.loc=idx.loc;
		return expressionSemantic(id,context);
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
	if(auto at=cast(ArrayTy)sl.e.type){
		sl.type=at;
	}else if(auto vt=cast(VectorTy)sl.e.type){
		auto se=new NSubExp(sl.r,sl.l);
		se.type=ℕt(true);
		se.sstate=SemState.completed;
		sl.type=vectorTy(vt.next,se.eval());
	}else if(auto tt=sl.e.type.isTupleTy){
		auto llit=cast(LiteralExp)sl.l, rlit=cast(LiteralExp)sl.r;
		if(!llit||llit.lit.type!=Tok!"0"){
			sc.error(format("slice lower bound for type %s should be integer constant",cast(Expression)tt),sl.loc);
			sl.sstate=SemState.error;
		}
		if(!rlit||rlit.lit.type!=Tok!"0"){
			sc.error(format("slice upper bound for type %s should be integer constant",cast(Expression)tt),sl.loc);
			sl.sstate=SemState.error;
		}
		if(sl.sstate==SemState.error)
			return sl;
		auto lc=ℤ(llit.lit.str), rc=ℤ(rlit.lit.str);
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

Expression expressionSemanticImpl(ArrayExp arr,ExpSemContext context){
	auto sc=context.sc;
	Expression t; bool tok=true;
	foreach(i,ref exp;arr.e){
		exp=expressionSemantic(exp,context);
		propErr(exp,arr);
		auto nt = joinTypes(t, exp.type);
		if(!nt&&tok){
			Expression texp;
			foreach(j,oexp;arr.e[0..i]){
				if(!joinTypes(oexp, exp)){
					texp=oexp;
					break;
				}
			}
			if(texp){
				sc.error(format("incompatible types %s and %s in array literal",t,exp.type),texp.loc);
				sc.note("incompatible entry",exp.loc);
			}
			arr.sstate=SemState.error;
			tok=false;
		}else t=nt;
	}
	if(arr.e.length && t){
		if(arr.e[0].type) arr.type=arrayTy(t);
	}else arr.type=arrayTy(ℝ(true)); // TODO: type inference?
	return arr;
}

Expression expressionSemanticImpl(TypeAnnotationExp tae,ExpSemContext context){
	auto sc=context.sc;
	tae.e=expressionSemantic(tae.e,context);
	tae.type=typeSemantic(tae.t,sc);
	propErr(tae.e,tae);
	propErr(tae.t,tae);
	if(!tae.type) tae.sstate=SemState.error;
	if(tae.sstate==SemState.error)
		return tae;
	if(auto arr=cast(ArrayExp)tae.e){
		if(!arr.e.length){
			if(auto aty=cast(ArrayTy)tae.type)
				arr.type=aty;
			if(auto vty=cast(VectorTy)tae.type)
				arr.type=arrayTy(vty.next);
		}
	}
	if(auto ce=cast(CallExp)tae.e)
		if(auto id=cast(Identifier)ce.e){
			if(id.name=="sampleFrom"||id.name=="readCSV"&&tae.type==arrayTy(arrayTy(ℝ(true))))
				ce.type=tae.type;
		}
	bool typeExplicitConversion(Expression from,Expression to,TypeAnnotationType annotationType){
		if(isSubtype(from,to)) return true;
		if(annotationType==annotationType.punning){
			auto ft1=cast(ProductTy)from, ft2=cast(ProductTy)to;
			if(ft1&&ft2&&ft1.setAnnotation(Annotation.none)==ft2.setAnnotation(Annotation.none))
				return true;
			return false;
		}
		if(annotationType>=annotationType.conversion){
			if(isSubtype(from,ℤt(true))&&(isUint(to)||isInt(to)))
				return true;
			if(isUint(from)&&isSubtype(ℕt(from.isClassical()),to))
				return true;
			if(isInt(from)&&isSubtype(ℤt(from.isClassical()),to))
				return true;
			if((isRat(from)||isFloat(from))&&isSubtype(ℚt(from.isClassical()),to))
				return true;
			auto ce1=cast(CallExp)from;
			if(ce1&&(isInt(ce1)||isUint(ce1))&&(isSubtype(vectorTy(Bool(ce1.isClassical()),ce1.arg),to)||isSubtype(arrayTy(Bool(ce1.isClassical())),to)))
				return true;
			auto ce2=cast(CallExp)to;
			if(ce2&&(isInt(ce2)||isUint(ce2))&&(isSubtype(from,vectorTy(Bool(ce2.isClassical()),ce2.arg))||annotationType==TypeAnnotationType.coercion&&isSubtype(from,arrayTy(Bool(ce2.isClassical())))))
				return true;
		}
		auto tpl1=from.isTupleTy(), tpl2=to.isTupleTy();
		if(tpl1&&tpl2&&tpl1.length==tpl2.length&&iota(tpl1.length).all!(i=>typeExplicitConversion(tpl1[i],tpl2[i],annotationType)))
			return true;
		auto arr1=cast(ArrayTy)from, arr2=cast(ArrayTy)to;
		if(arr1&&arr2&&typeExplicitConversion(arr1.next,arr2.next,annotationType))
			return true;
		auto vec1=cast(VectorTy)from, vec2=cast(VectorTy)to;
		if(vec1&&vec2&&vec1.num.eval()==vec2.num.eval()&&typeExplicitConversion(vec1.next,vec2.next,annotationType))
			return true;
		if(vec1&&arr2&&typeExplicitConversion(vec1.next,arr2.next,annotationType))
			return true;
		if(annotationType==TypeAnnotationType.coercion){
			if((arr1||vec1)&&to==unit) return true;
			if(vec1&&vec2&&typeExplicitConversion(vec1.next,vec2.next,annotationType))
				return true;
			if(arr1&&vec2&&typeExplicitConversion(arr1.next,vec2.next,annotationType))
				return true;
			if(vec1&&tpl2&&iota(tpl2.length).all!(i=>typeExplicitConversion(vec1.next,tpl2[i],annotationType)))
				return true;
			if(tpl1&&vec2&&iota(tpl1.length).all!(i=>typeExplicitConversion(tpl1[i],vec2.next,annotationType)))
				return true;
			if(from.isClassical()&&isSubtype(to.getClassical(),from)&&from.isNumeric) return true;
		}
		return false;
	}
	bool annotateLiteral(Expression expr, Expression type){
		auto lit=cast(LiteralExp)expr, negLit=cast(UMinusExp)expr?cast(LiteralExp)(cast(UMinusExp)expr).e:null;
		if(!lit&&!negLit) return false;
		bool check(){
			if(isSubtype(expr.type,ℕt(false))&&(isUint(type)||isInt(type)))
				return true;
			if(isSubtype(expr.type,ℤt(false))&&isInt(type))
				return true;
			if(isSubtype(expr.type,ℝ(false))&&isSubtype(ℚt(true),type))
				return true;
			if(isSubtype(expr.type,ℝ(false))&&(isRat(type)||isFloat(type)))
				return true;
			if(lit&&cast(BoolTy)type&&lit.lit.type==Tok!"0"&&!lit.lit.str.canFind(".")){
				auto val=ℤ(lit.lit.str);
				if(val==0||val==1) return true;
			}
			return false;
		}
		if(!check()) return false;
		auto ltype=type.getClassical();
		if(negLit){
			assert(minusType(ltype)==ltype);
			negLit.type=ltype;
		}
		expr.type=ltype;
		return true;
	}
	bool explicitConversion(Expression expr,Expression type,TypeAnnotationType annotationType){
		if(annotationType==annotationType.punning) return typeExplicitConversion(expr.type,type,annotationType);
		if(annotateLiteral(expr,type)) return true;
		if(typeExplicitConversion(expr.type,type,annotationType)) return true;
		if(auto tpl1=cast(TupleExp)expr){
			scope(success) expr.type=tupleTy(tpl1.e.map!(e=>e.type).array);
			if(auto tpl2=type.isTupleTy()){
				return tpl1.e.length==tpl2.length&&iota(tpl1.e.length).all!(i=>explicitConversion(tpl1.e[i],tpl2[i],annotationType));
			}
			if(auto arr=cast(ArrayTy)type){
				return iota(tpl1.e.length).all!(i=>explicitConversion(tpl1.e[i],arr.next,annotationType));
			}
			if(auto vec2=cast(VectorTy)type){
				bool ok=annotationType==TypeAnnotationType.coercion;
				if(!ok){
					auto len=LiteralExp.makeInteger(tpl1.e.length);
					len.loc=expr.loc;
					auto eq=new EqExp(len,vec2.num);
					eq.loc=expr.loc;
					ok=eq.eval()==LiteralExp.makeBoolean(1);
				}
				if(ok){
					return iota(tpl1.e.length).all!(i=>explicitConversion(tpl1.e[i],vec2.next,annotationType));
				}
			}
		}
		return false;
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
	if(isInt(t1) && isSubtype(t2,ℤt(t1.isClassical()))) return t1; // TODO: automatic promotion to quantum
	if(isInt(t2) && isSubtype(t1,ℤt(t2.isClassical()))) return t2;
	if(isUint(t1) && isSubtype(t2,ℤt(t1.isClassical()))) return t1;
	if(isUint(t2) && isSubtype(t1,ℤt(t2.isClassical()))) return t2;
	if(preludeNumericTypeName(t1) != null||preludeNumericTypeName(t2) != null)
		return joinTypes(t1,t2);
	if(!isNumeric(t1)||!isNumeric(t2)) return null;
	auto r=joinTypes(t1,t2);
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
	if(isInt(r)||isUint(r)) return null; // TODO: add a special operator for float and rat?
	return util.among(r,Bool(true),ℕt(true),ℤt(true))?ℚt(true):
		util.among(r,Bool(false),ℕt(false),ℤt(false))?ℚt(false):r;
}
Expression iDivType(Expression t1, Expression t2){
	auto r=arithmeticType!false(t1,t2);
	if(isInt(r)||isUint(r)) return r;
	if(cast(ℂTy)t1||cast(ℂTy)t2) return null;
	bool classical=t1.isClassical()&&t2.isClassical();
	return (cast(BoolTy)t1||cast(ℕTy)t1)&&(cast(BoolTy)t2||cast(ℕTy)t2)?ℕt(classical):ℤt(classical);
}
Expression nSubType(Expression t1, Expression t2){
	auto r=arithmeticType!true(t1,t2);
	if(isUint(r)) return r;
	if(isSubtype(r,ℕt(false))) return r;
	if(isSubtype(r,ℤt(false))) return ℕt(r.isClassical());
	return null;
}
Expression moduloType(Expression t1, Expression t2){
	auto r=arithmeticType!false(t1,t2);
	return r==ℤt(true)?ℕt(true):r==ℤt(false)?ℕt(false):r; // TODO: more general range information?
}
Expression powerType(Expression t1, Expression t2){
	bool classical=t1.isClassical()&&t2.isClassical();
	if(!isNumeric(t1)||!isNumeric(t2)) return null;
	if(cast(BoolTy)t1&&isSubtype(t2,ℕt(classical))) return Bool(classical);
	if(cast(ℕTy)t1&&isSubtype(t2,ℕt(classical))) return ℕt(classical);
	if(cast(ℂTy)t1||cast(ℂTy)t2) return ℂ(classical);
	if(util.among(t1,Bool(true),ℕt(true),ℤt(true),ℚt(true))&&isSubtype(t2,ℤt(false))) return ℚt(t2.isClassical);
	if(util.among(t1,Bool(false),ℕt(false),ℤt(false),ℚt(false))&&isSubtype(t2,ℤt(false))) return ℚt(false);
	return ℝ(classical); // TODO: good?
}
Expression minusType(Expression t){
	if(preludeNumericTypeName(t) != null)
		return t;
	if(!isNumeric(t)) return null;
	if(cast(BoolTy)t||cast(ℕTy)t) return ℤt(t.isClassical());
	return t;
}
Expression bitNotType(Expression t){
	if(preludeNumericTypeName(t) != null)
		return t;
	if(!isNumeric(t)) return null;
	if(cast(ℕTy)t) return ℤt(t.isClassical());
	return t;
}
Expression notType(Expression t){
	if(!cast(BoolTy)t) return null;
	return t;
}
Expression logicType(Expression t1,Expression t2){
	if(!cast(BoolTy)t1||!cast(BoolTy)t2) return null;
	return Bool(t1.isClassical()&&t2.isClassical());
}
Expression cmpType(Expression t1,Expression t2){
	if(preludeNumericTypeName(t1) != null||preludeNumericTypeName(t2) != null){
		if(!(joinTypes(t1,t2)||isNumeric(t1)||isNumeric(t2)))
			return null;
	}else{
		auto a1=cast(ArrayTy)t1,a2=cast(ArrayTy)t2;
		auto v1=cast(VectorTy)t1,v2=cast(VectorTy)t2;
		Expression n1=a1?a1.next:v1?v1.next:null,n2=a2?a2.next:v2?v2.next:null;
		if(n1&&n2) return cmpType(n1,n2);
		if(auto tpl1=t1.isTupleTy()){
			if(auto tpl2=t2.isTupleTy()){
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
	e.type=determineType(e1.type);
	if(!e.type){
		context.sc.error(format("incompatible type %s for %s",e1.type,name),e.loc);
		e.sstate=SemState.error;
	}
	return e;
}

Expression expressionSemanticImpl(UMinusExp ume,ExpSemContext context){
	return handleUnary!minusType("minus",ume,ume.e,context);
}
Expression expressionSemanticImpl(UNotExp une,ExpSemContext context){
	auto sc=context.sc;
	une.e=expressionSemantic(une.e,context.nestConst);
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
		/+if(auto le=cast(LiteralExp)e2){
			if(le.lit.type==Tok!"0"){
				if(!le.lit.str.canFind(".")){
					auto n=ℤ(le.lit.str);
					if(0<=n&&n<long.max)
						return tupleTy(e1.repeat(cast(size_t)n.toLong()).array);
				}
			}
		}
		sc.error("expected non-negative integer constant",e2.loc);
		e.sstate=SemState.error;+/
		if(!isSubtype(e2.type,ℕt(true))){
			sc.error(format("vector length should be of type !ℕ, not %s",e2.type), e2.loc);
			e.sstate=SemState.error;
		}else return vectorTy(e1,e2);
	}else{
		e.type = determineType(e1.type,e2.type);
		if(!e.type){
			sc.error(format("incompatible types %s and %s for %s",e1.type,e2.type,name),e.loc);
			e.sstate=SemState.error;
		}
	}
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
	return handleBinary!(arithmeticType!true)("bitwise or",boe,boe.e1,boe.e2,context);
}
Expression expressionSemanticImpl(BitXorExp bxe,ExpSemContext context){
	return handleBinary!(arithmeticType!true)("bitwise xor",bxe,bxe.e1,bxe.e2,context);
}
Expression expressionSemanticImpl(BitAndExp bae,ExpSemContext context){
	return handleBinary!(arithmeticType!true)("bitwise and",bae,bae.e1,bae.e2,context);
}

Expression expressionSemanticImpl(AndExp ae,ExpSemContext context){
	return handleBinary!logicType("conjunction",ae,ae.e1,ae.e2,context);
}
Expression expressionSemanticImpl(OrExp oe,ExpSemContext context){
	return handleBinary!logicType("disjunction",oe,oe.e1,oe.e2,context);
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

Expression expressionSemanticImpl(CatExp ce,ExpSemContext context){
	auto sc=context.sc;
	ce.e1=expressionSemantic(ce.e1,context);
	ce.e2=expressionSemantic(ce.e2,context);
	propErr(ce.e1,ce);
	propErr(ce.e2,ce);
	if(ce.sstate==SemState.error)
		return ce;
	auto vt1=cast(VectorTy)ce.e1.type,vt2=cast(VectorTy)ce.e2.type;
	// TODO: concatenation of tuples
	assert(!ce.type);
	if(vt1&&vt2){
		if(auto netype=joinTypes(vt1.next,vt2.next)){
			auto add=new AddExp(vt1.num,vt2.num);
			add.type=ℕt(true);
			add.sstate=SemState.completed;
			auto ntype=vectorTy(netype,add.eval()); // TODO: evaluation context
			ce.type=ntype;
		}
	}else if(ce.e1.type==unit||ce.e2.type==unit){
		auto ntype=ce.e1.type==unit?ce.e2.type:ce.e1.type;
		if(cast(ArrayTy)ntype||cast(VectorTy)ntype||cast(TupleTy)ntype)
			ce.type=ntype;
	}else{
		auto ntype=joinTypes(ce.e1.type,ce.e2.type);
		if(cast(ArrayTy)ntype)
			ce.type=ntype;
	}
	if(!ce.type){
		sc.error(format("incompatible types %s and %s for ~",ce.e1.type,ce.e2.type),ce.loc);
		ce.sstate=SemState.error;
	}
	return ce;
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
			static if(language==silq) if(auto ce=cast(UnaryExp!(Tok!"const"))e){
				return q([true],typeSemantic(ce.e,sc));
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
	auto names=fa.params.map!(p=>p.getName).array;
	auto types=fa.params.map!(p=>p.vtype).array;
	assert(fa.isTuple||types.length==1);
	auto dom=fa.isTuple?tupleTy(types):types[0];
	return productTy(const_,names,dom,cod,fa.isSquare,fa.isTuple,fa.annotation,false);
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
	if(expr.sstate==SemState.started){
		sc.error("cyclic dependency",expr.loc);
		expr.sstate=SemState.error;
		FunctionDef fd=null;
		if(auto le=cast(LambdaExp)expr) fd=le.fd;
		else if(auto id=cast(Identifier)expr) fd=cast(FunctionDef)id.meaning;
		if(fd&&!fd.rret)
			sc.note("possibly caused by missing return type annotation for recursive function",fd.loc);
		return expr;
	}
	assert(expr.sstate==SemState.initial);
	expr.sstate=SemState.started;
	Scope.ConstBlockContext constSave;
	if(!context.constResult) constSave=sc.saveConst();
	scope(success){
		static if(language==silq){
			if(!context.constResult) sc.resetConst(constSave);
			expr.constLookup=context.constResult;
			if(expr&&expr.sstate!=SemState.error){
				if(context.constResult&&!expr.isLifted(sc)&&!expr.type.isClassical()){
					sc.error("non-'lifted' quantum expression must be consumed",expr.loc);
					expr.sstate=SemState.error;
				}else{
					bool consumesIdentifier(){
						auto id=cast(Identifier)expr;
						if(!id||!id.meaning) return false;
						return id.meaning.isLinear();
					}
					if(!context.constResult&&context.inType&&consumesIdentifier){
						sc.error("cannot consume variables within types",expr.loc);
						expr.sstate=SemState.error;
					}else{
						assert(!!expr.type);
						expr.sstate=SemState.completed;
					}
				}
			}
			if(unrealizable(expr.type)){
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


bool setFtype(FunctionDef fd){
	if(fd.ftype) return true;
	if(!fd.ret) return false;
	bool[] pc;
	string[] pn;
	Expression[] pty;
	foreach(p;fd.params){
		if(!p.vtype){
			assert(fd.sstate==SemState.error);
			return false;
		}
		pc~=p.isConst;
		pn~=p.getName;
		pty~=p.vtype;
	}
	assert(fd.isTuple||pty.length==1);
	auto pt=fd.isTuple?tupleTy(pty):pty[0];
	fd.ftype=productTy(pc,pn,pt,fd.ret,fd.isSquare,fd.isTuple,fd.annotation,!fd.context||fd.context.vtype==contextTy(true));
	assert(fd.retNames==[]);
	if(!fd.retNames) fd.retNames = new string[](fd.numReturns);
	assert(fd.fscope_||fd.sstate==SemState.error);
	foreach(callback;fd.ftypeCallbacks)
		callback(fd.ftype);
	fd.ftypeCallbacks=[];
	return true;
}

FunctionDef functionDefSemantic(FunctionDef fd,Scope sc){
	if(fd.sstate==SemState.completed) return fd;
	if(!fd.fscope_) fd=cast(FunctionDef)presemantic(fd,sc); // TODO: why does checking for fd.scope_ not work? (test3.slq)
	auto fsc=fd.fscope_;
	++fd.semanticDepth;
	assert(!!fsc,text(fd));
	assert(fsc.allowsLinear());
	auto bdy=fd.body_?compoundExpSemantic(fd.body_,fsc):null;
	scope(exit){
		static if(language==silq) fsc.pushConsumed();
		if(fd.sstate==SemState.completed){
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
			if(--fd.semanticDepth==0&&(fsc.merge(false,bdy.blscope_)||fsc.close())) fd.sstate=SemState.error;
		}else{
			fsc.forceClose();
		}
	}
	fd.body_=bdy;
	fd.type=unit;
	if(bdy){
		propErr(bdy,fd);
		if(!definitelyReturns(bdy)){
			if(!fd.ret || fd.ret == unit){
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
	if(!fd.ret) fd.ret=unit; // TODO: add bottom type
	setFtype(fd);
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

void determineType(ref Expression e,ExpSemContext context,void delegate(Expression) future){
	if(e.type) return future(e.type);
	if(auto le=cast(LambdaExp)e){
		assert(!!le.fd);
		if(!le.fd.scope_){
			le.fd.scope_=context.sc;
			le.fd=cast(FunctionDef)presemantic(le.fd,context.sc);
			assert(!!le.fd);
		}
		if(auto ty=le.fd.ftype)
			return future(ty);
		le.fd.ftypeCallbacks~=future;
		return;
	}
	e=expressionSemantic(e,context);
	return future(e.type);
}

ReturnExp returnExpSemantic(ReturnExp ret,Scope sc){
	if(ret.sstate==SemState.completed) return ret;
	ret.scope_=sc;
	auto fd=sc.getFunction();
	if(!fd){
		sc.error("return statement must be within function",ret.loc);
		ret.sstate=SemState.error;
		return ret;
	}
	auto context=expSemContext(sc,ConstResult.no,InType.no);
	if(!fd.rret && !fd.ret){
		determineType(ret.e,context,(ty){
			fd.ret=ty;
			setFtype(fd);
		});
	}
	ret.e=expressionSemantic(ret.e,context);
	propErr(ret.e,ret);
	if(cast(CommaExp)ret.e){
		sc.error("use parentheses for multiple return values",ret.e.loc);
		ret.sstate=SemState.error;
	}
	static if(language==silq){
		auto bottom=Dependency(false,SetX!string.init); // variable is a workaround for DMD regression
		if(ret.e.type&&ret.e.type.isClassical()&&sc.controlDependency!=bottom){
			sc.error("cannot return quantum-controlled classical value",ret.e.loc); // TODO: automatically promote to quantum?
			ret.sstate=SemState.error;
		}
	}
	if(ret.sstate==SemState.error)
		return ret;
	static if(language==silq) sc.pushConsumed();
	if(sc.close()){
		sc.note("at function return",ret.loc);
		ret.sstate=SemState.error;
		return ret;
	}
	if(fd.ret){
		if(!isSubtype(ret.e.type,fd.ret)){
			sc.error(format("%s is incompatible with return type %s",ret.e.type,fd.ret),ret.e.loc);
			ret.sstate=SemState.error;
			return ret;
		}
	}else{
		ret.sstate=SemState.error;
		return ret;
	}
	ret.type=unit;
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
	if(isType(expr)||(allowQNumeric&&isQNumeric(expr))) return expr;
	if(auto lit=cast(LiteralExp)expr){
		lit.type=utypeTy;
		if(lit.lit.type==Tok!"0"){
			if(lit.lit.str=="1")
				return unit;
		}
	}
	auto at=cast(IndexExp)expr;
	if(at){
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
		auto id=cast(Identifier)expr;
		if(id&&id.meaning){
			auto decl=id.meaning;
			sc.error(format("%s %s is not a type",decl.kind,decl.name),id.loc);
			sc.note("declared here",decl.loc);
		}else{
			sc.error("not a type",expr.loc);
		}
		expr.sstate=SemState.error;
		return null;
	}else return e;
}

Expression typeForDecl(Declaration decl){
	if(auto dat=cast(DatDecl)decl){
		if(!dat.dtype&&dat.scope_) dat=cast(DatDecl)presemantic(dat,dat.scope_);
		assert(cast(AggregateTy)dat.dtype);
		static if(language==silq){
			assert(dat.isQuantum);
			auto ttype=qtypeTy;
		}else auto ttype=typeTy;
		if(!dat.hasParams) return ttype;
		foreach(p;dat.params) if(!p.vtype) return unit; // TODO: ok?
		assert(dat.isTuple||dat.params.length==1);
		auto pt=dat.isTuple?tupleTy(dat.params.map!(p=>p.vtype).array):dat.params[0].vtype;
		return productTy(dat.params.map!(p=>p.isConst).array,dat.params.map!(p=>p.getName).array,pt,ttype,true,dat.isTuple,deterministic,true);
	}
	if(auto vd=cast(VarDecl)decl){
		return vd.vtype;
	}
	if(auto fd=cast(FunctionDef)decl){
		if(!fd.ftype&&fd.scope_) fd=functionDefSemantic(fd,fd.scope_);
		assert(!!fd);
		return fd.ftype;
	}
	return unit; // TODO
}

bool definitelyReturns(Expression e){
	if(auto ret=cast(ReturnExp)e)
		return true;
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

Expression handleQuantumPrimitive(CallExp ce, ExpSemContext context){
	Scope sc=context.sc;
	ce.arg=expressionSemantic(ce.arg,context.nestConst);
	Expression[] args;
	if(auto tpl=cast(TupleExp)ce.arg) args=tpl.e;
	else {
		sc.error("expected literal arguments to quantumPrimitive",ce.loc);
		ce.sstate=SemState.error;
		return ce;
	}
	if(args.length!=2){
		sc.error("expected two arguments to quantumPrimitive",ce.loc);
		ce.sstate=SemState.error;
		return ce;
	}
	auto literal=cast(LiteralExp)args[0];
	if(!literal||literal.lit.type!=Tok!"``"){
		sc.error("first argument to quantumPrimitive must be string literal",args[0].loc);
		ce.sstate=SemState.error;
		return ce;
	}
	if(!isType(args[1])){
		sc.error("second argument to quantumPrimitive must be a type",args[0].loc);
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
		default:
			sc.error(format("unknown query '%s'",literal.lit.str),literal.loc);
			ce.sstate=SemState.error;
			break;
	}
	return ce;
}

}
