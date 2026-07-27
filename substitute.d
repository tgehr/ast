module ast.substitute;

import ast.expression, ast.type, ast.declaration, ast.scope_, ast.lastuse;
import astopt;
import std.meta: AliasSeq;

private template isOneOf(T,List...){
	enum isOneOf=List.length!=0&&(is(T==List[0])||isOneOf!(T,List[1..$]));
}

private alias genericLhsTypes=AliasSeq!(
	IteExp,AssertExp,LiteralExp,LambdaExp,PlaceholderExp,ForgetExp,SliceExp,VectorExp,
	UPlusExp,UMinusExp,UNotExp,UBitNotExp,
	AddExp,SubExp,NSubExp,MulExp,DivExp,IDivExp,ModExp,PowExp,
	BitOrExp,BitXorExp,BitAndExp,AndThenExp,OrElseExp,
	OrExp,XorExp,AndExp,LtExp,LeExp,GtExp,GeExp,EqExp,NeqExp,
	VectorForExp,ClassicalTy,ProductTy,ArrayTy,TupleTy,VectorTy,
	VariadicTy,TypeTy,QNumericTy,BottomTy,NumericTy,StringTy
);

Expression transitionToType(Expression e,Scope target){
	assert(e.isSemCompleted());
	CompoundExp[] regions;
	void collect(Expression x){
		if(auto ce=cast(CompoundExp)x)
			if(ce.blscope_) regions~=ce;
		if(cast(FunctionDef)x||cast(LambdaExp)x||cast(VectorForExp)x) return;
		if(auto le=cast(LetExp)x)
			if(le.s.blscope_) regions~=le.s;
		foreach(c;x.components) collect(c);
	}
	collect(e);
	if(!regions.length) return e;
	TypeTransition tt;
	tt.target=target;
	foreach(ce;regions) tt.codScopes[ce.blscope_]=[];
	e.freeVarsImpl((id){ tt.taken[id.id]=[]; return 0; });
	foreach(ce;regions) foreach(stmt;ce.s) collectBoundNamesImpl(stmt,tt.taken);
	for(auto sc=target;sc;sc=sc.parentScope())
		foreach(id,_;sc.rnsymtab) tt.taken[id]=[];
	Expression[Id] subst;
	foreach(ce;regions){
		void attr(Expression stmt){
			if(auto de=cast(DefineExp)stmt){
				defineLhsBoundVarsImpl(de.e1,(id){
					if(id.meaning) tt.declRegion[id.meaning]=ce.blscope_;
					return 0;
				});
				return;
			}
			if(auto fd=cast(FunctionDef)stmt){ tt.declRegion[fd]=ce.blscope_; return; }
			if(auto ce2=cast(CommaExp)stmt){ attr(ce2.e1); attr(ce2.e2); return; }
			if(auto ce2=cast(CompoundExp)stmt){
				if(!ce2.blscope_) foreach(x;ce2.s) attr(x);
				return;
			}
		}
		foreach(stmt;ce.s) attr(stmt);
	}
	auto r=e.substitute(subst,&tt);
	void[0][Declaration] twins;
	foreach(orig,twin;tt.declMap){
		twins[twin]=[];
		Scope rs=null;
		if(orig.scope_ in tt.codScopes) rs=orig.scope_;
		if(auto p=orig in tt.declRegion) rs=*p;
		if(rs){
			auto ts=tt.mapScope(rs);
			twin.scope_=ts;
			ts.symtabInsert(twin);
			if(auto fdt=cast(FunctionDef)twin)
				if(fdt.fscope_){ if(!ts.origin) ts.origin=rs; fdt.fscope_.parent=ts; }
		}
	}
	void[0][Scope] tsSet;
	foreach(_,ts;tt.scopes) tsSet[ts]=[];
	void fixUses(Expression x,Scope cur){
		if(cast(FunctionDef)x||cast(LambdaExp)x) return;
		if(auto le=cast(LetExp)x){
			if(le.s.blscope_ in tsSet) cur=le.s.blscope_;
			fixUses(le.s,cur);
			fixUses(le.e,cur);
			return;
		}
		if(auto ce=cast(CompoundExp)x){
			if(ce.blscope_ in tsSet) cur=ce.blscope_;
			foreach(stmt;ce.s) fixUses(stmt,cur);
			return;
		}
		if(auto id=cast(Identifier)x){
			if(cur&&(id.scope_ in tt.codScopes||id.meaning&&id.meaning in twins))
				id.scope_=cur;
			return;
		}
		foreach(c;x.components) fixUses(c,cur);
	}
	fixUses(r,null);
	return r;
}

Expression ttTransitionLet(LetExp le,Expression[Id] subst,TypeTransition* tt){
	Expression[Id] active;
	foreach(k,v;subst) if(le.freeVarsImpl((id)=>id.id==k?1:0)) active[k]=v;
	Id[Id] forced;
	foreach(stmt;le.s.s)
		statementBoundVarsImpl(stmt,(id){
			forced[id.id]=tt.freshName(id.id);
			return 0;
		});
	auto ctx=BlockSubst(active,forced,&tt.taken,&tt.declMap,false,tt);
	auto ns=substituteBlockCompound(le.s,ctx);
	auto ne=substituteLValue(le.e,ctx);
	auto r=new LetExp(ns,ne);
	r.loc=le.loc;
	if(le.isSemError()) r.sstate=SemState.error;
	else if(le.isSemCompleted()){
		r.type=le.type?le.type.substitute(subst,tt):null;
		if(r.type&&r.type.isSemEvaluated()) r.sstate=SemState.completed;
	}
	return r;
}

Expression ttTransitionIte(IteExp ite,Expression[Id] subst,TypeTransition* tt){
	Expression[Id] active;
	foreach(k,v;subst) if(ite.freeVarsImpl((id)=>id.id==k?1:0)) active[k]=v;
	Id[Id] forced;
	foreach(branch;[ite.then,ite.othw])
		if(branch) foreach(stmt;branch.s)
			statementBoundVarsImpl(stmt,(id){
				forced[id.id]=tt.freshName(id.id);
				return 0;
			});
	auto ctx=BlockSubst(active,forced,&tt.taken,&tt.declMap,false,tt);
	auto ncond=substituteLValue(ite.cond,ctx);
	auto tctx=ctx.nested();
	auto nthen=substituteBlockCompound(ite.then,tctx);
	CompoundExp nothw=null;
	if(ite.othw){
		auto fctx=ctx.nested();
		nothw=substituteBlockCompound(ite.othw,fctx);
	}
	auto r=new IteExp(ncond,nthen,nothw);
	r.loc=ite.loc;
	if(ite.isSemError()) r.sstate=SemState.error;
	else if(ite.isSemCompleted()){
		r.type=ite.type?ite.type.substitute(subst,tt):null;
		if(r.type&&r.type.isSemEvaluated()) r.sstate=SemState.completed;
	}
	return r;
}

int defineLhsBoundVarsImpl(Expression lhs,scope int delegate(Identifier) dg){
	return dispatchExp!(dlBoundVars,dlBoundVarsDefault)(lhs,dg);
}
private int dlBoundVars(Identifier id,scope int delegate(Identifier) dg){
	return dg(id);
}
private int dlBoundVars(TypeAnnotationExp tae,scope int delegate(Identifier) dg){
	return defineLhsBoundVarsImpl(tae.e,dg);
}
private int dlBoundVars(TupleExp tpl,scope int delegate(Identifier) dg){
	foreach(x;tpl.e) if(auto r=defineLhsBoundVarsImpl(x,dg)) return r;
	return 0;
}
private int dlBoundVars(CatExp ce,scope int delegate(Identifier) dg){
	if(auto r=defineLhsBoundVarsImpl(ce.e1,dg)) return r;
	return defineLhsBoundVarsImpl(ce.e2,dg);
}
private int dlBoundVars(CallExp ce,scope int delegate(Identifier) dg){
	auto ft=cast(ProductTy)ce.e.type;
	auto tpl=cast(TupleExp)ce.arg;
	if(ft&&ft.isTuple&&tpl&&ft.nargs==tpl.length){
		foreach(i,x;tpl.e){
			if(ft.isConstForReverse[i]) continue;
			if(auto r=defineLhsBoundVarsImpl(x,dg)) return r;
		}
		return 0;
	}
	if(ft&&!ft.isTuple&&ft.nargs==1&&ft.isConstForReverse[0]) return 0;
	return defineLhsBoundVarsImpl(ce.arg,dg);
}
private int dlBoundVars(IndexExp ie,scope int delegate(Identifier) dg){
	return defineLhsBoundVarsImpl(ie.e,dg);
}
private int dlBoundVars(FieldExp fe,scope int delegate(Identifier) dg){
	return defineLhsBoundVarsImpl(fe.e,dg);
}
private int dlBoundVars(LetExp le,scope int delegate(Identifier) dg){
	return le.freeVarsImpl((id)=>id.constLookup||id.implicitDup?0:dg(id));
}
private int dlBoundVars(T)(T lhs,scope int delegate(Identifier) dg) if(isOneOf!(T,genericLhsTypes)){
	return 0; // no names are bound in these positions
}
private int dlBoundVarsDefault(Expression lhs,scope int delegate(Identifier) dg){
	return 0;
}

int defineLhsFreeVarsImpl(Expression lhs,scope int delegate(Identifier) dg){
	return dispatchExp!(dlFreeVars,dlFreeVarsDefault)(lhs,dg);
}
private int dlFreeVars(Identifier id,scope int delegate(Identifier) dg){
	return 0;
}
private int dlFreeVars(TypeAnnotationExp tae,scope int delegate(Identifier) dg){
	if(auto r=defineLhsFreeVarsImpl(tae.e,dg)) return r;
	if(tae.t) return tae.t.freeVarsImpl(dg);
	return 0;
}
private int dlFreeVars(TupleExp tpl,scope int delegate(Identifier) dg){
	foreach(x;tpl.e) if(auto r=defineLhsFreeVarsImpl(x,dg)) return r;
	return 0;
}
private int dlFreeVars(CatExp ce,scope int delegate(Identifier) dg){
	if(auto r=defineLhsFreeVarsImpl(ce.e1,dg)) return r;
	return defineLhsFreeVarsImpl(ce.e2,dg);
}
private int dlFreeVars(CallExp ce,scope int delegate(Identifier) dg){
	if(auto r=ce.e.freeVarsImpl(dg)) return r;
	auto ft=cast(ProductTy)ce.e.type;
	auto tpl=cast(TupleExp)ce.arg;
	if(ft&&ft.isTuple&&tpl&&ft.nargs==tpl.length){
		foreach(i,x;tpl.e){
			if(ft.isConstForReverse[i]){ if(auto r=x.freeVarsImpl(dg)) return r; }
			else if(auto r=defineLhsFreeVarsImpl(x,dg)) return r;
		}
		return 0;
	}
	if(ft&&!ft.isTuple&&ft.nargs==1&&ft.isConstForReverse[0]) return ce.arg.freeVarsImpl(dg);
	return defineLhsFreeVarsImpl(ce.arg,dg);
}
private int dlFreeVars(IndexExp ie,scope int delegate(Identifier) dg){
	return ie.freeVarsImpl(dg);
}
private int dlFreeVars(FieldExp fe,scope int delegate(Identifier) dg){
	return fe.freeVarsImpl(dg);
}
private int dlFreeVars(LetExp le,scope int delegate(Identifier) dg){
	return le.freeVarsImpl((id)=>id.constLookup||id.implicitDup?dg(id):0);
}
private int dlFreeVars(T)(T lhs,scope int delegate(Identifier) dg) if(isOneOf!(T,genericLhsTypes)){
	return lhs.freeVarsImpl(dg);
}
private int dlFreeVarsDefault(Expression lhs,scope int delegate(Identifier) dg){
	return lhs.freeVarsImpl(dg);
}

int statementBoundVarsImpl(Expression stmt,scope int delegate(Identifier) dg){
	return dispatchStm!(stmtBoundVars,stmtBoundVarsDefault)(stmt,dg);
}
private int stmtBoundVars(FunctionDef fd,scope int delegate(Identifier) dg){
	auto name=fd.rename?fd.rename:fd.name;
	return name?dg(name):0;
}
private int stmtBoundVars(CommaExp ce,scope int delegate(Identifier) dg){
	if(auto r=statementBoundVarsImpl(ce.e1,dg)) return r;
	return statementBoundVarsImpl(ce.e2,dg);
}
private int stmtBoundVars(IteExp ite,scope int delegate(Identifier) dg){
	foreach(x;ite.then.s) if(auto r=statementBoundVarsImpl(x,dg)) return r;
	if(ite.othw) foreach(x;ite.othw.s) if(auto r=statementBoundVarsImpl(x,dg)) return r;
	return 0;
}
private int stmtBoundVars(CompoundExp ce,scope int delegate(Identifier) dg){
	if(!ce.blscope_)
		foreach(x;ce.s) if(auto r=statementBoundVarsImpl(x,dg)) return r;
	return 0;
}
private int stmtBoundVars(T)(T stmt,scope int delegate(Identifier) dg)
	if(is(T==ForExp)||is(T==WhileExp)||is(T==RepeatExp)||is(T==ReturnExp)||is(T==ForgetExp)||is(T==CallExp)||is(T==TypeAnnotationExp)||is(T==AssertExp)||is(T==ObserveExp)||is(T==CObserveExp))
{
	return 0; // these statement kinds bind no names in the enclosing block
}
static if(language==silq)
private int stmtBoundVars(WithExp we,scope int delegate(Identifier) dg){
	return 0; // names bound by a `with` block are local to the construct
}
private int stmtBoundVarsDefault(Expression stmt,scope int delegate(Identifier) dg){
	if(auto de=cast(DefineExp)stmt) return defineLhsBoundVarsImpl(de.e1,dg);
	return 0;
}

int statementFreeVarsImpl(Expression stmt,scope int delegate(Identifier) dg){
	return dispatchStm!(stmtFreeVars,stmtFreeVarsDefault)(stmt,dg);
}
private int stmtFreeVars(FunctionDef fd,scope int delegate(Identifier) dg){
	return functionDefFreeVarsImpl(fd,dg);
}
private int stmtFreeVars(CommaExp ce,scope int delegate(Identifier) dg){
	if(auto r=statementFreeVarsImpl(ce.e1,dg)) return r;
	return statementFreeVarsImpl(ce.e2,dg);
}
private int stmtFreeVars(CompoundExp ce,scope int delegate(Identifier) dg){
	return blockFreeVarsImpl(ce.s,null,dg);
}
private int stmtFreeVars(IteExp ite,scope int delegate(Identifier) dg){
	if(auto r=ite.cond.freeVarsImpl(dg)) return r;
	if(auto r=blockFreeVarsImpl(ite.then.s,null,dg)) return r;
	if(ite.othw) if(auto r=blockFreeVarsImpl(ite.othw.s,null,dg)) return r;
	return 0;
}
private int stmtFreeVars(ForExp fe,scope int delegate(Identifier) dg){
	if(auto rng=fe.aggr.isRange()){
		if(auto r=rng.left.freeVarsImpl(dg)) return r;
		if(rng.step) if(auto r=rng.step.freeVarsImpl(dg)) return r;
		if(auto r=rng.right.freeVarsImpl(dg)) return r;
	}else if(auto cont=fe.aggr.isContainer()){
		if(auto r=cont.e.freeVarsImpl(dg)) return r;
	}
	void[0][Id] bound;
	if(fe.var) bound[fe.var.id]=[];
	if(fe.pattern) defineLhsBoundVarsImpl(fe.pattern,(id){ bound[id.id]=[]; return 0; });
	if(fe.pattern) if(auto r=defineLhsFreeVarsImpl(fe.pattern,dg)) return r;
	return blockFreeVarsImpl(fe.bdy.s,null,(id)=>id.id in bound?0:dg(id));
}
private int stmtFreeVars(WhileExp we,scope int delegate(Identifier) dg){
	if(auto r=we.cond.freeVarsImpl(dg)) return r;
	return blockFreeVarsImpl(we.bdy.s,null,dg);
}
private int stmtFreeVars(RepeatExp re,scope int delegate(Identifier) dg){
	if(auto r=re.num.freeVarsImpl(dg)) return r;
	return blockFreeVarsImpl(re.bdy.s,null,dg);
}
private int stmtFreeVars(ReturnExp re,scope int delegate(Identifier) dg){
	return re.e?re.e.freeVarsImpl(dg):0;
}
private int stmtFreeVars(ForgetExp fe,scope int delegate(Identifier) dg){
	if(auto r=fe.var.freeVarsImpl(dg)) return r;
	return fe.val?fe.val.freeVarsImpl(dg):0;
}
private int stmtFreeVars(T)(T stmt,scope int delegate(Identifier) dg)
	if(is(T==CallExp)||is(T==TypeAnnotationExp)||is(T==AssertExp)||is(T==ObserveExp)||is(T==CObserveExp))
{
	return stmt.freeVarsImpl(dg);
}
static if(language==silq)
private int stmtFreeVars(WithExp we,scope int delegate(Identifier) dg){
	return we.freeVarsImpl(dg);
}
private int stmtFreeVarsDefault(Expression stmt,scope int delegate(Identifier) dg){
	if(auto de=cast(DefineExp)stmt){
		if(auto r=de.e2.freeVarsImpl(dg)) return r;
		return defineLhsFreeVarsImpl(de.e1,dg);
	}
	return stmt.freeVarsImpl(dg);
}

int blockFreeVarsImpl(Expression[] stmts,Expression trailing,scope int delegate(Identifier) dg){
	void[0][Id] bound;
	int filtered(Identifier id){ return id.id in bound?0:dg(id); }
	foreach(stmt;stmts){
		if(auto r=statementFreeVarsImpl(stmt,&filtered)) return r;
		statementBoundVarsImpl(stmt,(id){ bound[id.id]=[]; return 0; });
	}
	if(trailing) return trailing.freeVarsImpl(&filtered);
	return 0;
}

int functionDefFreeVarsImpl(FunctionDef fd,scope int delegate(Identifier) dg){
	void[0][Id] bound;
	if(fd.name){ bound[fd.getId]=[]; bound[fd.name.id]=[]; }
	int filtered(Identifier id){ return id.id in bound?0:dg(id); }
	foreach(p;fd.params){
		if(auto pt=p.vtype?p.vtype:p.dtype) if(auto r=pt.freeVarsImpl(&filtered)) return r;
		if(p.name){ bound[p.getId]=[]; bound[p.name.id]=[]; }
	}
	if(auto ret=fd.ret?fd.ret:fd.rret) if(auto r=ret.freeVarsImpl(&filtered)) return r;
	if(fd.body_) if(auto r=blockFreeVarsImpl(fd.body_.s,null,&filtered)) return r;
	return 0;
}

void collectBoundNamesImpl(Expression stmt,ref void[0][Id] names){
	statementBoundVarsImpl(stmt,(id){ names[id.id]=[]; return 0; });
	dispatchStm!(collectBoundNames,collectBoundNamesDefault)(stmt,names);
}
private void collectBoundNames(FunctionDef fd,ref void[0][Id] names){
	collectFunctionBoundNames(fd,names);
}
private void collectBoundNames(CommaExp ce,ref void[0][Id] names){
	collectBoundNamesImpl(ce.e1,names);
	collectBoundNamesImpl(ce.e2,names);
}
private void collectBoundNames(CompoundExp ce,ref void[0][Id] names){
	foreach(x;ce.s) collectBoundNamesImpl(x,names);
}
private void collectBoundNames(IteExp ite,ref void[0][Id] names){
	foreach(x;ite.then.s) collectBoundNamesImpl(x,names);
	if(ite.othw) foreach(x;ite.othw.s) collectBoundNamesImpl(x,names);
}
private void collectBoundNames(ForExp fe,ref void[0][Id] names){
	if(fe.var) names[fe.var.id]=[];
	if(fe.pattern) defineLhsBoundVarsImpl(fe.pattern,(id){ names[id.id]=[]; return 0; });
	foreach(x;fe.bdy.s) collectBoundNamesImpl(x,names);
}
private void collectBoundNames(WhileExp we,ref void[0][Id] names){
	foreach(x;we.bdy.s) collectBoundNamesImpl(x,names);
}
private void collectBoundNames(RepeatExp re,ref void[0][Id] names){
	foreach(x;re.bdy.s) collectBoundNamesImpl(x,names);
}
private void collectBoundNames(T)(T stmt,ref void[0][Id] names)
	if(is(T==ReturnExp)||is(T==ForgetExp)||is(T==CallExp)||is(T==TypeAnnotationExp)||is(T==AssertExp)||is(T==ObserveExp)||is(T==CObserveExp))
{
}
static if(language==silq)
private void collectBoundNames(WithExp we,ref void[0][Id] names){
}
private void collectBoundNamesDefault(Expression stmt,ref void[0][Id] names){
	if(auto de=cast(DefineExp)stmt){
		if(auto le=cast(LambdaExp)de.e2) collectFunctionBoundNames(le.fd,names);
		return;
	}
	if(auto le=cast(LetExp)stmt) foreach(x;le.s.s) collectBoundNamesImpl(x,names);
}
void collectFunctionBoundNames(FunctionDef fd,ref void[0][Id] names){
	if(!fd) return;
	if(fd.name){ names[fd.getId]=[]; names[fd.name.id]=[]; }
	foreach(p;fd.params) if(p.name){ names[p.getId]=[]; names[p.name.id]=[]; }
	if(fd.body_) foreach(x;fd.body_.s) collectBoundNamesImpl(x,names);
}

struct BlockSubst{
	Expression[Id] subst;
	Id[Id] forced;
	void[0][Id]* taken;
	Declaration[Declaration]* declMap;
	bool changed=false;
	TypeTransition* tt=null;

	bool wouldCapture(Id b){
		foreach(k,v;subst) if(v.hasFreeVar(b)) return true;
		return false;
	}
	Id freshName(Id base){
		auto nn=base?base:Id.intern("x");
		do nn=nn.apos; while(nn in *taken||wouldCapture(nn));
		(*taken)[nn]=[];
		return nn;
	}
	BlockSubst nested(){
		return BlockSubst(subst.dup,forced.dup,taken,declMap,false,tt);
	}
	Identifier bindVar(Identifier id,Expression vtype=null){
		auto b=id.id;
		Id nb=b;
		if(auto f=b in forced) nb=*f;
		else if(wouldCapture(b)) nb=freshName(b);
		if(nb==b){
			if(b in subst) subst.remove(b);
			return id;
		}
		auto nid=remakeIdentifier(id,nb);
		auto use=remakeIdentifier(id,nb);
		use.constLookup=true;
		use.byRef=false;
		use.implicitDup=false;
		if(!use.type) use.type=vtype;
		if(!use.isSemCompleted()&&!use.isSemError()&&use.type&&use.type.isSemEvaluated()) use.sstate=SemState.completed;
		if(auto vd=cast(VarDecl)id.meaning){
			auto dvtype=vd.vtype&&vd.vtype.isSemCompleted()&&subst.length?vd.vtype.substitute(subst,tt):vd.vtype;
			auto twin=getVarDeclTwin(vd,nid,dvtype);
			nid.meaning=twin;
			use.meaning=twin;
			if(!use.scope_) use.scope_=twin.scope_;
			if(declMap) (*declMap)[vd]=twin;
		}
		subst[b]=use;
		changed=true;
		return nid;
	}
}

private VarDecl getVarDeclTwin(VarDecl orig,Identifier nname,Expression nvtype){
	auto twin=new VarDecl(nname);
	twin.copyAnalyzedFieldsFrom(orig);
	twin.vtype=nvtype;
	twin.dtype=orig.dtype;
	twin.scope_=orig.scope_;
	return twin;
}

private Declaration[] remapDecls(Declaration[] decls,Declaration[Declaration]* declMap,ref bool remapped){
	if(!declMap||!(*declMap).length||!decls.length) return decls;
	bool c=false;
	auto r=decls.dup;
	foreach(ref d;r) if(auto p=d in *declMap){ d=*p; c=true; }
	if(!c) return decls;
	remapped=true;
	return r;
}

private Identifier remakeIdentifier(Identifier id,Id nid){
	Expression.CopyArgs cargs={preserveSemantic:true};
	auto r=id.copy(cargs);
	r.id=nid;
	r.loc=id.loc;
	return r;
}

private Expression useSubstitute(Expression e,ref BlockSubst ctx){
	if(!e) return null;
	if(!e.isSemCompleted()) return e;
	if(!ctx.subst.length) return e;
	auto ne=e.substitute(ctx.subst,ctx.tt);
	if(ne !is e) ctx.changed=true;
	return ne;
}

private T finishStatement(T)(T r,Expression orig,ref BlockSubst ctx){
	r.loc=orig.loc;
	ctx.changed=true;
	if(orig.isSemError()){ r.sstate=SemState.error; return r; }
	if(orig.isSemCompleted()){
		if(!r.type) r.type=orig.type&&ctx.subst.length?orig.type.substitute(ctx.subst,ctx.tt):(orig.type?orig.type:unit);
		if(r.type&&r.type.isSemEvaluated()) r.sstate=SemState.completed;
	}
	return r;
}

Expression substituteLValue(Expression lhs,ref BlockSubst ctx){
	if(!lhs) return null;
	return dispatchExp!(substLhs,substLhsDefault)(lhs,ctx);
}
private Expression substLhs(Identifier id,ref BlockSubst ctx){
	if(id.constLookup||id.implicitDup) return useSubstitute(id,ctx);
	if(auto p=id.id in ctx.subst){
		Expression.CopyArgs cargs={preserveSemantic:true};
		auto nv=(*p).copy(cargs);
		nv.setConstLookup(id.constLookup);
		nv.byRef=id.byRef;
		ctx.changed=true;
		return nv;
	}
	return id;
}
private Expression substLhs(TypeAnnotationExp tae,ref BlockSubst ctx){
	auto ne=substituteLValue(tae.e,ctx);
	auto nt=useSubstitute(tae.t,ctx);
	if(ne is tae.e&&nt is tae.t) return tae;
	auto r=new TypeAnnotationExp(ne,nt,tae.annotationType);
	return finishStatement(r,tae,ctx);
}
private Expression substLhs(TupleExp tpl,ref BlockSubst ctx){
	auto ne=tpl.e.dup;
	bool chg=false;
	foreach(ref x;ne){
		auto nx=substituteLValue(x,ctx);
		if(nx !is x) chg=true;
		x=nx;
	}
	if(!chg) return tpl;
	auto r=new TupleExp(ne);
	return finishStatement(r,tpl,ctx);
}
private Expression substLhs(IndexExp ie,ref BlockSubst ctx){
	auto nagg=substituteLValue(ie.e,ctx);
	auto na=useSubstitute(ie.a,ctx);
	if(nagg is ie.e&&na is ie.a) return ie;
	auto r=new IndexExp(nagg,na);
	r.isArraySyntax=ie.isArraySyntax;
	static if(language==silq) r.isClassical_=ie.isClassical_;
	return finishStatement(r,ie,ctx);
}
private Expression substLhs(FieldExp fe,ref BlockSubst ctx){
	auto nagg=substituteLValue(fe.e,ctx);
	if(nagg is fe.e) return fe;
	auto r=new FieldExp(nagg,fe.f);
	return finishStatement(r,fe,ctx);
}
private Expression substLhs(CatExp ce,ref BlockSubst ctx){
	auto ne1=substituteLValue(ce.e1,ctx);
	auto ne2=substituteLValue(ce.e2,ctx);
	if(ne1 is ce.e1&&ne2 is ce.e2) return ce;
	auto r=new CatExp(ne1,ne2);
	return finishStatement(r,ce,ctx);
}
private Expression substLhs(CallExp ce,ref BlockSubst ctx){
	auto ne=useSubstitute(ce.e,ctx);
	auto narg=substituteLValue(ce.arg,ctx);
	if(ne is ce.e&&narg is ce.arg) return ce;
	auto r=new CallExp(ne,narg,ce.isSquare,ce.isClassical_);
	return finishStatement(r,ce,ctx);
}
private Expression substLhs(LetExp le,ref BlockSubst ctx){
	auto nctx=ctx.nested();
	foreach(stmt;le.s.s) collectBoundNamesImpl(stmt,*nctx.taken);
	auto ns=substituteBlockCompound(le.s,nctx);
	auto ne=substituteLValue(le.e,nctx);
	if(nctx.changed) ctx.changed=true;
	if(ns is le.s&&ne is le.e) return le;
	auto r=new LetExp(ns,ne);
	return finishStatement(r,le,ctx);
}
private Expression substLhs(T)(T e,ref BlockSubst ctx) if(isOneOf!(T,genericLhsTypes)){
	return useSubstitute(e,ctx);
}
private Expression substLhsDefault(Expression e,ref BlockSubst ctx){
	return useSubstitute(e,ctx);
}

private Expression substituteDefineLhs(Expression lhs,ref BlockSubst ctx){
	if(!lhs) return null;
	return dispatchExp!(substDefineLhs,substDefineLhsDefault)(lhs,ctx);
}
private Expression substDefineLhs(Identifier id,ref BlockSubst ctx){
	auto nid=ctx.bindVar(id,id.type);
	return nid;
}
private Expression substDefineLhs(TypeAnnotationExp tae,ref BlockSubst ctx){
	auto nt=useSubstitute(tae.t,ctx);
	auto ne=substituteDefineLhs(tae.e,ctx);
	if(ne is tae.e&&nt is tae.t) return tae;
	auto r=new TypeAnnotationExp(ne,nt,tae.annotationType);
	return finishStatement(r,tae,ctx);
}
private Expression substDefineLhs(TupleExp tpl,ref BlockSubst ctx){
	auto ne=tpl.e.dup;
	bool chg=false;
	foreach(ref x;ne){
		auto nx=substituteDefineLhs(x,ctx);
		if(nx !is x) chg=true;
		x=nx;
	}
	if(!chg) return tpl;
	auto r=new TupleExp(ne);
	return finishStatement(r,tpl,ctx);
}
private Expression substDefineLhs(CatExp ce,ref BlockSubst ctx){
	auto ne1=substituteDefineLhs(ce.e1,ctx);
	auto ne2=substituteDefineLhs(ce.e2,ctx);
	if(ne1 is ce.e1&&ne2 is ce.e2) return ce;
	auto r=new CatExp(ne1,ne2);
	return finishStatement(r,ce,ctx);
}
private Expression substDefineLhs(CallExp ce,ref BlockSubst ctx){
	auto ne=useSubstitute(ce.e,ctx);
	auto ft=cast(ProductTy)ce.e.type;
	auto tpl=cast(TupleExp)ce.arg;
	Expression narg;
	if(ft&&ft.isTuple&&tpl&&ft.nargs==tpl.length){
		auto nes=tpl.e.dup;
		bool chg=false;
		foreach(i,ref x;nes){
			auto nx=ft.isConstForReverse[i]?substituteLValue(x,ctx):substituteDefineLhs(x,ctx);
			if(nx !is x) chg=true;
			x=nx;
		}
		if(!chg) narg=ce.arg;
		else{
			auto ntpl=new TupleExp(nes);
			narg=finishStatement(ntpl,ce.arg,ctx);
		}
	}else if(ft&&!ft.isTuple&&ft.nargs==1&&ft.isConstForReverse[0]) narg=substituteLValue(ce.arg,ctx);
	else narg=substituteDefineLhs(ce.arg,ctx);
	if(ne is ce.e&&narg is ce.arg) return ce;
	auto r=new CallExp(ne,narg,ce.isSquare,ce.isClassical_);
	return finishStatement(r,ce,ctx);
}
private Expression substDefineLhs(IndexExp ie,ref BlockSubst ctx){
	auto nagg=substituteLValue(ie.e,ctx);
	auto na=useSubstitute(ie.a,ctx);
	defineLhsBoundVarsImpl(ie.e,(id){ ctx.subst.remove(id.id); return 0; });
	if(nagg is ie.e&&na is ie.a) return ie;
	auto r=new IndexExp(nagg,na);
	r.isArraySyntax=ie.isArraySyntax;
	static if(language==silq) r.isClassical_=ie.isClassical_;
	return finishStatement(r,ie,ctx);
}
private Expression substDefineLhs(FieldExp fe,ref BlockSubst ctx){
	auto nagg=substituteLValue(fe.e,ctx);
	defineLhsBoundVarsImpl(fe.e,(id){ ctx.subst.remove(id.id); return 0; });
	if(nagg is fe.e) return fe;
	auto r=new FieldExp(nagg,fe.f);
	return finishStatement(r,fe,ctx);
}
private Expression substDefineLhs(LetExp le,ref BlockSubst ctx){
	defineLhsBoundVarsImpl(le,(id){ ctx.subst.remove(id.id); return 0; });
	return substituteLValue(le,ctx);
}
private Expression substDefineLhs(T)(T e,ref BlockSubst ctx) if(isOneOf!(T,genericLhsTypes)){
	return substituteLValue(e,ctx);
}
private Expression substDefineLhsDefault(Expression e,ref BlockSubst ctx){
	return substituteLValue(e,ctx);
}

private Expression substituteStatement(Expression stmt,ref BlockSubst ctx){
	return dispatchStm!(substStm,substStmDefault)(stmt,ctx);
}

// the default handles the statement kinds that dispatchStm does not route
private Expression substDefine(DefineExp de,ref BlockSubst ctx){
	auto ne2=substituteLValue(de.e2,ctx);
	auto ne1=substituteDefineLhs(de.e1,ctx);
	if(ne1 is de.e1&&ne2 is de.e2) return de;
	auto r=new DefineExp(ne1,ne2);
	return finishStatement(r,de,ctx);
}
private Expression substAssign(AAssignExp ae,ref BlockSubst ctx){
	auto ne1=substituteLValue(ae.e1,ctx);
	auto ne2=useSubstitute(ae.e2,ctx);
	if(ne1 is ae.e1&&ne2 is ae.e2) return ae;
	auto r=cast(AAssignExp)(cast(Expression)ae).copy();
	assert(!!r);
	r.e1=ne1;
	r.e2=ne2;
	r.type=null;
	r.sstate=SemState.initial;
	return finishStatement(r,ae,ctx);
}
private Expression substStmDefault(Expression stmt,ref BlockSubst ctx){
	if(auto de=cast(DefineExp)stmt) return substDefine(de,ctx);
	if(auto ae=cast(AAssignExp)stmt) return substAssign(ae,ctx);
	// expression-statements are substituted as lvalues
	return substituteLValue(stmt,ctx);
}

private Expression substStm(FunctionDef fd,ref BlockSubst ctx){
	auto nfd=substituteFunctionDefImpl(fd,ctx,true);
	if(nfd !is fd){
		if(ctx.declMap) (*ctx.declMap)[fd]=nfd;
		auto fname=fd.rename?fd.rename:fd.name;
		if(fname) if(auto p=fname.id in ctx.subst)
			if(auto uid=cast(Identifier)(*p)){
				if(uid.meaning is fd||uid.meaning is null) uid.meaning=nfd;
				if(uid.meaning is nfd&&nfd.ftype&&nfd.ftype.isSemEvaluated()) uid.type=nfd.ftype;
			}
	}
	return nfd;
}
private Expression substStm(CommaExp ce,ref BlockSubst ctx){
	auto ne1=substituteStatement(ce.e1,ctx);
	auto ne2=substituteStatement(ce.e2,ctx);
	if(ne1 is ce.e1&&ne2 is ce.e2) return ce;
	auto r=new CommaExp(ne1,ne2);
	return finishStatement(r,ce,ctx);
}
private Expression substStm(IteExp ite,ref BlockSubst ctx){
	auto ncond=useSubstitute(ite.cond,ctx);
	int decide(Identifier id){
		auto b=id.id;
		if(b in ctx.forced) return 0;
		if(ctx.wouldCapture(b)) ctx.forced[b]=ctx.freshName(b);
		return 0;
	}
	foreach(x;ite.then.s) statementBoundVarsImpl(x,&decide);
	if(ite.othw) foreach(x;ite.othw.s) statementBoundVarsImpl(x,&decide);
	auto tctx=ctx.nested();
	auto nthen=substituteBlockCompound(ite.then,tctx);
	auto octx=ctx.nested();
	CompoundExp nothw=null;
	if(ite.othw) nothw=substituteBlockCompound(ite.othw,octx);
	void applyEscaping(Expression[] ss,ref BlockSubst src){
		foreach(x;ss) statementBoundVarsImpl(x,(id){
			auto b=id.id;
			if(b in ctx.forced){
				if(auto v=b in src.subst) ctx.subst[b]=*v;
				else ctx.subst.remove(b);
			}else ctx.subst.remove(b);
			return 0;
		});
	}
	applyEscaping(ite.then.s,tctx);
	if(ite.othw) applyEscaping(ite.othw.s,octx);
	if(tctx.changed||octx.changed) ctx.changed=true;
	if(ncond is ite.cond&&nthen is ite.then&&nothw is ite.othw) return ite;
	auto r=new IteExp(ncond,nthen,nothw);
	return finishStatement(r,ite,ctx);
}
private Expression substStm(CompoundExp ce,ref BlockSubst ctx){
	if(!ce.blscope_) return substituteBlockCompound(ce,ctx);
	auto nctx=ctx.nested();
	auto r=substituteBlockCompound(ce,nctx);
	if(nctx.changed) ctx.changed=true;
	return r;
}
private Expression substStm(ForExp fe,ref BlockSubst ctx){
	ForAggregate naggr=fe.aggr;
	bool aggrChanged=false;
	if(auto rng=fe.aggr.isRange()){
		auto nleft=useSubstitute(rng.left,ctx);
		auto nstep=rng.step?useSubstitute(rng.step,ctx):null;
		auto nright=useSubstitute(rng.right,ctx);
		if(nleft !is rng.left||nstep !is rng.step||nright !is rng.right){
			naggr=ForAggregate(ForRange(rng.leftExclusive,nleft,nstep,rng.rightExclusive,nright));
			aggrChanged=true;
		}
	}else if(auto cont=fe.aggr.isContainer()){
		auto nce=useSubstitute(cont.e,ctx);
		if(nce !is cont.e){
			naggr=ForAggregate(ForContainer(nce));
			aggrChanged=true;
		}
	}
	auto bctx=ctx.nested();
	Identifier nvar=fe.var;
	if(fe.var) nvar=bctx.bindVar(fe.var,fe.var.type);
	Expression npattern=fe.pattern?substituteDefineLhs(fe.pattern,bctx):null;
	auto nbdy=substituteBlockCompound(fe.bdy,bctx);
	if(bctx.changed) ctx.changed=true;
	if(!aggrChanged&&nvar is fe.var&&npattern is fe.pattern&&nbdy is fe.bdy) return fe;
	auto r=new ForExp(nvar,npattern,naggr,nbdy);
	r.fescope_=fe.fescope_;
	r.loopVar=fe.loopVar;
	if(fe.loopVar&&bctx.declMap)
		if(auto p=cast(Declaration)fe.loopVar in *bctx.declMap)
			if(auto nvd=cast(VarDecl)*p) r.loopVar=nvd;
	return finishStatement(r,fe,ctx);
}
private Expression substStm(WhileExp we,ref BlockSubst ctx){
	auto ncond=useSubstitute(we.cond,ctx);
	auto bctx=ctx.nested();
	auto nbdy=substituteBlockCompound(we.bdy,bctx);
	if(bctx.changed) ctx.changed=true;
	if(ncond is we.cond&&nbdy is we.bdy) return we;
	auto r=new WhileExp(ncond,nbdy);
	return finishStatement(r,we,ctx);
}
private Expression substStm(RepeatExp re,ref BlockSubst ctx){
	auto nnum=useSubstitute(re.num,ctx);
	auto bctx=ctx.nested();
	auto nbdy=substituteBlockCompound(re.bdy,bctx);
	if(bctx.changed) ctx.changed=true;
	if(nnum is re.num&&nbdy is re.bdy) return re;
	auto r=new RepeatExp(nnum,nbdy);
	return finishStatement(r,re,ctx);
}
private Expression substStm(ReturnExp re,ref BlockSubst ctx){
	auto ne=re.e?substituteLValue(re.e,ctx):null;
	bool remapped=false;
	auto nfv=remapDecls(re.forgottenVars,ctx.declMap,remapped);
	if(ne is re.e&&!remapped) return re;
	auto r=new ReturnExp(ne);
	r.expected=re.expected;
	r.forgottenVars=nfv;
	return finishStatement(r,re,ctx);
}
private Expression substStm(ForgetExp fe,ref BlockSubst ctx){
	auto nvar=substituteLValue(fe.var,ctx);
	auto nval=fe.val?useSubstitute(fe.val,ctx):null;
	if(nvar is fe.var&&nval is fe.val) return fe;
	auto r=new ForgetExp(nvar,nval);
	return finishStatement(r,fe,ctx);
}
// expression-statements are substituted as lvalues
private Expression substStm(T)(T stmt,ref BlockSubst ctx)
	if(is(T==CallExp)||is(T==TypeAnnotationExp)||is(T==AssertExp)||is(T==ObserveExp)||is(T==CObserveExp))
{
	return substituteLValue(stmt,ctx);
}
static if(language==silq)
private Expression substStm(WithExp we,ref BlockSubst ctx){
	return substituteLValue(we,ctx);
}

CompoundExp substituteBlockCompound(CompoundExp ce,ref BlockSubst ctx){
	auto entrySubst=ctx.subst.dup;
	auto ns=ce.s.dup;
	bool changed=ctx.tt&&ce.blscope_&&ce.blscope_ in ctx.tt.codScopes;
	foreach(ref x;ns){
		auto nx=substituteStatement(x,ctx);
		if(nx !is x) changed=true;
		x=nx;
	}
	if(!changed) return ce;
	auto r=new CompoundExp(ns);
	r.loc=ce.loc;
	r.blscope_=ce.blscope_;
	if(ctx.tt&&ce.blscope_&&ce.blscope_ in ctx.tt.codScopes){
		Declaration[] filter(Declaration[] ds){
			Declaration[] r;
			foreach(d;ds){ if(!d.splitFrom&&d in ctx.tt.declRegion) r~=d; }
			return r;
		}
		Declaration[] boundVars(){
			Declaration[] r;
			void walk(Expression stmt){
				if(auto de=cast(DefineExp)stmt){
					defineLhsBoundVarsImpl(de.e1,(id){
						if(id.meaning&&!id.meaning.splitFrom) r~=id.meaning;
						return 0;
					});
					return;
				}
				if(auto fd=cast(FunctionDef)stmt){ if(!fd.splitFrom) r~=fd; return; }
				if(auto ce2=cast(CommaExp)stmt){ walk(ce2.e1); walk(ce2.e2); return; }
				if(auto ce2=cast(CompoundExp)stmt){
					if(!ce2.blscope_) foreach(x;ce2.s) walk(x);
					return;
				}
			}
			foreach(stmt;ce.s) walk(stmt);
			return r;
		}
		bool remapped=false;
		auto ts=ctx.tt.mapScope(ce.blscope_);
		auto fv=filter(ce.blscope_.forgottenVars);
		if(!fv.length) fv=boundVars();
		ts.forgottenVars=remapDecls(fv,ctx.declMap,remapped);
		ts.forgottenVarsOnEntry=remapDecls(filter(ce.blscope_.forgottenVarsOnEntry),ctx.declMap,remapped);
		r.blscope_=ts;
	}else if(ce.blscope_&&ctx.declMap&&(*ctx.declMap).length){
		bool remapped=false;
		auto nfv=remapDecls(ce.blscope_.forgottenVars,ctx.declMap,remapped);
		auto nfve=remapDecls(ce.blscope_.forgottenVarsOnEntry,ctx.declMap,remapped);
		auto nmv=remapDecls(ce.blscope_.mergedVars,ctx.declMap,remapped);
		if(remapped){
			if(auto ts=cast(TypeScope)ce.blscope_){
				ts.forgottenVars=nfv;
				ts.forgottenVarsOnEntry=nfve;
				ts.mergedVars=nmv;
			}else{
				auto nsc=new BlockScope(null,ce.blscope_.restriction_);
				nsc.parent=ce.blscope_.parent;
				nsc.forgottenVars=nfv;
				nsc.forgottenVarsOnEntry=nfve;
				nsc.mergedVars=nmv;
				r.blscope_=nsc;
			}
		}
	}
	ctx.changed=true;
	if(ce.isSemError()) r.sstate=SemState.error;
	else if(ce.isSemCompleted()){
		r.type=ce.type&&entrySubst.length?ce.type.substitute(entrySubst,ctx.tt):(ce.type?ce.type:unit);
		if(r.type&&r.type.isSemEvaluated()) r.sstate=SemState.completed;
	}
	return r;
}

FunctionDef substituteFunctionDefImpl(FunctionDef fd,ref BlockSubst ctx,bool bindNameInEnclosing){
	auto fname=fd.rename?fd.rename:fd.name;
	auto ftypeSubst=ctx.subst.dup;
	Identifier nname=fname;
	if(fname&&bindNameInEnclosing) nname=ctx.bindVar(fname,fd.ftype);
	auto bctx=ctx.nested();
	if(fname&&!bindNameInEnclosing) nname=bctx.bindVar(fname,fd.ftype);
	bool changed=nname !is fname;
	auto nparams=fd.params.dup;
	Parameter freshen(Parameter p,Expression ndtype,Expression nvtype,Identifier pname,Identifier npname){
		auto np=new Parameter(p.isConst,npname,ndtype);
		np.copyAnalyzedFieldsFrom(p);
		np.vtype=nvtype;
		np.scope_=p.scope_;
		if(bctx.declMap) (*bctx.declMap)[p]=np;
		return np;
	}
	foreach(ref p;nparams){
		auto ndtype=p.dtype&&p.dtype.isSemCompleted()?useSubstitute(p.dtype,bctx):p.dtype;
		auto nvtype=p.vtype&&p.vtype.isSemCompleted()?useSubstitute(p.vtype,bctx):p.vtype;
		auto pname=p.rename?p.rename:p.name;
		Identifier npname=pname;
		if(pname) npname=bctx.bindVar(pname,nvtype?nvtype:ndtype);
		if(ndtype is p.dtype&&nvtype is p.vtype&&npname is pname) continue;
		auto edtype=p.dtype?p.dtype.eval():null;
		auto evtype=p.vtype?p.vtype.eval():null;
		if(edtype==ndtype&&evtype==nvtype&&npname is pname) continue;
		p=freshen(p,ndtype,nvtype,pname,npname);
		changed=true;
	}
	Scope savedLocalRoot;
	if(bctx.tt){ savedLocalRoot=bctx.tt.localRoot; bctx.tt.localRoot=fd.fscope_; }
	scope(exit) if(bctx.tt) bctx.tt.localRoot=savedLocalRoot;
	auto nrret=fd.rret&&fd.rret.isSemCompleted()?useSubstitute(fd.rret,bctx):fd.rret;
	auto nret=fd.ret&&fd.ret.isSemCompleted()?useSubstitute(fd.ret,bctx):fd.ret;
	CompoundExp nbody=null;
	if(fd.body_) nbody=substituteBlockCompound(fd.body_,bctx);
	if(bctx.changed) ctx.changed=true;
	bool freshParams=false;
	foreach(i, p; fd.params) if(nparams[i] is p){ freshParams=true; break; }
	if(freshParams){
		foreach(i, p; fd.params) if(nparams[i] is p){ auto pname=p.rename?p.rename:p.name; nparams[i]=freshen(p,p.dtype,p.vtype,pname,pname); }
	}
	auto r=new FunctionDef(nname,nparams,fd.isTuple,nrret,nbody);
	r.copyAnalyzedFieldsFrom(fd);
	r.ret=nret;
	r.scope_=fd.scope_;
	r.fscope_=new FunctionScope(r.scope_,r);
	foreach(np;r.params) np.scope_=r.fscope_;
	if(fd.ftype){
		auto nftype=ftypeSubst.length?fd.ftype.substitute(ftypeSubst,ctx.tt):fd.ftype;
		r.ftype=cast(FunTy)nftype;
		assert(!!r.ftype);
	}
	if(bctx.declMap) (*bctx.declMap)[fd]=r;
	if(fname){
		Expression.CopyArgs cargs={preserveSemantic:true};
		auto use=fname.copy(cargs);
		use.id=nname.id;
		use.meaning=r;
		if(!use.scope_) use.scope_=fd.scope_;
		use.constLookup=true;
		use.byRef=false;
		use.implicitDup=false;
		if(!use.type) use.type=fd.ftype;
		if(!use.isSemCompleted()&&!use.isSemError()&&use.type&&use.type.isSemEvaluated()) use.sstate=SemState.completed;
		(bindNameInEnclosing?ctx.subst:bctx.subst)[fname.id]=use;
		if(r.body_){
			Expression[Id] rsubst;
			rsubst[nname.id]=use;
			void[0][Id] rtaken;
			Declaration[Declaration] rdeclMap;
			auto rctx=BlockSubst(rsubst,null,&rtaken,&rdeclMap,false);
			r.body_=substituteBlockCompound(r.body_,rctx);
		}
	}
	rescopeTwin(r,fd,bctx);
	computeCapturesFromBody(r);
	ctx.changed=true;
	return r;
}

// make a substituted function definition independent of the function it was
// substituted from: fresh nested scopes with their own split/merge graphs and
// forgottenVars, and identifiers rebound to the fresh declarations
private void rescopeTwin(FunctionDef r,FunctionDef fd,ref BlockSubst bctx){
	if(!r.body_) return;
	Declaration[Declaration] dmap;
	Scope[Scope] smap;
	foreach(i,p;fd.params) dmap[p]=r.params[i];
	smap[fd.fscope_]=r.fscope_;
	Expression.CopyArgs cargs={preserveSemantic:true};

	Scope mapScope(Scope s){ return s is null?null:smap.get(s,s); }
	Expression delegate(Expression) rescopeCopy;
	Declaration mapDecl(Declaration d){
		if(!d) return null;
		if(d is fd) return r;
		if(auto p=d in dmap) return *p;
		if(!cast(FunctionDef)d&&d.scope_&&d.scope_.isNestedIn(fd.fscope_)){
			auto vd=cast(VarDecl)d;
			assert(vd,"rescopeTwin: unexpected declaration in substituted function body");
			auto nid=d.name?d.name.id:Id();
			bool fromChain=false;
			for(Declaration a=d;;){
				auto nxt=a.splitFrom?a.splitFrom:(a.mergedFrom.length==1?a.mergedFrom[0]:null);
				if(!nxt) break;
				if(auto p=nxt in dmap){ if((*p).name){ nid=(*p).name.id; fromChain=true; } break; }
				a=nxt;
			}
			auto nd=new VarDecl(d.name?new Identifier(nid):null);
			nd.copyAnalyzedFieldsFrom(d);
			// names inherited via the split/merge lineage already track the
			// twin's own renaming; otherwise keep the template's rename
			if(d.rename&&!fromChain) nd.rename=new Identifier(d.rename.id);
			dmap[d]=nd;
			nd.scope_=mapScope(d.scope_);
			nd.vtype=vd.vtype?(vd.vtype.isSemEvaluated()?vd.vtype:rescopeCopy(useSubstitute(vd.vtype,bctx))):null;
			nd.dtype=vd.dtype?(vd.dtype.isSemEvaluated()?vd.dtype:rescopeCopy(useSubstitute(vd.dtype,bctx))):null;
			return nd;
		}
		if(auto pe=d.getId in bctx.subst){
			// declarations lexically outer to the substituted function are
			// substituted away; others (e.g. from inserted values) stay
			if(d.scope_&&fd.scope_&&fd.scope_.isNestedIn(d.scope_)){
				if(auto id=cast(Identifier)*pe) if(id.meaning) return id.meaning;
				return null;
			}
		}
		return d;
	}
	// the generic BinaryExp copy drops checker-computed fields
	void fixAssignFields(Expression e,Expression r){
		import std.algorithm: map, endsWith;
		import std.array: array;
		if(auto sae=cast(AAssignExp)e){
			auto rae=cast(AAssignExp)r;
			if(sae.replacements.length)
				rae.replacements=sae.replacements.map!(x=>AAssignExp.Replacement(mapDecl(x.previous),mapDecl(x.new_))).array;
		}
		import ast.parser, ast.lexer;
		static foreach(op;binaryOps){
			static if(op.endsWith("←")&&op!="←"){
				if(auto se=cast(BinaryExp!(Tok!op))e)
					if(se.operation) (cast(BinaryExp!(Tok!op))r).operation=rescopeCopy(se.operation);
			}
		}
		if(auto se=cast(BinaryExp!(Tok!":="))e){
			auto dr=cast(BinaryExp!(Tok!":="))r;
			dr.isSwap=se.isSwap;
			if(se.replacements.length)
				dr.replacements=se.replacements.map!(x=>AAssignExp.Replacement(mapDecl(x.previous),mapDecl(x.new_))).array;
		}
	}
	rescopeCopy=(Expression e){ return e?e.copy(cargs):null; };
	void fixup(Expression r,Expression e){
		r.loc=e.loc;
		r.sstate=e.sstate;
		r.type=e.type?(e.type.isSemEvaluated()?e.type:e.type.copy(cargs)):null;
		r.constLookup=e.constLookup;
		r.brackets=e.brackets;
		r.byRef=e.byRef;
		r.implicitDup=e.implicitDup;
	}
	Expression mapExp(Expression e,ref Expression.CopyArgs args){
		if(auto nfd=cast(FunctionDef)e){
			nfd.scope_=mapScope(nfd.scope_);
			if(nfd.fscope_&&nfd.fscope_.parent) nfd.fscope_.parent=mapScope(nfd.fscope_.parent);
			foreach(np;nfd.params){
				if(np.dtype) np.dtype=np.dtype.isSemEvaluated()?np.dtype:rescopeCopy(np.dtype);
				if(np.vtype) np.vtype=np.vtype.isSemEvaluated()?np.vtype:rescopeCopy(np.vtype);
			}
			if(nfd.rret) nfd.rret=nfd.rret.isSemEvaluated()?nfd.rret:rescopeCopy(nfd.rret);
			if(nfd.ret) nfd.ret=nfd.ret.isSemEvaluated()?nfd.ret:rescopeCopy(nfd.ret);
			if(nfd.body_) nfd.body_=cast(CompoundExp)rescopeCopy(nfd.body_);
			computeCapturesFromBody(nfd);
			return nfd;
		}
		if(auto le=cast(LambdaExp)e){
			auto r=new LambdaExp(le.orig,cast(FunctionDef)mapExp(le.fd,args));
			fixup(r,le);
			return r;
		}
		if(auto fe=cast(ForExp)e){
			ForAggregate naggr=fe.aggr;
			if(auto rng=fe.aggr.isRange()){
				naggr=ForAggregate(ForRange(rng.leftExclusive,rng.left?rescopeCopy(rng.left):null,rng.step?rescopeCopy(rng.step):null,rng.rightExclusive,rng.right?rescopeCopy(rng.right):null));
			}else if(auto cont=fe.aggr.isContainer()){
				naggr=ForAggregate(ForContainer(rescopeCopy(cont.e)));
			}
			auto r=new ForExp(fe.var?cast(Identifier)rescopeCopy(fe.var):null,fe.pattern?rescopeCopy(fe.pattern):null,naggr,cast(CompoundExp)rescopeCopy(fe.bdy));
			r.fescope_=cast(BlockScope)mapScope(fe.fescope_);
			r.loopVar=cast(VarDecl)mapDecl(fe.loopVar);
			fixup(r,fe);
			return r;
		}
		if(auto we=cast(WhileExp)e){
			auto r=new WhileExp(rescopeCopy(we.cond),cast(CompoundExp)rescopeCopy(we.bdy));
			fixup(r,we);
			return r;
		}
		if(auto re=cast(RepeatExp)e){
			auto r=new RepeatExp(rescopeCopy(re.num),cast(CompoundExp)rescopeCopy(re.bdy));
			fixup(r,re);
			return r;
		}
		if(auto ve=cast(VectorForExp)e){
			auto r=new VectorForExp(cast(ForExp)mapExp(ve.fe,args));
			r.fd=ve.fd?cast(FunctionDef)mapExp(ve.fd,args):null;
			r.len=ve.len?rescopeCopy(ve.len):null;
			fixup(r,ve);
			return r;
		}
		return null;
	}
	Scope mapScopeTree(Scope s,Scope twincarried,Scope parent){
		if(auto p=s in smap) return *p;
		auto bs=cast(BlockScope)s;
		BlockScope ns;
		if(auto ts=cast(TypeScope)twincarried){
			ns=ts;
		}else{
			assert(bs,"rescopeTwin: expected BlockScope");
			ns=new BlockScope(parent,bs.restriction_);
			ns.isLoopBody=bs.isLoopBody;
		}
		smap[s]=ns;
		if(twincarried !is s) smap[twincarried]=ns;
		if(bs){
			foreach(d;bs.splitVars){
				auto sf=mapDecl(d.splitFrom);
				if(!sf) continue;
				auto nd=mapDecl(d);
				nd.splitFrom=sf;
				ns.splitVars~=nd;
			}
			foreach(d;bs.mergedVars){
				auto mi=mapDecl(d.mergedInto);
				if(!mi) continue;
				auto nd=mapDecl(d);
				nd.mergedInto=mi;
				ns.mergedVars~=nd;
			}
			foreach(d;bs.forgottenVars) if(auto nd=mapDecl(d)) ns.forgottenVars~=nd;
			foreach(d;bs.forgottenVarsOnEntry) if(auto nd=mapDecl(d)) ns.forgottenVarsOnEntry~=nd;
		}
		return ns;
	}
	cargs.mapDecl=&mapDecl; cargs.postCopy=&fixAssignFields;
	cargs.mapScope=&mapScope;
	cargs.mapExp=&mapExp;
	auto bparent=cast(Scope)r.fscope_;
	if(r.body_.blscope_) bparent=mapScopeTree(fd.body_.blscope_,r.body_.blscope_,r.fscope_);
	walkStmts(fd.body_.s,r.body_.s,bparent,&dmap,&mapScopeTree);
	Expression shareTy(Expression e){ return e?(e.isSemEvaluated()?e:rescopeCopy(e)):null; }
	r.body_=cast(CompoundExp)rescopeCopy(r.body_);
	if(r.rret) r.rret=shareTy(r.rret);
	if(r.ret) r.ret=shareTy(r.ret);
	foreach(np;r.params){
		if(np.dtype) np.dtype=shareTy(np.dtype);
		if(np.vtype) np.vtype=shareTy(np.vtype);
	}
	// rebuild split/merge links in template order (creation order)
	void[0][Declaration] seen;
	for(bool progress=true;progress;){
		progress=false;
		foreach(td,nd;dmap){
			if(td in seen) continue;
			seen[td]=[]; progress=true;
			if(td.splitFrom) if(auto m=mapDecl(td.splitFrom)) nd.splitFrom=m;
			if(td.mergedInto) if(auto m=mapDecl(td.mergedInto)) nd.mergedInto=m;
			if(td.splitInto.length){
				Declaration[] si;
				foreach(x;td.splitInto) if(auto m=mapDecl(x)) si~=m;
				nd.splitInto=si;
			}
			if(td.mergedFrom.length){
				Declaration[] mf;
				foreach(x;td.mergedFrom) if(auto m=mapDecl(x)) mf~=m;
				nd.mergedFrom=mf;
			}
		}
	}
	// give twin scopes their own last-use state (hqir re-analyzes lowered
	// fragments against them)
	Scope[ast.lastuse.LastUses*] luOwner;
	foreach(ts,ns;smap)
		if(ts is fd.fscope_||(fd.fscope_&&ts.isNestedIn(fd.fscope_)))
			luOwner[&ts.lastUses]=ns;
	foreach(ts,ns;smap){
		if(ts is fd.fscope_||(fd.fscope_&&ts.isNestedIn(fd.fscope_))){
			ns.lastUses.remapFrom(ts.lastUses,&mapDecl,&mapScope);
			if(auto p=ts.lastUses.parent)
				if(auto owner=p in luOwner) ns.lastUses.parent=&(*owner).lastUses;
		}
	}
}

// walks template/twin statement trees in parallel, rebuilding the twin's
// scope tree and declaration map (see rescopeTwin)
private alias MapScopeTreeDg = Scope delegate(Scope tpl,Scope twin,Scope fparent);
private void walkStmt(FunctionDef tfd,Expression twstmt,Scope fparent,Declaration[Declaration]* dmap,MapScopeTreeDg mapFn){
	if(auto wfd=cast(FunctionDef)twstmt){ (*dmap)[tfd]=wfd; wfd.canonicalSource_=tfd.canonicalSource; }
}
private void walkStmt(CompoundExp ce,Expression twstmt,Scope fparent,Declaration[Declaration]* dmap,MapScopeTreeDg mapFn){
	auto ce2=cast(CompoundExp)twstmt;
	assert(!!ce2);
	if(ce.blscope_){
		auto ns=mapFn(ce.blscope_,ce2.blscope_,fparent);
		walkStmts(ce.s,ce2.s,ns,dmap,mapFn);
	}else walkStmts(ce.s,ce2.s,fparent,dmap,mapFn);
}
private void walkStmt(IteExp ite,Expression twstmt,Scope fparent,Declaration[Declaration]* dmap,MapScopeTreeDg mapFn){
	auto ite2=cast(IteExp)twstmt;
	assert(!!ite2);
	walkStmts([ite.then],[ite2.then],fparent,dmap,mapFn);
	if(ite.othw) walkStmts([ite.othw],[ite2.othw],fparent,dmap,mapFn);
}
private void walkStmt(ForExp fe,Expression twstmt,Scope fparent,Declaration[Declaration]* dmap,MapScopeTreeDg mapFn){
	auto fe2=cast(ForExp)twstmt;
	assert(!!fe2);
	if(fe.fescope_) mapFn(fe.fescope_,fe2.fescope_,fparent);
	walkStmts([fe.bdy],[fe2.bdy],fparent,dmap,mapFn);
}
private void walkStmt(WhileExp we,Expression twstmt,Scope fparent,Declaration[Declaration]* dmap,MapScopeTreeDg mapFn){
	auto we2=cast(WhileExp)twstmt;
	assert(!!we2);
	walkStmts([we.bdy],[we2.bdy],fparent,dmap,mapFn);
}
private void walkStmt(RepeatExp re,Expression twstmt,Scope fparent,Declaration[Declaration]* dmap,MapScopeTreeDg mapFn){
	auto re2=cast(RepeatExp)twstmt;
	assert(!!re2);
	walkStmts([re.bdy],[re2.bdy],fparent,dmap,mapFn);
}
private void walkStmt(CommaExp ce,Expression twstmt,Scope fparent,Declaration[Declaration]* dmap,MapScopeTreeDg mapFn){
	auto ce2=cast(CommaExp)twstmt;
	assert(!!ce2);
	walkStmts([ce.e1],[ce2.e1],fparent,dmap,mapFn);
	walkStmts([ce.e2],[ce2.e2],fparent,dmap,mapFn);
}
static if(language==silq)
private void walkStmt(WithExp we,Expression twstmt,Scope fparent,Declaration[Declaration]* dmap,MapScopeTreeDg mapFn){
	auto we2=cast(WithExp)twstmt;
	assert(!!we2);
	void walkBlock(CompoundExp t,CompoundExp w){
		if(t.blscope_){
			auto ns=mapFn(t.blscope_,w.blscope_,fparent);
			walkStmts(t.s,w.s,ns,dmap,mapFn);
		}else walkStmts(t.s,w.s,fparent,dmap,mapFn);
	}
	if(we.trans) walkBlock(we.trans,we2.trans);
	if(we.bdy) walkBlock(we.bdy,we2.bdy);
	if(we.itrans) walkBlock(we.itrans,we2.itrans);
}
private void walkStmt(T)(T stmt,Expression twstmt,Scope fparent,Declaration[Declaration]* dmap,MapScopeTreeDg mapFn)
	if(is(T==CallExp)||is(T==TypeAnnotationExp)||is(T==ReturnExp)||is(T==ForgetExp)||is(T==AssertExp)||is(T==ObserveExp)||is(T==CObserveExp))
{
	// statements without nested blocks need no scope remapping
}
private void walkStmtDefault(Expression stmt,Expression twstmt,Scope fparent,Declaration[Declaration]* dmap,MapScopeTreeDg mapFn){
	if(auto le=cast(LetExp)stmt){
		auto le2=cast(LetExp)twstmt;
		assert(!!le2);
		walkStmts([le.s],[le2.s],fparent,dmap,mapFn);
	}
}
private void walkStmts(Expression[] tpl,Expression[] twin,Scope fparent,Declaration[Declaration]* dmap,MapScopeTreeDg mapFn){
	assert(tpl.length==twin.length);
	foreach(i,stmt;tpl) dispatchStm!(walkStmt,walkStmtDefault)(stmt,twin[i],fparent,dmap,mapFn);
}

void computeCapturesFromBody(FunctionDef fd){
	fd.capturedDecls=[];
	fd.captures=null;
	if(!fd.body_) return;
	functionDefFreeVarsImpl(fd,(id){
		if(id.lazyCapture) return 0;
		auto m=id.meaning;
		if(m is fd||m&&m.isSplitFrom(fd)) return 0;
		if(m&&m.scope_&&m.scope_.getFunction()){
			if(m !in fd.captures) fd.capturedDecls~=m;
			fd.captures[m]~=id;
		}
		return 0;
	});
}

Expression substituteFunctionDefExp(FunctionDef fd,Expression[Id] subst,bool bindNameInEnclosing=false,TypeTransition* tt=null){
	Expression[Id] active;
	foreach(k,v;subst) if(functionDefFreeVarsImpl(fd,(id)=>id.id==k?1:0)) active[k]=v;
	if(!active.length) return fd;
	void[0][Id] taken;
	foreach(k,v;subst) taken[k]=[];
	functionDefFreeVarsImpl(fd,(id){ taken[id.id]=[]; return 0; });
	collectFunctionBoundNames(fd,taken);
	Declaration[Declaration] declMap;
	auto ctx=BlockSubst(active,null,&taken,&declMap,false,tt);
	return substituteFunctionDefImpl(fd,ctx,bindNameInEnclosing);
}
