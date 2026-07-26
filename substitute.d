module ast.substitute;

import ast.expression, ast.type, ast.declaration, ast.scope_;
import astopt;

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
	if(auto id=cast(Identifier)lhs) return dg(id);
	if(auto tae=cast(TypeAnnotationExp)lhs) return defineLhsBoundVarsImpl(tae.e,dg);
	if(auto tpl=cast(TupleExp)lhs){
		foreach(x;tpl.e) if(auto r=defineLhsBoundVarsImpl(x,dg)) return r;
		return 0;
	}
	if(auto ce=cast(CatExp)lhs){
		if(auto r=defineLhsBoundVarsImpl(ce.e1,dg)) return r;
		return defineLhsBoundVarsImpl(ce.e2,dg);
	}
	if(auto ce=cast(CallExp)lhs){
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
	if(auto ie=cast(IndexExp)lhs) return defineLhsBoundVarsImpl(ie.e,dg);
	if(auto fe=cast(FieldExp)lhs) return defineLhsBoundVarsImpl(fe.e,dg);
	if(auto le=cast(LetExp)lhs){
		return le.freeVarsImpl((id)=>id.constLookup||id.implicitDup?0:dg(id));
	}
	return 0;
}

int defineLhsFreeVarsImpl(Expression lhs,scope int delegate(Identifier) dg){
	if(cast(Identifier)lhs) return 0;
	if(auto tae=cast(TypeAnnotationExp)lhs){
		if(auto r=defineLhsFreeVarsImpl(tae.e,dg)) return r;
		if(tae.t) return tae.t.freeVarsImpl(dg);
		return 0;
	}
	if(auto tpl=cast(TupleExp)lhs){
		foreach(x;tpl.e) if(auto r=defineLhsFreeVarsImpl(x,dg)) return r;
		return 0;
	}
	if(auto ce=cast(CatExp)lhs){
		if(auto r=defineLhsFreeVarsImpl(ce.e1,dg)) return r;
		return defineLhsFreeVarsImpl(ce.e2,dg);
	}
	if(auto ce=cast(CallExp)lhs){
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
	if(auto ie=cast(IndexExp)lhs) return lhs.freeVarsImpl(dg);
	if(auto fe=cast(FieldExp)lhs) return lhs.freeVarsImpl(dg);
	if(auto le=cast(LetExp)lhs)
		return le.freeVarsImpl((id)=>id.constLookup||id.implicitDup?dg(id):0);
	return lhs.freeVarsImpl(dg);
}

int statementBoundVarsImpl(Expression stmt,scope int delegate(Identifier) dg){
	if(auto de=cast(DefineExp)stmt) return defineLhsBoundVarsImpl(de.e1,dg);
	if(auto fd=cast(FunctionDef)stmt){
		auto name=fd.rename?fd.rename:fd.name;
		return name?dg(name):0;
	}
	if(auto ce=cast(CommaExp)stmt){
		if(auto r=statementBoundVarsImpl(ce.e1,dg)) return r;
		return statementBoundVarsImpl(ce.e2,dg);
	}
	if(auto ite=cast(IteExp)stmt){
		foreach(x;ite.then.s) if(auto r=statementBoundVarsImpl(x,dg)) return r;
		if(ite.othw) foreach(x;ite.othw.s) if(auto r=statementBoundVarsImpl(x,dg)) return r;
		return 0;
	}
	if(auto ce=cast(CompoundExp)stmt){
		if(!ce.blscope_)
			foreach(x;ce.s) if(auto r=statementBoundVarsImpl(x,dg)) return r;
		return 0;
	}
	return 0;
}

int statementFreeVarsImpl(Expression stmt,scope int delegate(Identifier) dg){
	if(auto de=cast(DefineExp)stmt){
		if(auto r=de.e2.freeVarsImpl(dg)) return r;
		return defineLhsFreeVarsImpl(de.e1,dg);
	}
	if(auto fd=cast(FunctionDef)stmt) return functionDefFreeVarsImpl(fd,dg);
	if(auto ce=cast(CommaExp)stmt){
		if(auto r=statementFreeVarsImpl(ce.e1,dg)) return r;
		return statementFreeVarsImpl(ce.e2,dg);
	}
	if(auto ce=cast(CompoundExp)stmt) return blockFreeVarsImpl(ce.s,null,dg);
	if(auto ite=cast(IteExp)stmt){
		if(auto r=ite.cond.freeVarsImpl(dg)) return r;
		if(auto r=blockFreeVarsImpl(ite.then.s,null,dg)) return r;
		if(ite.othw) if(auto r=blockFreeVarsImpl(ite.othw.s,null,dg)) return r;
		return 0;
	}
	if(auto fe=cast(ForExp)stmt){
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
	if(auto we=cast(WhileExp)stmt){
		if(auto r=we.cond.freeVarsImpl(dg)) return r;
		return blockFreeVarsImpl(we.bdy.s,null,dg);
	}
	if(auto re=cast(RepeatExp)stmt){
		if(auto r=re.num.freeVarsImpl(dg)) return r;
		return blockFreeVarsImpl(re.bdy.s,null,dg);
	}
	if(auto re=cast(ReturnExp)stmt) return re.e?re.e.freeVarsImpl(dg):0;
	if(auto fe=cast(ForgetExp)stmt){
		if(auto r=fe.var.freeVarsImpl(dg)) return r;
		return fe.val?fe.val.freeVarsImpl(dg):0;
	}
	if(auto le=cast(LetExp)stmt) return le.freeVarsImpl(dg);
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
	if(auto de=cast(DefineExp)stmt){
		if(auto le=cast(LambdaExp)de.e2) collectFunctionBoundNames(le.fd,names);
		return;
	}
	if(auto fd=cast(FunctionDef)stmt){ collectFunctionBoundNames(fd,names); return; }
	if(auto ce=cast(CommaExp)stmt){
		collectBoundNamesImpl(ce.e1,names);
		collectBoundNamesImpl(ce.e2,names);
		return;
	}
	if(auto ce=cast(CompoundExp)stmt){ foreach(x;ce.s) collectBoundNamesImpl(x,names); return; }
	if(auto ite=cast(IteExp)stmt){
		foreach(x;ite.then.s) collectBoundNamesImpl(x,names);
		if(ite.othw) foreach(x;ite.othw.s) collectBoundNamesImpl(x,names);
		return;
	}
	if(auto fe=cast(ForExp)stmt){
		if(fe.var) names[fe.var.id]=[];
		if(fe.pattern) defineLhsBoundVarsImpl(fe.pattern,(id){ names[id.id]=[]; return 0; });
		foreach(x;fe.bdy.s) collectBoundNamesImpl(x,names);
		return;
	}
	if(auto we=cast(WhileExp)stmt){ foreach(x;we.bdy.s) collectBoundNamesImpl(x,names); return; }
	if(auto re=cast(RepeatExp)stmt){ foreach(x;re.bdy.s) collectBoundNamesImpl(x,names); return; }
	if(auto le=cast(LetExp)stmt){ foreach(x;le.s.s) collectBoundNamesImpl(x,names); return; }
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
			if(declMap) (*declMap)[vd]=twin;
		}
		subst[b]=use;
		changed=true;
		return nid;
	}
}

private VarDecl getVarDeclTwin(VarDecl orig,Identifier nname,Expression nvtype){
	auto twin=new VarDecl(nname);
	twin.vtype=nvtype;
	twin.dtype=orig.dtype;
	twin.scope_=orig.scope_;
	twin.loc=orig.loc;
	if(orig.isSemError()) twin.sstate=SemState.error;
	else if(orig.isSemCompleted()) twin.sstate=SemState.completed;
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
	if(auto id=cast(Identifier)lhs){
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
	if(auto tae=cast(TypeAnnotationExp)lhs){
		auto ne=substituteLValue(tae.e,ctx);
		auto nt=useSubstitute(tae.t,ctx);
		if(ne is tae.e&&nt is tae.t) return lhs;
		auto r=new TypeAnnotationExp(ne,nt,tae.annotationType);
		return finishStatement(r,lhs,ctx);
	}
	if(auto tpl=cast(TupleExp)lhs){
		auto ne=tpl.e.dup;
		bool chg=false;
		foreach(ref x;ne){
			auto nx=substituteLValue(x,ctx);
			if(nx !is x) chg=true;
			x=nx;
		}
		if(!chg) return lhs;
		auto r=new TupleExp(ne);
		return finishStatement(r,lhs,ctx);
	}
	if(auto ie=cast(IndexExp)lhs){
		auto nagg=substituteLValue(ie.e,ctx);
		auto na=useSubstitute(ie.a,ctx);
		if(nagg is ie.e&&na is ie.a) return lhs;
		auto r=new IndexExp(nagg,na);
		r.isArraySyntax=ie.isArraySyntax;
		static if(language==silq) r.isClassical_=ie.isClassical_;
		return finishStatement(r,lhs,ctx);
	}
	if(auto fe=cast(FieldExp)lhs){
		auto nagg=substituteLValue(fe.e,ctx);
		if(nagg is fe.e) return lhs;
		auto r=new FieldExp(nagg,fe.f);
		return finishStatement(r,lhs,ctx);
	}
	if(auto ce=cast(CatExp)lhs){
		auto ne1=substituteLValue(ce.e1,ctx);
		auto ne2=substituteLValue(ce.e2,ctx);
		if(ne1 is ce.e1&&ne2 is ce.e2) return lhs;
		auto r=new CatExp(ne1,ne2);
		return finishStatement(r,lhs,ctx);
	}
	if(auto ce=cast(CallExp)lhs){
		auto ne=useSubstitute(ce.e,ctx);
		auto narg=substituteLValue(ce.arg,ctx);
		if(ne is ce.e&&narg is ce.arg) return lhs;
		auto r=new CallExp(ne,narg,ce.isSquare,ce.isClassical_);
		return finishStatement(r,lhs,ctx);
	}
	if(auto le=cast(LetExp)lhs){
		auto nctx=ctx.nested();
		foreach(stmt;le.s.s) collectBoundNamesImpl(stmt,*nctx.taken);
		auto ns=substituteBlockCompound(le.s,nctx);
		auto ne=substituteLValue(le.e,nctx);
		if(nctx.changed) ctx.changed=true;
		if(ns is le.s&&ne is le.e) return lhs;
		auto r=new LetExp(ns,ne);
		return finishStatement(r,lhs,ctx);
	}
	return useSubstitute(lhs,ctx);
}

private Expression substituteDefineLhs(Expression lhs,ref BlockSubst ctx){
	if(!lhs) return null;
	if(auto id=cast(Identifier)lhs){
		auto nid=ctx.bindVar(id,id.type);
		return nid;
	}
	if(auto tae=cast(TypeAnnotationExp)lhs){
		auto nt=useSubstitute(tae.t,ctx);
		auto ne=substituteDefineLhs(tae.e,ctx);
		if(ne is tae.e&&nt is tae.t) return lhs;
		auto r=new TypeAnnotationExp(ne,nt,tae.annotationType);
		return finishStatement(r,lhs,ctx);
	}
	if(auto tpl=cast(TupleExp)lhs){
		auto ne=tpl.e.dup;
		bool chg=false;
		foreach(ref x;ne){
			auto nx=substituteDefineLhs(x,ctx);
			if(nx !is x) chg=true;
			x=nx;
		}
		if(!chg) return lhs;
		auto r=new TupleExp(ne);
		return finishStatement(r,lhs,ctx);
	}
	if(auto ce=cast(CatExp)lhs){
		auto ne1=substituteDefineLhs(ce.e1,ctx);
		auto ne2=substituteDefineLhs(ce.e2,ctx);
		if(ne1 is ce.e1&&ne2 is ce.e2) return lhs;
		auto r=new CatExp(ne1,ne2);
		return finishStatement(r,lhs,ctx);
	}
	if(auto ce=cast(CallExp)lhs){
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
		if(ne is ce.e&&narg is ce.arg) return lhs;
		auto r=new CallExp(ne,narg,ce.isSquare,ce.isClassical_);
		return finishStatement(r,lhs,ctx);
	}
	if(auto ie=cast(IndexExp)lhs){
		auto nagg=substituteLValue(ie.e,ctx);
		auto na=useSubstitute(ie.a,ctx);
		defineLhsBoundVarsImpl(ie.e,(id){ ctx.subst.remove(id.id); return 0; });
		if(nagg is ie.e&&na is ie.a) return lhs;
		auto r=new IndexExp(nagg,na);
		r.isArraySyntax=ie.isArraySyntax;
		static if(language==silq) r.isClassical_=ie.isClassical_;
		return finishStatement(r,lhs,ctx);
	}
	if(auto fe=cast(FieldExp)lhs){
		auto nagg=substituteLValue(fe.e,ctx);
		defineLhsBoundVarsImpl(fe.e,(id){ ctx.subst.remove(id.id); return 0; });
		if(nagg is fe.e) return lhs;
		auto r=new FieldExp(nagg,fe.f);
		return finishStatement(r,lhs,ctx);
	}
	if(auto le=cast(LetExp)lhs){
		defineLhsBoundVarsImpl(le,(id){ ctx.subst.remove(id.id); return 0; });
		return substituteLValue(le,ctx);
	}
	return substituteLValue(lhs,ctx);
}

private Expression substituteStatement(Expression stmt,ref BlockSubst ctx){
	if(auto de=cast(DefineExp)stmt){
		auto ne2=substituteLValue(de.e2,ctx);
		auto ne1=substituteDefineLhs(de.e1,ctx);
		if(ne1 is de.e1&&ne2 is de.e2) return stmt;
		auto r=new DefineExp(ne1,ne2);
		return finishStatement(r,stmt,ctx);
	}
	if(auto fd=cast(FunctionDef)stmt){
		auto nfd=substituteFunctionDefImpl(fd,ctx,true);
		if(nfd !is fd){
			if(ctx.declMap) (*ctx.declMap)[fd]=nfd;
			auto fname=fd.rename?fd.rename:fd.name;
			if(fname) if(auto p=fname.id in ctx.subst)
				if(auto uid=cast(Identifier)(*p))
					if(uid.meaning is fd||uid.meaning is null) uid.meaning=nfd;
		}
		return nfd;
	}
	if(auto ce=cast(CommaExp)stmt){
		auto ne1=substituteStatement(ce.e1,ctx);
		auto ne2=substituteStatement(ce.e2,ctx);
		if(ne1 is ce.e1&&ne2 is ce.e2) return stmt;
		auto r=new CommaExp(ne1,ne2);
		return finishStatement(r,stmt,ctx);
	}
	if(auto ite=cast(IteExp)stmt){
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
		if(ncond is ite.cond&&nthen is ite.then&&nothw is ite.othw) return stmt;
		auto r=new IteExp(ncond,nthen,nothw);
		return finishStatement(r,stmt,ctx);
	}
	if(auto ce=cast(CompoundExp)stmt){
		if(!ce.blscope_) return substituteBlockCompound(ce,ctx);
		auto nctx=ctx.nested();
		auto r=substituteBlockCompound(ce,nctx);
		if(nctx.changed) ctx.changed=true;
		return r;
	}
	if(auto fe=cast(ForExp)stmt){
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
		if(!aggrChanged&&nvar is fe.var&&npattern is fe.pattern&&nbdy is fe.bdy) return stmt;
		auto r=new ForExp(nvar,npattern,naggr,nbdy);
		r.fescope_=fe.fescope_;
		r.loopVar=fe.loopVar;
		if(fe.loopVar&&bctx.declMap)
			if(auto p=cast(Declaration)fe.loopVar in *bctx.declMap)
				if(auto nvd=cast(VarDecl)*p) r.loopVar=nvd;
		return finishStatement(r,stmt,ctx);
	}
	if(auto we=cast(WhileExp)stmt){
		auto ncond=useSubstitute(we.cond,ctx);
		auto bctx=ctx.nested();
		auto nbdy=substituteBlockCompound(we.bdy,bctx);
		if(bctx.changed) ctx.changed=true;
		if(ncond is we.cond&&nbdy is we.bdy) return stmt;
		auto r=new WhileExp(ncond,nbdy);
		return finishStatement(r,stmt,ctx);
	}
	if(auto re=cast(RepeatExp)stmt){
		auto nnum=useSubstitute(re.num,ctx);
		auto bctx=ctx.nested();
		auto nbdy=substituteBlockCompound(re.bdy,bctx);
		if(bctx.changed) ctx.changed=true;
		if(nnum is re.num&&nbdy is re.bdy) return stmt;
		auto r=new RepeatExp(nnum,nbdy);
		return finishStatement(r,stmt,ctx);
	}
	if(auto re=cast(ReturnExp)stmt){
		auto ne=re.e?substituteLValue(re.e,ctx):null;
		bool remapped=false;
		auto nfv=remapDecls(re.forgottenVars,ctx.declMap,remapped);
		if(ne is re.e&&!remapped) return stmt;
		auto r=new ReturnExp(ne);
		r.expected=re.expected;
		r.forgottenVars=nfv;
		return finishStatement(r,stmt,ctx);
	}
	if(auto fe=cast(ForgetExp)stmt){
		auto nvar=substituteLValue(fe.var,ctx);
		auto nval=fe.val?useSubstitute(fe.val,ctx):null;
		if(nvar is fe.var&&nval is fe.val) return stmt;
		auto r=new ForgetExp(nvar,nval);
		return finishStatement(r,stmt,ctx);
	}
	if(auto ae=cast(AAssignExp)stmt){
		auto ne1=substituteLValue(ae.e1,ctx);
		auto ne2=useSubstitute(ae.e2,ctx);
		if(ne1 is ae.e1&&ne2 is ae.e2) return stmt;
		auto r=cast(AAssignExp)stmt.copy();
		assert(!!r);
		r.e1=ne1;
		r.e2=ne2;
		r.type=null;
		r.sstate=SemState.initial;
		return finishStatement(r,stmt,ctx);
	}
	return substituteLValue(stmt,ctx);
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
		auto np=new Parameter(p.isConst,npname,ndtype);
		np.vtype=nvtype;
		np.loc=p.loc;
		np.scope_=p.scope_;
		np.sstate=p.sstate;
		auto origp=p;
		p=np;
		changed=true;
		if(bctx.declMap){
			(*bctx.declMap)[origp]=np;
			void mapSplits(Declaration d){
				foreach(sd; d.splitInto){
					(*bctx.declMap)[sd]=np;
					mapSplits(sd);
				}
			}
			mapSplits(origp);
		}
		if(pname){
			Expression.CopyArgs cargs={preserveSemantic:true};
			auto puse=pname.copy(cargs);
			puse.id=npname.id;
			puse.meaning=np;
			if(!puse.scope_) puse.scope_=np.scope_;
			puse.constLookup=true;
			puse.byRef=false;
			puse.implicitDup=false;
			if(!puse.type) puse.type=nvtype?nvtype:ndtype;
			if(!puse.isSemCompleted()&&!puse.isSemError()&&puse.type&&puse.type.isSemEvaluated()) puse.sstate=SemState.completed;
			bctx.subst[pname.id]=puse;
		}
	}
	auto nrret=fd.rret&&fd.rret.isSemCompleted()?useSubstitute(fd.rret,bctx):fd.rret;
	auto nret=fd.ret&&fd.ret.isSemCompleted()?useSubstitute(fd.ret,bctx):fd.ret;
	CompoundExp nbody=null;
	if(fd.body_) nbody=substituteBlockCompound(fd.body_,bctx);
	if(bctx.changed) ctx.changed=true;
	if(!changed&&nrret is fd.rret&&nret is fd.ret&&nbody is fd.body_) return fd;
	auto r=new FunctionDef(nname,nparams,fd.isTuple,nrret,nbody);
	r.isSquare=fd.isSquare;
	r.annotation=fd.annotation;
	r.inferAnnotation=fd.inferAnnotation;
	r.attributes=fd.attributes.dup;
	r.ret=nret;
	r.hasReturn=fd.hasReturn;
	r.retNames=fd.retNames;
	r.loc=fd.loc;
	r.scope_=fd.scope_;
	r.fscope_=fd.fscope_;
	r.context=fd.context;
	r.thisVar=fd.thisVar;
	r.isConstructor=fd.isConstructor;
	r.sealed=fd.sealed;
	r.captureAnnotationReady=fd.captureAnnotationReady;
	r.ftypeFinal=fd.ftypeFinal;
	if(fd.ftype){
		auto nftype=ftypeSubst.length?fd.ftype.substitute(ftypeSubst,ctx.tt):fd.ftype;
		r.ftype=cast(FunTy)nftype;
		assert(!!r.ftype);
	}
	if(fd.isSemError()) r.sstate=SemState.error;
	else if(fd.isSemCompleted()) r.sstate=SemState.completed;
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
			auto rctx=BlockSubst(rsubst,null,&rtaken,null,false);
			r.body_=substituteBlockCompound(r.body_,rctx);
		}
	}
	computeCapturesFromBody(r);
	ctx.changed=true;
	return r;
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
