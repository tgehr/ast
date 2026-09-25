// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

// Lowering of loops to recursive functions (`--remove-loops`):
//  - `splitLoop`: splits a loop into several loops, such that loop-carried lifted state can be lowered
//    into `qfree` recursive functions (with logs communicating values between the loops)
//  - `lowerLoop`: lowers a single loop into a recursive function
//  - early-return elimination: prepares functions whose loops contain `return` statements for `lowerLoop`
module ast.looplowering;
import astopt;

import std.array,std.algorithm,std.range,std.exception;
import std.format, std.conv, util.tuple:Q=Tuple,q=tuple;
import ast.lexer,ast.scope_,ast.expression,ast.type,ast.conversion;
import ast.declaration,ast.error,util;
import ast.semantic_;

void visitStm(Expression e,scope void delegate(Expression) dg){
	if(!e) return;
	dg(e);
	if(auto fd=cast(FunctionDef)e){
		foreach(decl;fd.capturedDecls) foreach(id;fd.captures[decl]) visitStm(id,dg);
		return;
	}
	if(auto fe=cast(ForExp)e){
		if(auto r=fe.aggr.isRange){
			visitStm(r.left,dg);
			visitStm(r.step,dg);
			visitStm(r.right,dg);
		}else if(auto c=fe.aggr.isContainer) visitStm(c.e,dg);
		visitStm(fe.bdy,dg);
		return;
	}
	foreach(c;e.components) visitStm(c,dg);
}
private void visitStmSkip(Expression e,scope bool delegate(Expression) dg){
	if(!e) return;
	if(!dg(e)) return;
	if(auto fd=cast(FunctionDef)e){
		foreach(decl;fd.capturedDecls) foreach(id;fd.captures[decl]) visitStmSkip(id,dg);
		return;
	}
	if(auto fe=cast(ForExp)e){
		if(auto r=fe.aggr.isRange){
			visitStmSkip(r.left,dg);
			visitStmSkip(r.step,dg);
			visitStmSkip(r.right,dg);
		}else if(auto c=fe.aggr.isContainer) visitStmSkip(c.e,dg);
		visitStmSkip(fe.bdy,dg);
		return;
	}
	foreach(c;e.components) visitStmSkip(c,dg);
}
private void walkCond(Expression e,bool cond,scope void delegate(Expression,bool) dg){
	if(!e) return;
	dg(e,cond);
	if(auto fd=cast(FunctionDef)e){
		foreach(decl;fd.capturedDecls) foreach(id;fd.captures[decl]) walkCond(id,cond,dg);
		return;
	}
	if(auto le=cast(LambdaExp)e){
		foreach(decl;le.fd.capturedDecls) foreach(id;le.fd.captures[decl]) walkCond(id,cond,dg);
		return;
	}
	if(auto ite=cast(IteExp)e){
		walkCond(ite.cond,cond,dg);
		walkCond(ite.then,true,dg);
		walkCond(ite.othw,true,dg);
		return;
	}
	if(auto fe=cast(ForExp)e){
		if(auto r=fe.aggr.isRange){
			walkCond(r.left,cond,dg);
			walkCond(r.step,cond,dg);
			walkCond(r.right,cond,dg);
		}else if(auto c=fe.aggr.isContainer) walkCond(c.e,cond,dg);
		walkCond(fe.bdy,true,dg);
		return;
	}
	if(cast(WhileExp)e||cast(RepeatExp)e){
		foreach(c;e.components) walkCond(c,true,dg);
		return;
	}
	if(auto le=cast(ALogicExp)e){
		walkCond(le.e1,cond,dg);
		walkCond(le.e2,true,dg);
		return;
	}
	foreach(c;e.components) walkCond(c,cond,dg);
}
private void walkShallow(Expression e,scope void delegate(Expression) dg){
	if(!e) return;
	dg(e);
	if(cast(FunctionDef)e||cast(LambdaExp)e) return;
	if(auto tae=cast(TypeAnnotationExp)e){
		walkShallow(tae.e,dg);
		return;
	}
	if(auto ce=cast(CallExp)e) if(ce.isSquare){
		walkShallow(ce.e,dg);
		return;
	}
	if(auto fe=cast(ForExp)e){
		if(auto r=fe.aggr.isRange){
			walkShallow(r.left,dg);
			walkShallow(r.step,dg);
			walkShallow(r.right,dg);
		}else if(auto c=fe.aggr.isContainer) walkShallow(c.e,dg);
		walkShallow(fe.bdy,dg);
		return;
	}
	foreach(c;e.components) walkShallow(c,dg);
}
private Id varName(Identifier id){
	return id.meaning&&id.meaning.name?id.meaning.name.id:id.id;
}
private bool sameDeps(ref Dependency a,ref Dependency b){
	if(a.dependencies.length!=b.dependencies.length) return false;
	foreach(x;a.dependencies) if(x !in b.dependencies) return false;
	return true;
}

Expression splitLoop(T)(T loop,ref FixedPointIterState state,Scope sc,ref StmFlags flags){
	static if(is(T==ForExp)){
		auto range=loop.aggr.isRange;
		if(!range||!loop.loopVar) return null;
	}
	if(loop.noSplit) return null;
	enum NONE=-3,LSH=-2,SHARED=-1;
	auto carried=state.prevStateSnapshot.loopParams(loop.bdy.blscope_,null,false,null);
	if(!carried[0].length) return null;
	Dependency[] classDeps;
	int[] classOf;
	foreach(p;carried[0]){
		auto dep=state.prevStateSnapshot.dependencyOf(p[1]);
		if(dep.isTop) return null;
		int c=-1;
		foreach(j,ref d;classDeps) if(sameDeps(d,dep)){ c=cast(int)j; break; }
		if(c==-1){
			c=cast(int)classDeps.length;
			classDeps~=dep;
		}
		classOf~=c;
	}
	auto late=new bool[](classDeps.length);
	auto rank=new int[](classDeps.length);
	int P;
	void setupRanks(){
		auto order=iota(cast(int)classDeps.length).array;
		order.sort!((a,b)=>late[a]<late[b]||late[a]==late[b]&&classDeps[a].dependencies.length<classDeps[b].dependencies.length,SwapStrategy.stable);
		P=cast(int)late.count!(x=>!x);
		foreach(r,c;order) rank[c]=cast(int)(late[c]?r+1:r);
	}
	setupRanks();
	MapX!(Id,int) color;
	SetX!Id isCarried;
	MapX!(Id,Expression) carriedType;
	SetX!Id classical;
	foreach(p;carried[0]~carried[1]){
		auto ty=typeForDecl(p[1]);
		isCarried.insert(p[1].name.id);
		carriedType[p[1].name.id]=ty;
		if(ty.isClassical()) classical.insert(p[1].name.id);
	}
	struct StmInfo{
		SetX!Id defs,uses,nonConst,consumed,strong;
		MapX!(Id,Expression) types;
		bool nonQfree=false,isForget=false,effects=false;
	}
	Id[const(void)*] extracted;
	bool[const(void)*] reanalyze,isExtractAtom;
	StmInfo analyzeStm(Expression s,out bool bad){
		StmInfo info;
		info.isForget=!!cast(ForgetExp)s;
		SetX!Identifier targets;
		void strongDef(Id n){
			info.defs.insert(n);
			info.strong.insert(n);
		}
		void addDefs(Expression lhs){
			visitStm(lhs,(Expression x){
				if(auto ie=cast(IndexExp)x){
					Expression r=ie;
					while(cast(IndexExp)r) r=(cast(IndexExp)r).e;
					if(auto id=cast(Identifier)r) strongDef(varName(id));
				}else if(auto id=cast(Identifier)x) if(!id.constLookup){
					strongDef(varName(id));
					targets.insert(id);
					if(id.type) info.types[varName(id)]=id.type;
				}
			});
		}
		visitStmSkip(s,(Expression x){
			if(auto f=cast(const(void)*)x in extracted){
				info.uses.insert(*f);
				if(x.type) info.types[*f]=x.type;
				return false;
			}
			if(cast(ReturnExp)x){
				// Loops with early returns are not split: a separate loop computing lifted state would also run the
				// iterations after the return, which may fail or diverge where the original program does not.
				bad=true;
				return false;
			}
			if(auto fd=cast(FunctionDef)x) if(fd.name) strongDef(fd.name.id);
			if(cast(AssertExp)x) info.effects=true;
			if(auto de=cast(DefineExp)x) addDefs(de.e1);
			else if(auto we=cast(WithExp)x){
				visitStm(we.trans,(Expression y){
					if(auto id=cast(Identifier)y)
						if(id.type&&!id.type.isClassical())
							strongDef(varName(id));
				});
			}else if(auto ae=cast(AAssignExp)x){
				Expression lhs=ae.e1;
				while(cast(IndexExp)lhs) lhs=(cast(IndexExp)lhs).e;
				if(auto id=cast(Identifier)lhs) strongDef(varName(id));
				else addDefs(ae.e1);
			}else if(auto ce=cast(CallExp)x){
				if(auto ft=cast(FunTy)ce.e.type)
					if(!ft.isSquare&&ft.annotation<Annotation.qfree) info.nonQfree=true;
			}else if(auto id=cast(Identifier)x){
				if(id in targets||cast(DatDecl)id.meaning) return true;
				auto n=varName(id);
				info.uses.insert(n);
				if(id.type) info.types[n]=id.type;
				if(!id.constLookup&&!id.implicitDup){
					info.nonConst.insert(n);
					if(id.type&&!id.type.isClassical()){
						info.consumed.insert(n);
						info.defs.insert(n);
					}
				}
			}
			return true;
		});
		return info;
	}
	Expression[] stms;
	StmInfo[] infos;
	bool bad=false;
	void addStm(Expression s){
		if(auto ce=cast(CompoundExp)s) if(!ce.blscope_){
			foreach(x;ce.s) addStm(x);
			return;
		}
		bool b=false;
		auto info=analyzeStm(s,b);
		bad|=b;
		stms~=s;
		infos~=info;
	}
	foreach(s;loop.bdy.s) addStm(s);
	if(bad) return null;
	MapX!(Id,size_t) occurrences(Expression[] ss){
		MapX!(Id,size_t) r;
		foreach(s;ss) walkCond(s,false,(Expression x,bool c){
			if(auto id=cast(Identifier)x) r[varName(id)]=r.get(varName(id),0)+1;
		});
		return r;
	}
	auto totalOcc=occurrences(stms);
	Expression[const(void)*] replacedBy;
	StmInfo[const(void)*] synthInfo;
	void dce(ref Expression[] stms,ref StmInfo[] infos,scope bool delegate(Id) liveAtEnd){
		struct Ver{ Id var; int stm; }
		Ver[] vers;
		MapX!(Id,int) cur;
		int[][] usedBy;
		MapX!(Id,int)[] useVer, defVer;
		int getCur(Id n){
			if(n !in cur){
				cur[n]=cast(int)vers.length;
				vers~=Ver(n,-1);
				usedBy~=null;
			}
			return cur[n];
		}
		foreach(i,ref info;infos){
			MapX!(Id,int) uv,dv;
			foreach(u;info.uses){
				auto v=getCur(u);
				uv[u]=v;
				usedBy[v]~=cast(int)i;
			}
			foreach(d;info.defs){
				cur[d]=cast(int)vers.length;
				dv[d]=cast(int)vers.length;
				vers~=Ver(d,cast(int)i);
				usedBy~=null;
			}
			useVer~=uv;
			defVer~=dv;
		}
		auto liveOut=new bool[](vers.length);
		foreach(n,v;cur) if(liveAtEnd(n)) liveOut[v]=true;
		auto dead=new bool[](infos.length);
		foreach(i,ref info;infos) dead[i]=!info.isForget&&!info.nonQfree&&!info.effects&&info.defs.length;
		bool defDead(int v){ return vers[v].stm>=0&&dead[vers[v].stm]; }
		for(bool changed=true;changed;){
			changed=false;
			foreach(i,ref info;infos){
				if(!dead[i]) continue;
				bool ok=true;
				foreach(d,v;defVer[i]){
					if(liveOut[v]){ ok=false; break; }
					foreach(j;usedBy[v]){
						if(infos[j].isForget){
							foreach(u,w;useVer[j]) if(!defDead(w)) ok=false;
						}else if(!dead[j]) ok=false;
					}
				}
				if(!ok){
					dead[i]=false;
					changed=true;
				}
			}
		}
		if(dead.any){
			Expression[] nstms;
			StmInfo[] ninfos;
			foreach(i,s;stms){
				if(infos[i].isForget){
					if(useVer[i].byValue.any!(w=>defDead(w))) continue;
				}else if(dead[i]){
					foreach(u;infos[i].consumed){
						auto w=useVer[i][u];
						if(defDead(w)||vers[w].stm<0&&!liveAtEnd(u)) continue;
						auto fid=new Identifier(u);
						fid.loc=s.loc;
						auto fe=new ForgetExp(fid,null);
						fe.loc=s.loc;
						StmInfo fi;
						fi.isForget=true;
						fi.defs.insert(u);
						fi.uses.insert(u);
						fi.nonConst.insert(u);
						fi.consumed.insert(u);
						if(auto t=infos[i].types.get(u,null)) fi.types[u]=t;
						nstms~=fe;
						ninfos~=fi;
						replacedBy[cast(const(void)*)fe]=s;
						synthInfo[cast(const(void)*)fe]=fi;
					}
					continue;
				}
				nstms~=s;
				ninfos~=infos[i];
			}
			stms=nstms;
			infos=ninfos;
		}
	}
	dce(stms,infos,(Id n)=>!!(n in isCarried));
	Expression[] blockStms(Expression[] ss,bool isLoopBody){
		Expression[] list;
		StmInfo[] linfos;
		void add(Expression s){
			if(auto ce=cast(CompoundExp)s) if(!ce.blscope_){
				foreach(x;ce.s) add(x);
				return;
			}
			bool b=false;
			linfos~=analyzeStm(s,b);
			bad|=b;
			list~=s;
		}
		foreach(s;ss) add(s);
		auto occ=occurrences(list);
		SetX!Id early;
		if(isLoopBody){
			SetX!Id defined;
			foreach(ref inf;linfos){
				foreach(u;inf.uses) if(u !in defined) early.insert(u);
				foreach(d;inf.defs) defined.insert(d);
			}
		}
		dce(list,linfos,(Id n)=>n in isCarried||n in early||totalOcc.get(n,0)>occ.get(n,0));
		return list;
	}
	struct Atom{
		Expression e;
		size_t stm;
		size_t[] ites;
		bool[] inElse;
		Expression[] parts;
	}
	struct Ite{
		Expression e;
		size_t stm;
		StmInfo info;
		size_t[] ctx;
		size_t first;
		bool isLoop;
		Expression[] heads;
		bool isWith;
		size_t pseudo;
	}
	Atom[] atoms;
	Ite[] ites;
	bool splitTuple(DefineExp de){
		auto lhs=cast(TupleExp)de.e1, rhs=cast(TupleExp)de.e2;
		if(de.isSwap||!lhs||!rhs||lhs.e.length!=rhs.e.length||lhs.e.length<2) return false;
		Id[] roots;
		foreach(l;lhs.e){
			Expression r=l;
			while(cast(IndexExp)r) r=(cast(IndexExp)r).e;
			auto id=cast(Identifier)r;
			if(!id) return false;
			auto n=varName(id);
			if(roots.canFind(n)) return false;
			roots~=n;
		}
		foreach(k;0..lhs.e.length){
			bool ok=true;
			void check(Expression e){
				visitStm(e,(Expression x){
					if(auto id=cast(Identifier)x){
						auto n=varName(id);
						foreach(j,r;roots) if(j!=k&&r==n) ok=false;
					}
				});
			}
			check(lhs.e[k]);
			check(rhs.e[k]);
			if(!ok) return false;
		}
		return true;
	}
	void extractFrom(Expression root,size_t i,size_t[] ctx,bool[] inElse){
		bool rb=false;
		auto rootInfo=analyzeStm(root,rb);
		// within a single simple statement, subexpressions are evaluated before any variable is updated
		bool simple=true;
		walkShallow(root,(Expression x){
			if(cast(CompoundExp)x||cast(IteExp)x||cast(ForExp)x||cast(WhileExp)x||cast(RepeatExp)x||cast(WithExp)x) simple=false;
		});
		SetX!Expression covered;
		walkShallow(root,(Expression x){
			if(x in covered) return;
			auto ce=cast(CallExp)x;
			if(!ce||!ce.type||!ce.type.isClassical()) return;
			auto ft=cast(FunTy)ce.e.type;
			if(!ft||ft.isSquare||ft.annotation>=Annotation.qfree) return;
			bool ok=true;
			walkShallow(ce,(Expression y){
				covered.insert(y);
				if(auto id=cast(Identifier)y) if(id.type&&!id.type.isClassical()&&!cast(FunctionDef)id.meaning){
					if(!simple&&(id.constLookup||id.implicitDup)&&varName(id) in rootInfo.defs) ok=false;
				}
				if(cast(LambdaExp)y||cast(FunctionDef)y) ok=false;
			});
			if(!ok) return;
			auto fresh=freshName();
			auto fid=new Identifier(fresh);
			fid.loc=ce.loc;
			fid.constLookup=false;
			auto w=new DefineExp(fid,ce);
			w.loc=ce.loc;
			bool b2=false;
			auto wi=analyzeStm(w,b2);
			wi.types[fresh]=ce.type;
			synthInfo[cast(const(void)*)w]=wi;
			extracted[cast(const(void)*)ce]=fresh;
			reanalyze[cast(const(void)*)root]=true;
			isExtractAtom[cast(const(void)*)w]=true;
			atoms~=Atom(w,i,ctx,inElse,[ce]);
		});
	}
	bool[size_t] isPseudo;
	Id[size_t] condVars;
	SetX!Id isCondVar;
	Id condVar(size_t k){
		if(auto r=k in condVars) return *r;
		auto n=freshName();
		condVars[k]=n;
		isCondVar.insert(n);
		return n;
	}
	void flatten(Expression e,size_t i,size_t[] ctx,bool[] inElse){
		if(auto ite=cast(IteExp)e){
			bool b=false;
			auto info=analyzeStm(ite.cond,b);
			bad|=b;
			if(info.nonQfree&&ite.cond.type&&ite.cond.type.isClassical()){
				extractFrom(ite.cond,i,ctx,inElse);
				info=analyzeStm(ite.cond,b);
			}
			if(!info.strong.length){
				foreach(u;info.consumed){
					info.defs.remove(u);
					info.nonConst.remove(u);
				}
				info.consumed=typeof(info.consumed).init;
			}
			if(!info.defs.length){
				auto k=ites.length;
				ites~=Ite(ite,i,info,ctx,atoms.length,false,[ite.cond]);
				auto before=atoms.length;
				foreach(x;blockStms(ite.then.s,false)) flatten(x,i,ctx~k,inElse~false);
				if(ite.othw) foreach(x;blockStms(ite.othw.s,false)) flatten(x,i,ctx~k,inElse~true);
				if(atoms.length!=before) return;
				ites=ites[0..k];
			}
		}
		if(auto we=cast(WithExp)e) if(!we.isIndices){
			auto k=ites.length;
			auto p=atoms.length;
			atoms~=Atom(we.trans,i,ctx,inElse,[we.trans]);
			auto it=Ite(we,i,StmInfo.init,ctx,p,false,[]);
			it.isWith=true;
			it.pseudo=p;
			ites~=it;
			foreach(x;blockStms(we.bdy.s,false)) flatten(x,i,ctx~k,inElse~false);
			if(atoms.length!=p+1){
				isPseudo[p]=true;
				return;
			}
			ites=ites[0..k];
			atoms=atoms[0..p];
		}
		Expression[] heads;
		CompoundExp lbdy;
		if(auto fe=cast(ForExp)e){
			if(auto r=fe.aggr.isRange) if(fe.loopVar){
				heads=[r.left]~(r.step?[r.step]:[])~[r.right];
				lbdy=fe.bdy;
			}
		}else if(auto re=cast(RepeatExp)e){
			heads=[re.num];
			lbdy=re.bdy;
		}else if(auto we=cast(WhileExp)e){
			heads=[we.cond];
			lbdy=we.bdy;
		}
		if(lbdy){
			StmInfo info;
			if(!cast(WhileExp)e) foreach(h;heads){
				bool b=false;
				auto hi=analyzeStm(h,b);
				if(hi.nonQfree&&h.type&&h.type.isClassical()) extractFrom(h,i,ctx,inElse);
			}
			foreach(h;heads){
				bool b=false;
				auto hi=analyzeStm(h,b);
				bad|=b;
				foreach(u;hi.uses) info.uses.insert(u);
				foreach(u;hi.defs) info.defs.insert(u);
				foreach(u;hi.nonConst) info.nonConst.insert(u);
				foreach(u,t;hi.types) info.types[u]=t;
				info.nonQfree|=hi.nonQfree;
				info.effects|=hi.effects;
			}
			if(!info.defs.length){
				auto k=ites.length;
				ites~=Ite(e,i,info,ctx,atoms.length,true,heads);
				auto before=atoms.length;
				foreach(x;blockStms(lbdy.s,true)) flatten(x,i,ctx~k,inElse~false);
				if(atoms.length!=before) return;
				ites=ites[0..k];
			}
		}
		if(auto ce=cast(CompoundExp)e) if(!ce.blscope_){
			foreach(x;ce.s) flatten(x,i,ctx,inElse);
			return;
		}
		if(auto de=cast(DefineExp)e) if(splitTuple(de)){
			auto lhs=cast(TupleExp)de.e1, rhs=cast(TupleExp)de.e2;
			foreach(k;0..lhs.e.length){
				auto w=new DefineExp(lhs.e[k],rhs.e[k]);
				w.loc=de.loc;
				atoms~=Atom(w,i,ctx,inElse,[lhs.e[k],rhs.e[k]]);
			}
			return;
		}
		{
			bool b=false;
			auto inf=analyzeStm(e,b);
			bool qdef=false;
			foreach(d;inf.defs){
				if(d in isCarried&&d !in classical) qdef=true;
				if(auto t=inf.types.get(d,null)) if(!t.isClassical()) qdef=true;
			}
			if(inf.nonQfree&&qdef){
				extractFrom(e,i,ctx,inElse);
			}
		}
		atoms~=Atom(e,i,ctx,inElse,[e]);
	}
	foreach(i,s;stms) flatten(s,i,[],[]);
	if(bad) return null;
	StmInfo[] ainfos;
	foreach(ref a;atoms){
		bool b=false;
		auto info=a.e is stms[a.stm]&&cast(const(void)*)a.e !in reanalyze?infos[a.stm]:cast(const(void)*)a.e in synthInfo?synthInfo[cast(const(void)*)a.e]:analyzeStm(a.e,b);
		if(b) return null;
		foreach(k;a.ites){
			auto ci=&ites[k].info;
			foreach(u;ci.uses) info.uses.insert(u);
			foreach(u;ci.nonConst) info.nonConst.insert(u);
			foreach(u,t;ci.types) info.types[u]=t;
			if(ci.nonQfree) info.uses.insert(condVar(k));
			info.effects|=ci.effects;
		}
		ainfos~=info;
	}
	bool quantumIte(size_t j){
		if(ites[j].isLoop||ites[j].isWith) return false;
		auto c=ites[j].heads[0];
		return !(c.type&&c.type.isClassical());
	}
	void refreshCtl(){
		foreach(k,ref it;ites){
			size_t f=size_t.max;
			foreach(ai,ref at;atoms) if(at.ites.canFind(k)){
				f=ai;
				break;
			}
			if(f==size_t.max) continue;
			if(!it.isWith) it.first=f;
			auto c=atoms[f].ites;
			auto x=c.countUntil(k);
			if(x>=0) it.ctx=c[0..x];
		}
	}
	bool hoistLocal(size_t q,Id t){
		if(t in isCarried) return false;
		size_t occ=0;
		walkCond(ites[q].e,false,(Expression x,bool c){
			if(auto id=cast(Identifier)x) if(varName(id)==t) occ++;
		});
		if(occ!=totalOcc.get(t,0)) return false;
		size_t[] defs;
		foreach(ai,ref at;atoms) if(at.ites.canFind(q)&&t in ainfos[ai].defs) defs~=ai;
		if(!defs.length) return false;
		foreach(ai;defs){
			auto inf=&ainfos[ai];
			if(inf.nonQfree||inf.effects||ai in isPseudo) return false;
			foreach(d;inf.defs) if(d!=t) return false;
			foreach(u;inf.uses){
				if(u==t||u in isCarried) continue;
				foreach(bj,ref b;atoms) if(b.ites.canFind(q)&&u in ainfos[bj].defs) return false;
			}
		}
		foreach(ai;defs){
			auto c=atoms[ai].ites;
			auto x=c.countUntil(q);
			size_t[] nc;
			bool[] ne;
			foreach(y,k;c){
				if(y>=x&&quantumIte(k)) continue;
				nc~=k;
				ne~=atoms[ai].inElse[y];
			}
			atoms[ai].ites=nc;
			atoms[ai].inElse=ne;
		}
		return true;
	}
	foreach(q,ref qt;ites){
		if(!quantumIte(q)) continue;
		SetX!Id need;
		foreach(ai,ref at;atoms){
			auto x=at.ites.countUntil(q);
			if(x<0||!at.ites[x+1..$].any!(k=>ites[k].isLoop)) continue;
			foreach(u;ainfos[ai].uses) need.insert(u);
		}
		foreach(k,ref it;ites) if(it.isLoop&&it.ctx.canFind(q)) foreach(u;it.info.uses) need.insert(u);
		foreach(t;need) hoistLocal(q,t);
	}
	refreshCtl();
	foreach(ai,ref a;atoms){
		for(;;){
			auto c=a.ites;
			size_t qi=size_t.max,li=size_t.max;
			foreach(x,k;c) if(quantumIte(k)){
				foreach(y;x+1..c.length) if(ites[c[y]].isLoop) li=y;
				if(li!=size_t.max){
					qi=x;
					break;
				}
			}
			if(qi==size_t.max) break;
			size_t[] cls,qs;
			bool[] clsE,qsE;
			foreach(x;qi..li+1){
				if(quantumIte(c[x])){
					qs~=c[x];
					qsE~=a.inElse[x];
				}else{
					cls~=c[x];
					clsE~=a.inElse[x];
				}
			}
			bool ok=!cls.any!(m=>ites[m].isWith);
			foreach(m;cls) foreach(u;ites[m].info.uses){
				if(u in isCarried) continue;
				foreach(bj,ref b;atoms){
					if(bj>=ites[m].first) break;
					if(u in ainfos[bj].defs&&qs.any!(q=>b.ites.canFind(q))) ok=false;
				}
			}
			if(!ok) break;
			a.ites=c[0..qi]~cls~qs~c[li+1..$];
			a.inElse=a.inElse[0..qi]~clsE~qsE~a.inElse[li+1..$];
		}
	}
	refreshCtl();
	int colorOf(Id n){ return color.get(n,NONE); }
	bool isClassicalName(Id n,ref StmInfo info){
		if(n in classical||n in isCondVar) return true;
		if(auto t=info.types.get(n,null)) return t.isClassical();
		return false;
	}
	int reads2(ref StmInfo info,out bool lateRead){
		int c=info.nonQfree?P:NONE;
		bool qdefs=!info.nonQfree&&info.defs.length;
		foreach(d;info.defs) if(isClassicalName(d,info)) qdefs=false;
		void add(Id u){
			auto x=colorOf(u);
			if(info.nonQfree&&x>P) return; // computed within F
			if(x==LSH||x==P&&qdefs&&isClassicalName(u,info)){
				lateRead=true;
				return;
			}
			c=max(c,x);
		}
		foreach(u;info.uses) add(u);
		foreach(d;info.defs) add(d);
		return c;
	}
	int reads(ref StmInfo info){
		bool lr;
		return reads2(info,lr);
	}
	bool native(int c,int Y){
		return c==NONE||c==Y||c==LSH&&Y>=P||Y==P&&c>P;
	}
	int[] atomColor;
	int[] lateReq;
	bool colorAtoms(bool lower,bool weakRaise){
		color=typeof(color).init;
		foreach(i,p;carried[0]) color[p[1].name.id]=rank[classOf[i]];
		foreach(p;carried[1]) color[p[1].name.id]=lower&&p[1].name.id in classical?0:P;
		foreach(n;isCondVar) color[n]=P;
		foreach(ref info;ainfos) foreach(d;info.defs) if(d !in color) color[d]=NONE;
		bool fixed(Id d){ return d in isCarried&&!(lower&&d in classical); }
		for(bool changed=true;changed;){
			changed=false;
			foreach(ref info;ainfos){
				bool lr;
				auto c=reads2(info,lr);
				if(c==NONE&&lr) c=LSH;
				foreach(d;info.defs){
					if(fixed(d)||colorOf(d)>=c) continue;
					if(!weakRaise&&d in info.consumed&&d !in info.strong) continue;
					color[d]=c;
					changed=true;
				}
			}
		}
		atomColor=[];
		foreach(ref info;ainfos){
			if(info.defs.length==0){
				atomColor~=P;
				continue;
			}
			int dc=NONE;
			bool skipped=false;
			foreach(d;info.defs){
				if(d in info.consumed&&d !in info.strong&&(d in isCarried||!weakRaise)){
					skipped=true;
					continue;
				}
				auto x=colorOf(d);
				if(dc!=NONE&&x!=dc) return false;
				dc=x;
			}
			if(dc==NONE&&skipped) dc=reads(info);
			if(dc==NONE){
				atomColor~=SHARED;
				continue;
			}
			bool lr;
			auto r=reads2(info,lr);
			if(dc==LSH){
				if(r>=0) return false;
				atomColor~=LSH;
				continue;
			}
			if(dc>=0&&dc<P&&(lr||r>P)){
				foreach(i,p;carried[0]) if(rank[classOf[i]]==dc) lateReq~=classOf[i];
				return false;
			}
			if(r>dc&&dc!=P) return false;
			atomColor~=dc;
		}
		return true;
	}
	bool lateAll=false;
	bool guardOK(){
		static if(is(T==WhileExp)){
			if(!loop.cond.type||!loop.cond.type.isClassical()) return false;
			bool ok=true;
			visitStm(loop.cond,(Expression x){
				if(auto ce=cast(CallExp)x){
					if(auto ft=cast(FunTy)ce.e.type)
						if(!ft.isSquare&&ft.annotation<Annotation.qfree&&P>0) ok=false;
				}else if(auto id=cast(Identifier)x){
					if(cast(DatDecl)id.meaning) return;
					auto c=colorOf(varName(id));
					if(c==P&&P>0) lateAll=true;
					if(c!=NONE&&c!=0) ok=false;
				}
			});
			if(!ok&&P>0){
				bool nq=false;
				visitStm(loop.cond,(Expression x){
					if(auto ce=cast(CallExp)x)
						if(auto ft=cast(FunTy)ce.e.type)
							if(!ft.isSquare&&ft.annotation<Annotation.qfree) nq=true;
				});
				if(nq) lateAll=true;
			}
			return ok;
		}else return true;
	}
	for(;;){
		lateReq=[];
		lateAll=false;
		if(colorAtoms(false,true)&&guardOK()||colorAtoms(true,true)&&guardOK()||colorAtoms(false,false)&&guardOK()||colorAtoms(true,false)&&guardOK()) break;
		bool progress=false;
		if(lateAll) foreach(ref x;late) if(!x){ x=true; progress=true; }
		foreach(c;lateReq) if(!late[c]){ late[c]=true; progress=true; }
		if(!progress) return null;
		setupRanks();
	}
	if((atomColor.filter!(c=>c>=0).array~(atomColor.any!(c=>c>P)?[P]:[])).sort.uniq.walkLength<2) return null;
	{
		bool changed=false;
		foreach(q,ref qt;ites){
			if(!quantumIte(q)) continue;
			SetX!Id need;
			foreach(ai,ref at;atoms){
				if(!at.ites.canFind(q)||atomColor[ai]<0) continue;
				foreach(u;ainfos[ai].uses){
					auto cu=colorOf(u);
					if(cu>=0&&cu!=atomColor[ai]) need.insert(u);
				}
			}
			foreach(t;need) changed|=hoistLocal(q,t);
		}
		if(changed) refreshCtl();
	}
	bool inX(size_t a,int X){ return atomColor[a]==X||X==P&&atomColor[a]>P||atomColor[a]==LSH&&X>=P; }
	bool keepAtom(size_t a,int X){ return inX(a,X)||atomColor[a]==SHARED; }
	foreach(k,ref it;ites) if(it.isWith){
		auto owner=atomColor[it.pseudo];
		auto ti=&ainfos[it.pseudo];
		foreach(a,ref at;atoms){
			if(!at.ites.canFind(k)||atomColor[a]==owner||owner==SHARED) continue;
			foreach(u;ainfos[a].uses) if(u in ti.defs&&u !in ti.strong) return null;
		}
	}
	bool iteHas(size_t k,int X){
		foreach(a,ref at;atoms) if(at.ites.canFind(k)&&inX(a,X)) return true;
		return false;
	}
	struct Log{
		Id var;
		size_t stm;
		int src,dst;
		Id name,tmp,ctr;
		Expression type;
		IndexExp access;
		size_t node;
		Expression bound;
		size_t wAt,rAt,level;
		size_t[] rnodes;
		bool primary=true;
		size_t ite=size_t.max;
		bool consume;
		size_t rLevel=size_t.max;
		Id slot;
		size_t count=size_t.max;
		Id cntVar;
		bool viaDummy;
		bool alias_;
	}
	Log[] logs;
	void addLog(Log l){
		if(l.rLevel==size_t.max) l.rLevel=l.level;
		if(!l.access&&l.slot==Id.init&&!l.consume&&l.rLevel==0&&l.count==size_t.max&&l.ite==size_t.max&&l.var!=Id.init&&l.type&&l.type.isClassical()){
			foreach_reverse(ref o;logs){
				if(o.alias_||o.var!=l.var||o.src!=l.src||o.dst!=l.dst||o.access||o.slot!=Id.init||o.rLevel!=0||o.count!=size_t.max||o.ite!=size_t.max||o.rAt>l.rAt) continue;
				bool redefined=false;
				foreach(a;o.rAt..l.rAt) if(l.var in ainfos[a].defs) redefined=true;
				if(redefined) break;
				l.tmp=o.tmp;
				l.alias_=true;
				l.primary=false;
				logs~=l;
				return;
			}
		}
		foreach(ref o;logs) if(o.primary&&o.var==l.var&&o.stm==l.stm&&o.wAt==l.wAt&&o.level==l.level&&!!o.access==!!l.access&&(!l.access||o.node==l.node)&&o.ite==l.ite&&o.count==l.count){
			l.name=o.name;
			l.primary=false;
			break;
		}
		if(l.rLevel==size_t.max) l.rLevel=l.level;
		if(l.rLevel) l.ctr=freshName();
		logs~=l;
	}
	bool available(Expression e){
		bool ok=true;
		visitStm(e,(Expression x){
			if(auto ce=cast(CallExp)x){
				if(auto ft=cast(FunTy)ce.e.type)
					if(!ft.isSquare&&ft.annotation<Annotation.qfree) ok=false;
			}else if(auto id=cast(Identifier)x){
				if(cast(DatDecl)id.meaning) return;
				if(colorOf(varName(id))!=NONE) ok=false;
				if(!id.constLookup&&!id.implicitDup&&id.type&&!id.type.isClassical()) ok=false;
			}
		});
		return ok;
	}
	bool isClassicalIte(size_t j){
		if(ites[j].isLoop||ites[j].isWith) return true;
		auto c=ites[j].heads[0];
		return c.type&&c.type.isClassical();
	}
	bool headsOK(size_t j,int Y,bool upTo){
		bool ok=true;
		foreach(h;ites[j].heads) visitStm(h,(Expression x){
			if(auto ce=cast(CallExp)x){
				if(auto ft=cast(FunTy)ce.e.type)
					if(!ft.isSquare&&ft.annotation<Annotation.qfree&&Y!=P) ok=false;
			}else if(auto id=cast(Identifier)x){
				if(cast(DatDecl)id.meaning) return;
				auto c=colorOf(varName(id));
				if(!native(c,Y)&&(!upTo||c>Y)) ok=false;
			}
		});
		return ok;
	}
	bool condOK(size_t j,int Y){
		if(!isClassicalIte(j)) return false;
		return headsOK(j,Y,false);
	}
	bool evalBy(size_t j,int Y){
		return headsOK(j,Y,false);
	}
	bool usable(size_t j,int Y){
		if(condOK(j,Y)) return true;
		if(!isClassicalIte(j)||!iteHas(j,Y)) return false;
		if(cast(WhileExp)ites[j].e) return false;
		foreach(h;ites[j].heads) if(ites[j].info.nonQfree) return false;
		return headsOK(j,Y,true);
	}
	int bitSource(size_t j,int Y){
		if(ites[j].isLoop||ites[j].isWith||!isClassicalIte(j)) return NONE;
		int Z=NONE;
		bool ok=true;
		visitStm(ites[j].heads[0],(Expression x){
			if(auto id=cast(Identifier)x){
				if(cast(DatDecl)id.meaning) return;
				auto c=colorOf(varName(id));
				if(c==NONE) return;
				if(Z!=NONE&&c!=Z) ok=false;
				Z=c;
			}
		});
		if(ites[j].info.nonQfree){
			if(Z!=NONE&&Z!=P) ok=false;
			Z=P;
		}
		if(!ok||Z==NONE||Z>=Y||!condOK(j,Z)) return NONE;
		return Z;
	}
	SetX!Id definedBefore;
	foreach(i,s;stms){
		scope(exit) foreach(ai,ref a;atoms) if(a.stm==i) foreach(d;ainfos[ai].defs) definedBefore.insert(d);
		Expression[] nodes;
		bool[] conds;
		walkCond(s,false,(Expression x,bool c){ nodes~=x; conds~=c; });
		size_t[const(void)*] pos;
		foreach(n,x;nodes) pos[cast(const(void)*)x]=n;
		auto owner=new int[](nodes.length), condOf=new int[](nodes.length);
		owner[]=-1;
		condOf[]=-1;
		MapX!(Id,size_t[]) defPos;
		foreach(ai,ref a;atoms) if(a.stm==i){
			if(cast(const(void)*)a.e !in isExtractAtom) foreach(part;a.parts)
				walkCond(part,false,(Expression x,bool c){
					if(auto p=cast(const(void)*)x in pos) owner[*p]=cast(int)ai;
				});
			auto key=cast(const(void)*)a.parts[0];
			if(key !in pos) key=cast(const(void)*)replacedBy[key];
			auto start=pos[key];
			foreach(d;ainfos[ai].defs) defPos[d]=defPos.get(d,[])~start;
		}
		foreach(k,ref it;ites) if(it.stm==i)
			foreach(h;it.heads)
				walkCond(h,false,(Expression x,bool c){
					if(auto p=cast(const(void)*)x in pos) condOf[*p]=cast(int)k;
				});
		size_t endOf(size_t j){
			size_t cnt=0;
			walkCond(ites[j].e,false,(Expression x,bool c){ cnt++; });
			return pos[cast(const(void)*)ites[j].e]+cnt;
		}
		size_t[2][] needBits;
		bool place(size_t n,int Y,scope bool delegate(size_t,size_t) inside,out size_t level,out size_t wAt,out size_t rAt,out size_t rLevel,out bool slot){
			size_t[] chain;
			size_t at;
			if(owner[n]>=0){
				chain=atoms[owner[n]].ites;
				at=owner[n];
			}else{
				chain=ites[condOf[n]].ctx;
				at=ites[condOf[n]].first;
			}
			level=rLevel=chain.length;
			wAt=rAt=at;
			slot=false;
			size_t regionStart(size_t dd){
				size_t b=at;
				bool same(size_t x){
					auto c=atoms[x].ites;
					return atoms[x].stm==i&&c.length>dd&&c[0..dd+1]==chain[0..dd+1];
				}
				while(b>0&&same(b-1)) b--;
				return b;
			}
			size_t[2][] bits;
			foreach(dd,j;chain){
				bool q=!isClassicalIte(j);
				if(!q&&usable(j,Y)) continue;
				if(!q&&bitSource(j,Y)!=NONE){
					bits~=[j,cast(size_t)Y];
					continue;
				}
				bool loopBelow=chain[dd..$].any!(k=>ites[k].isLoop);
				bool ins=inside(pos[cast(const(void)*)ites[j].e],loopBelow?endOf(j):n);
				if(ins&&(!q||loopBelow)) return false;
				rLevel=dd;
				rAt=regionStart(dd);
				if(!ins){
					level=dd;
					wAt=rAt;
					break;
				}
				slot=true;
				foreach(d2;dd..chain.length){
					auto k=chain[d2];
					if(evalBy(k,Y)||isClassicalIte(k)&&bitSource(k,Y)!=NONE) continue;
					if(inside(pos[cast(const(void)*)ites[k].e],n)) return false;
					level=d2;
					wAt=regionStart(d2);
					break;
				}
				foreach(d2;dd..level) if(isClassicalIte(chain[d2])&&!condOK(chain[d2],Y)) bits~=[chain[d2],cast(size_t)Y];
				break;
			}
			needBits~=bits;
			return true;
		}
		int[] xs=atoms.enumerate.filter!(a=>a.value.stm==i).map!(a=>atomColor[a.index]).filter!(c=>c>=0).array;
		if(xs.any!(c=>c>P)||atoms.enumerate.any!(a=>a.value.stm==i&&atomColor[a.index]==LSH)) xs~=P;
		foreach(c;P+1..cast(int)classDeps.length+1) if(atoms.enumerate.any!(a=>a.value.stm==i&&atomColor[a.index]==LSH)) xs~=c;
		xs=xs.sort.uniq.array;
		foreach(X;xs){
			SetX!Expression condCovered;
			foreach(k,ref it;ites){
				auto we=cast(WhileExp)it.e;
				if(it.stm!=i||!we||!iteHas(k,X)) continue;
				int Y=NONE;
				bool ok=true;
				Id[] vars;
				visitStm(we.cond,(Expression x){
					if(auto id=cast(Identifier)x){
						if(cast(DatDecl)id.meaning) return;
						auto c=colorOf(varName(id));
						if(native(c,X)) return;
						if(Y!=NONE&&c!=Y) ok=false;
						Y=c;
						vars~=varName(id);
					}
				});
				if(it.info.nonQfree&&X!=P){
					if(Y!=NONE&&Y!=P) ok=false;
					Y=P;
				}
				if(Y==NONE) continue;
				if(!ok||Y>X||!condOK(k,Y)) return null;
				auto n=pos[cast(const(void)*)we.cond];
				size_t level,wAt,rAt,rLevel;
				bool slot;
				if(!place(n,Y,(size_t start,size_t end)=>vars.any!(v=>defPos.get(v,[]).any!(d=>start<=d&&d<end)),level,wAt,rAt,rLevel,slot)) return null;
				if(slot||level!=it.ctx.length||rLevel!=level) return null;
				auto l=Log(Id.init,i,Y,X,freshName(),freshName(),Id.init,ℕt(true),null,n,null,wAt,rAt,level);
				l.count=k;
				l.cntVar=freshName();
				addLog(l);
				visitStm(we.cond,(Expression x){ condCovered.insert(x); });
			}
			foreach(k,ref it;ites){
				if(it.stm!=i||it.isLoop||it.isWith||!iteHas(k,X)||!isClassicalIte(k)) continue;
				int Y=NONE;
				bool ok=true;
				Id[] vars;
				visitStm(it.heads[0],(Expression x){
					if(auto id=cast(Identifier)x){
						if(cast(DatDecl)id.meaning) return;
						auto c=colorOf(varName(id));
						if(native(c,X)) return;
						if(Y!=NONE&&c!=Y) ok=false;
						Y=c;
						vars~=varName(id);
					}
				});
				if(it.info.nonQfree&&X!=P){
					if(Y!=NONE&&Y!=P) ok=false;
					Y=P;
				}
				if(!ok||Y==NONE||Y>=X||!condOK(k,Y)) continue;
				auto n=pos[cast(const(void)*)it.heads[0]];
				size_t level,wAt,rAt,rLevel;
				bool slot;
				if(!place(n,Y,(size_t start,size_t end)=>vars.any!(v=>defPos.get(v,[]).any!(d=>start<=d&&d<end)),level,wAt,rAt,rLevel,slot)) continue;
				auto l=Log(Id.init,i,Y,X,freshName(),freshName(),Id.init,it.heads[0].type,null,n,null,wAt,rAt,level);
				l.ite=k;
				l.rLevel=rLevel;
				if(slot) l.slot=freshName();
				addLog(l);
				visitStm(it.heads[0],(Expression x){ condCovered.insert(x); });
			}
			bool inScope(size_t n){
				if(owner[n]>=0) return inX(owner[n],X);
				if(condOf[n]>=0) return iteHas(condOf[n],X);
				return false;
			}
			SetX!Id uses,nonConst,consumed;
			MapX!(Id,Expression) types;
			foreach(ai,ref a;atoms) if(a.stm==i&&inX(ai,X)){
				foreach(u;ainfos[ai].uses) uses.insert(u);
				foreach(u;ainfos[ai].nonConst) nonConst.insert(u);
				foreach(u;ainfos[ai].consumed) consumed.insert(u);
				foreach(u,t;ainfos[ai].types) types[u]=t;
			}
			foreach(u;uses){
				auto Y=colorOf(u);
				if(Y<0||native(Y,X)||u in isCondVar) continue;
				if(Y>X) return null;
				bool consume=!!(u in consumed);
				foreach(n,x;nodes) if(condOf[n]>=0&&cast(WhileExp)ites[condOf[n]].e&&inScope(n)&&x !in condCovered)
					if(auto id=cast(Identifier)x) if(varName(id)==u) return null;
				struct Group{
					size_t wAt,rAt,level,rLevel;
					bool slot;
					size_t[] reads;
					bool viaDummy;
				}
				Group[] groups;
				bool anchor(size_t n){
					size_t level,wAt,rAt,rLevel;
					bool slot;
					if(!place(n,Y,(size_t start,size_t end)=>defPos.get(u,[]).any!(d=>start<=d&&d<end),level,wAt,rAt,rLevel,slot)) return false;
					if(consume&&(slot||owner[n]<0||level!=atoms[owner[n]].ites.length||wAt!=owner[n])) return false;
					bool viaDummy=false;
					if(slot&&u !in isCarried){
						auto chain=owner[n]>=0?atoms[owner[n]].ites:ites[condOf[n]].ctx;
						auto qk=chain[rLevel];
						auto rd=owner[n]>=0?owner[n]:ites[condOf[n]].first;
						bool avail=!!(u in definedBefore);
						foreach(bj,ref b;atoms) if(bj<rd&&b.stm==i&&u in ainfos[bj].defs&&!b.ites.canFind(qk)) avail=true;
						if(!avail){
							auto ty=types.get(u,null);
							if(!ty||!isQuantum(ty)) return false;
							viaDummy=true;
						}
					}
					foreach(ref g;groups) if(g.wAt==wAt&&g.level==level&&g.rLevel==rLevel){
						g.reads~=n;
						g.viaDummy|=viaDummy;
						return true;
					}
					if(!slot&&!consume&&u in classical||!slot&&!consume&&types.get(u,null)&&types[u].isClassical()){
						auto at=owner[n]>=0?owner[n]:ites[condOf[n]].first;
						foreach(ref g;groups){
							if(g.slot||g.viaDummy) continue;
							auto c0=atoms[g.rAt].ites;
							if(g.rLevel>c0.length) continue;
							bool same=g.rAt<=at;
							foreach(b;g.rAt..at+1) if(same){
								auto cb=atoms[b].ites;
								if(atoms[b].stm!=i||cb.length<g.rLevel||cb[0..g.rLevel]!=c0[0..g.rLevel]) same=false;
							}
							if(!same) continue;
							auto first=g.reads[0];
							if(defPos.get(u,[]).any!(d=>first<=d&&d<n)) continue;
							g.reads~=n;
							return true;
						}
					}
					groups~=Group(wAt,rAt,level,rLevel,slot,[n],viaDummy);
					return true;
				}
				SetX!Expression covered;
				foreach(n,x;nodes){
					if(x in covered||x in condCovered||!inScope(n)) continue;
					if(auto f=cast(const(void)*)x in extracted){
						if(*f==u&&!anchor(n)) return null;
						continue;
					}
					if(auto id=cast(Identifier)x){
						if(varName(id)==u&&!anchor(n)) return null;
						continue;
					}
					auto ie=cast(IndexExp)x;
					if(!ie) continue;
					Expression r=ie;
					while(auto je=cast(IndexExp)r){
						covered.insert(je);
						r=je.e;
					}
					auto rid=cast(Identifier)r;
					if(!rid||varName(rid)!=u) continue;
					covered.insert(rid);
					if(!anchor(n)) return null;
				}
				foreach(ref g;groups){
					Log[] elems;
					size_t[] rnodes;
					bool whole=false;
					foreach(n;g.reads){
						if(cast(const(void)*)nodes[n] in extracted){
							rnodes~=n;
							whole=true;
							continue;
						}
						if(auto id=cast(Identifier)nodes[n]){
							rnodes~=n;
							whole=true;
							continue;
						}
						IndexExp[] chain;
						Expression r=nodes[n];
						while(auto je=cast(IndexExp)r){
							chain~=je;
							r=je.e;
						}
						rnodes~=pos[cast(const(void)*)r];
						if(consume){
							whole=true;
							continue;
						}
						IndexExp acc=null;
						foreach_reverse(c;chain){
							if(!available(c.a)||!c.type) break;
							acc=c;
						}
						if(!acc){
							whole=true;
							continue;
						}
						Expression bound=null;
						if(conds[n]&&g.slot||g.viaDummy){
							whole=true;
							continue;
						}
						if(conds[n]){
							if(acc!is chain[$-1]||!acc.a.type||!isSubtype(acc.a.type,ℤt(true))){
								whole=true;
								continue;
							}
							if(auto ft=isFixedIntTy(acc.e.type)) bound=ft.bits;
							else if(cast(ArrayTy)acc.e.type||cast(VectorTy)acc.e.type) bound=acc.e;
							else{
								whole=true;
								continue;
							}
						}
						auto el=Log(u,i,Y,X,freshName(),freshName(),Id.init,acc.type,acc,pos[cast(const(void)*)acc],bound,g.wAt,g.rAt,g.level);
						el.rLevel=g.rLevel;
						if(g.slot) el.slot=freshName();
						elems~=el;
					}
					if(whole||consume){
						auto ty=u in isCarried?carriedType.get(u,null):types.get(u,null);
						if(!ty) return null;
						auto l=Log(u,i,Y,X,freshName(),freshName(),Id.init,ty,null,0,null,g.wAt,g.rAt,g.level,rnodes);
						l.consume=consume;
						l.rLevel=g.rLevel;
						if(g.slot) l.slot=freshName();
						l.viaDummy=g.viaDummy;
						addLog(l);
					}else foreach(l;elems) addLog(l);
				}
			}
		}
		for(size_t b=0;b<needBits.length;b++){
			auto j=needBits[b][0];
			int Y=cast(int)needBits[b][1];
			if(logs.any!(l=>l.stm==i&&l.ite==j&&l.dst==Y)) continue;
			auto Z=bitSource(j,Y);
			if(Z==NONE) return null;
			Id[] vars;
			visitStm(ites[j].heads[0],(Expression x){
				if(auto id=cast(Identifier)x) if(colorOf(varName(id))!=NONE) vars~=varName(id);
			});
			auto n=pos[cast(const(void)*)ites[j].heads[0]];
			size_t level,wAt,rAt,rLevel;
			bool slot;
			if(!place(n,Z,(size_t start,size_t end)=>vars.any!(v=>defPos.get(v,[]).any!(d=>start<=d&&d<end)),level,wAt,rAt,rLevel,slot)) return null;
			auto l=Log(Id.init,i,Z,Y,freshName(),freshName(),Id.init,ites[j].heads[0].type,null,n,null,wAt,rAt,level);
			l.ite=j;
			l.rLevel=rLevel;
			if(slot) l.slot=freshName();
			addLog(l);
		}
	}
	auto loc=loop.loc;
	Identifier mkId(Id n){
		auto r=new Identifier(n);
		r.loc=loc;
		return r;
	}
	Expression annot(Expression e,Expression t){
		auto r=new TypeAnnotationExp(e,t,TypeAnnotationType.annotation);
		r.loc=loc;
		return r;
	}
	Expression define(Expression l,Expression r){
		auto d=new DefineExp(l,r);
		d.loc=loc;
		return d;
	}
	Expression dummyOf(Expression ty){
		auto r=new CallExp(mkId(Id.s!"__dummy"),ty,false,false);
		r.loc=loc;
		return r;
	}
	Expression dupOf(Expression e){
		auto r=new CallExp(mkId(Id.s!"dup"),e,false,false);
		r.loc=loc;
		return r;
	}
	Expression[] stmts;
	static if(is(T==ForExp)){
		auto lo=freshName(),hi=freshName(),st=range.step?freshName():Id.init;
		stmts~=define(mkId(lo),annot(range.left.copy(),range.left.type));
		if(range.step) stmts~=define(mkId(st),annot(range.step.copy(),range.step.type));
		stmts~=define(mkId(hi),annot(range.right.copy(),range.right.type));
	}else static if(is(T==RepeatExp)){
		auto num=freshName();
		stmts~=define(mkId(num),annot(loop.num.copy(),loop.num.type));
	}else{
		auto num=freshName();
		stmts~=define(mkId(num),annot(LiteralExp.makeInteger(0),ℕt(true)));
	}
	Id[Id] fNames;
	foreach(i,p;carried[0]) if(rank[classOf[i]]>P) fNames[p[1].name.id]=freshName();
	foreach(X;0..cast(int)classDeps.length+1){
		if(!atomColor.canFind(X)&&!(X==P&&atomColor.any!(c=>c>P))) continue;
		if(X==P) foreach(v,fv;fNames) stmts~=define(mkId(fv),dupOf(mkId(v)));
		bool readsLogs=logs.any!(l=>l.dst==X&&!l.rLevel);
		Id counter;
		if(readsLogs){
			counter=freshName();
			stmts~=define(mkId(counter),annot(LiteralExp.makeInteger(0),ℕt(true)));
		}
		foreach(l;logs) if(l.dst==X&&l.rLevel) stmts~=define(mkId(l.ctr),annot(LiteralExp.makeInteger(0),ℕt(true)));
		foreach(l;logs) if(l.src==X&&l.primary){
			auto empty=new VectorExp([]);
			empty.loc=loc;
			auto ety=l.access?arrayTy(l.type):l.type;
			stmts~=define(mkId(l.name),annot(empty,arrayTy(ety)));
		}
		Expression logEntry(Log l){
			if(l.ite!=size_t.max) return dupOf(ites[l.ite].heads[0].copy());
			if(!l.access) return dupOf(mkId(l.var));
			auto one=new VectorExp([dupOf(l.access.copy())]);
			one.loc=loc;
			return one;
		}
		Expression appendOf(Log l,Expression e){
			auto v=new VectorExp([e]);
			v.loc=loc;
			auto app=new CatAssignExp(mkId(l.name),v);
			app.loc=loc;
			return app;
		}
		Expression[] appendLog(Log l){
			Expression append(Expression e){ return appendOf(l,e); }
			if(l.slot!=Id.init) return [define(mkId(l.slot),logEntry(l))];
			if(!l.access||!l.bound) return [append(logEntry(l))];
			auto one=logEntry(l);
			Expression bound=l.bound.copy();
			if(l.bound is l.access.e){
				auto len=new Identifier(Id.s!"length");
				len.loc=loc;
				bound=new FieldExp(bound,len);
				bound.loc=loc;
			}
			Expression cond=new LtExp(l.access.a.copy(),bound);
			cond.loc=loc;
			if(!isSubtype(l.access.a.type,ℕt(true))){
				auto zero=LiteralExp.makeInteger(0);
				zero.loc=loc;
				auto nonneg=new GeExp(l.access.a.copy(),zero);
				nonneg.loc=loc;
				cond=new AndThenExp(nonneg,cond);
				cond.loc=loc;
			}
			auto none=new VectorExp([]);
			none.loc=loc;
			auto then=new CompoundExp([append(one)]);
			then.loc=loc;
			auto othw=new CompoundExp([append(annot(none,arrayTy(l.type)))]);
			othw.loc=loc;
			auto ite=new IteExp(cond,then,othw);
			ite.loc=loc;
			return [ite];
		}
		Expression[] readLog(Log l){
			auto idx=new IndexExp(mkId(l.name),mkId(l.rLevel?l.ctr:counter));
			idx.loc=loc;
			Expression[] r=[define(mkId(l.tmp),dupOf(idx))];
			if(l.rLevel){
				auto inc=new AddAssignExp(mkId(l.ctr),LiteralExp.makeInteger(1));
				inc.loc=loc;
				r~=inc;
			}
			return r;
		}
		bool hasIn(size_t k){
			foreach(a,ref at;atoms) if(inX(a,X)&&at.ites.canFind(k)) return true;
			foreach(l;logs){
				if(l.src==X&&l.primary&&atoms[l.wAt].ites[0..l.level].canFind(k)) return true;
				if(l.dst==X&&atoms[l.rAt].ites[0..l.rLevel].canFind(k)) return true;
			}
			return false;
		}
		bool keepIn(size_t a,int X){
			if(!keepAtom(a,X)) return false;
			if(atomColor[a]!=SHARED) return true;
			foreach_reverse(k;atoms[a].ites) if(ites[k].isLoop) return hasIn(k);
			return true;
		}
		Expression[] bdy;
		foreach(i,s;stms){
			Expression[] nodes;
			walkCond(s,false,(Expression x,bool c){ nodes~=x; });
			Id[const(void)*] elemOf,renameOf;
			foreach(l;logs) if(l.stm==i&&l.dst==X){
				if(l.access) elemOf[cast(const(void)*)nodes[l.node]]=l.tmp;
				else foreach(n;l.rnodes) renameOf[cast(const(void)*)nodes[n]]=l.tmp;
			}
			bool ok=true;
			void renameItrans(Expression c,Id[Id] names){
				if(!names.length) return;
				walkShallow(c,(Expression x){
					if(auto we=cast(WithExp)x) if(we.itrans)
						walkShallow(we.itrans,(Expression y){
							if(auto id=cast(Identifier)y) if(auto t=id.id in names) id.id=*t;
						});
				});
			}
			void renameSkipped(Expression c,Id[Id] names){
				if(!names.length) return;
				void ren(Expression y){
					visitStm(y,(Expression z){
						if(auto id=cast(Identifier)z) if(auto t=id.id in names) id.id=*t;
					});
				}
				walkShallow(c,(Expression x){
					if(auto tae=cast(TypeAnnotationExp)x) ren(tae.t);
					else if(auto ce=cast(CallExp)x) if(ce.isSquare) ren(ce.arg);
				});
			}
			Expression cp0(Expression o){
				auto c=o.copy();
				Expression[] on,cn;
				walkShallow(o,(Expression x){ on~=x; });
				walkShallow(c,(Expression x){ cn~=x; });
				if(on.length!=cn.length){
					Id[Id] names;
					foreach(x;on){
						if(cast(const(void)*)x in elemOf||cast(const(void)*)x in extracted) ok=false;
						if(auto t=cast(const(void)*)x in renameOf) if(auto id=cast(Identifier)x) names[varName(id)]=*t;
						FunctionDef fd=cast(FunctionDef)x;
						if(auto le=cast(LambdaExp)x) fd=le.fd;
						if(fd) foreach(decl;fd.capturedDecls) foreach(id;fd.captures[decl]) if(auto t=cast(const(void)*)id in renameOf) names[varName(id)]=*t;
					}
					if(names.length){
						import ast.substitute:statementFreeVarsImpl;
						statementFreeVarsImpl(c,(Identifier y){
							if(auto t=y.id in names) y.id=*t;
							return 0;
						});
						walkShallow(c,(Expression x){
							if(auto le=cast(LambdaExp)x) le.orig=le.fd.copy();
						});
					}
					return c;
				}
				Id[Id] itransNames;
				foreach(k,x;on){
					FunctionDef ofd,cfd;
					if(auto le=cast(LambdaExp)x){
						ofd=le.fd;
						cfd=(cast(LambdaExp)cn[k]).fd;
					}else if(auto fd=cast(FunctionDef)x){
						ofd=fd;
						cfd=cast(FunctionDef)cn[k];
					}
					if(ofd) foreach(decl;ofd.capturedDecls) foreach(id;ofd.captures[decl]){
						if(auto t=cast(const(void)*)id in renameOf){
							import ast.substitute:functionDefFreeVarsImpl;
							auto name=varName(id),tmp=*t;
							functionDefFreeVarsImpl(cfd,(Identifier y){
								if(y.id==name) y.id=tmp;
								return 0;
							});
						}
					}
					if(ofd&&cast(LambdaExp)cn[k]) (cast(LambdaExp)cn[k]).orig=cfd.copy();
					if(auto t=cast(const(void)*)x in elemOf){
						auto ie=cast(IndexExp)cn[k];
						ie.e=mkId(*t);
						ie.a=LiteralExp.makeInteger(0);
						ie.a.loc=loc;
					}
					if(auto f=cast(const(void)*)x in extracted) if(cast(const(void)*)o !in isExtractAtom){
						auto ce=cast(CallExp)cn[k];
						auto name=renameOf.get(cast(const(void)*)x,*f);
						ce.e=mkId(Id.s!"dup");
						ce.arg=mkId(name);
						ce.isSquare=false;
						continue;
					}
					if(auto t=cast(const(void)*)x in renameOf){
						itransNames[varName(cast(Identifier)x)]=*t;
						(cast(Identifier)cn[k]).id=*t;
					}
				}
				visitStm(o,(Expression x){
					if(auto t=cast(const(void)*)x in renameOf) if(auto id=cast(Identifier)x) itransNames[varName(id)]=*t;
				});
				renameItrans(c,itransNames);
				renameSkipped(c,itransNames);
				return c;
			}
			Expression cp(Expression o){
				auto c=cp0(o);
				if(X==P&&fNames.length){
					import ast.substitute:statementFreeVarsImpl;
					statementFreeVarsImpl(c,(Identifier y){
						if(auto t=y.id in fNames) y.id=*t;
						return 0;
					});
					walkShallow(c,(Expression x){
						if(auto le=cast(LambdaExp)x) le.orig=le.fd.copy();
						if(auto id=cast(Identifier)x) if(auto t=id.id in fNames) id.id=*t;
					});
					renameItrans(c,fNames);
				}
				return c;
			}
			struct Frame{
				size_t ite;
				bool inElse;
				Expression copy;
				CompoundExp block;
				SetX!Id locals;
				Expression[] thenPre,elsePre,after,post;
			}
			Frame[] open;
			Expression[] top;
			SetX!Id topLocals,outOfScope;
			void emit(Expression e){
				if(!open.length) top~=e;
				else open[$-1].block.s~=e;
			}
			SetX!Id[size_t] closedLocals;
			bool[size_t] closedLoops;
			struct Closed{
				IteExp copy;
				bool inElse;
				size_t ite;
			}
			Closed[Id] closedIn,extended;
			void popFrame(){
				auto f=open[$-1];
				open=open[0..$-1];
				f.block.s~=f.post;
				if(ites[f.ite].isLoop) closedLoops[f.ite]=true;
				else{
					auto cl=closedLocals.get(f.ite,SetX!Id.init);
					foreach(n;f.locals) cl.insert(n);
					closedLocals[f.ite]=cl;
					if(quantumIte(f.ite)) foreach(n;f.locals) closedIn[n]=Closed(cast(IteExp)f.copy,f.inElse,f.ite);
				}
				if(auto cite=cast(IteExp)f.copy){
					if(f.thenPre.length) cite.then.s=f.thenPre~cite.then.s;
					if(f.elsePre.length){
						if(!cite.othw){
							cite.othw=new CompoundExp([]);
							cite.othw.loc=loc;
						}
						cite.othw.s=f.elsePre~cite.othw.s;
					}
				}
				foreach(e;f.after) emit(e);
			}
			void alignTo(size_t[] chain,bool[] inElse,size_t at){
				size_t d=0;
				while(d<open.length&&d<chain.length&&open[d].ite==chain[d]&&open[d].inElse==inElse[d]) d++;
				bool toElse=d<open.length&&d<chain.length&&open[d].ite==chain[d]&&!open[d].inElse&&inElse[d];
				auto full=atoms[at].ites;
				while(open.length>(toElse?d+1:d)){
					auto dd=open.length-1;
					if(dd<full.length&&full[dd]==open[dd].ite&&atoms[at].inElse[dd]==open[dd].inElse){
						if(ites[open[dd].ite].isLoop) ok=false;
						foreach(n;open[dd].locals) outOfScope.insert(n);
					}
					popFrame();
				}
				if(toElse){
					auto cite=cast(IteExp)open[d].copy;
					open[d].inElse=true;
					open[d].locals=typeof(open[d].locals).init;
					if(!cite.othw){
						cite.othw=new CompoundExp([]);
						cite.othw.loc=loc;
					}
					open[d].block=cite.othw;
					d++;
				}
				for(;d<chain.length;d++){
					if(chain[d] in closedLoops) ok=false;
					if(auto cl=chain[d] in closedLocals) foreach(n;*cl) outOfScope.insert(n);
					if(ites[chain[d]].isWith){
						auto we=cast(WithExp)ites[chain[d]].e;
						auto lb=new CompoundExp([]);
						lb.loc=we.bdy.loc;
						Expression wcopy=lb;
						auto owner=atomColor[ites[chain[d]].pseudo];
						if(owner==X||owner==SHARED){
							auto nw=new WithExp(cast(CompoundExp)cp(we.trans),lb);
							nw.loc=we.loc;
							wcopy=nw;
						}
						emit(wcopy);
						open~=Frame(chain[d],false,wcopy,lb);
						continue;
					}
					if(ites[chain[d]].isLoop){
						auto lb=new CompoundExp([]);
						lb.loc=ites[chain[d]].e.loc;
						Expression lcopy;
						if(auto fe=cast(ForExp)ites[chain[d]].e){
							auto r=fe.aggr.isRange;
							auto nr=ForRange(r.leftExclusive,cp(r.left),r.step?cp(r.step):null,r.rightExclusive,cp(r.right));
							auto var=new Identifier(fe.loopVar.name.id);
							var.loc=fe.var.loc;
							lcopy=new ForExp(var,null,ForAggregate(nr),lb);
						}else if(auto we=cast(WhileExp)ites[chain[d]].e){
							Id rep;
							foreach(l;logs) if(l.stm==i&&l.dst==X&&l.count==chain[d]) rep=l.tmp;
							if(rep!=Id.init) lcopy=new RepeatExp(mkId(rep),lb);
							else lcopy=new WhileExp(cp(we.cond),lb);
						}
						else lcopy=new RepeatExp(cp((cast(RepeatExp)ites[chain[d]].e).num),lb);
						lcopy.loc=ites[chain[d]].e.loc;
						Expression[] post,after;
						foreach(l;logs) if(l.stm==i&&l.src==X&&l.primary&&l.count==chain[d]){
							emit(define(mkId(l.cntVar),annot(LiteralExp.makeInteger(0),ℕt(true))));
							auto inc=new AddAssignExp(mkId(l.cntVar),LiteralExp.makeInteger(1));
							inc.loc=loc;
							post~=inc;
							after~=appendOf(l,mkId(l.cntVar));
						}
						emit(lcopy);
						open~=Frame(chain[d],false,lcopy,lb);
						open[$-1].post=post;
						open[$-1].after=after;
						continue;
					}
					auto ite=cast(IteExp)ites[chain[d]].e;
					auto then=new CompoundExp([]);
					then.loc=ite.then.loc;
					CompoundExp othw=null;
					if(inElse[d]){
						othw=new CompoundExp([]);
						othw.loc=ite.othw.loc;
					}
					Expression cond=null;
					foreach(l;logs) if(l.stm==i&&l.dst==X&&l.ite==chain[d]) cond=mkId(l.tmp);
					auto cite=new IteExp(cond?cond:cp(ite.cond),then,othw);
					cite.loc=ite.loc;
					emit(cite);
					open~=Frame(chain[d],inElse[d],cite,inElse[d]?othw:then);
				}
			}
			foreach(a;0..atoms.length){
				if(atoms[a].stm!=i) continue;
				size_t[2][] evs;
				foreach(li,l;logs) if(l.stm==i){
					if(l.dst==X&&l.rAt==a&&!l.alias_) evs~=[l.rLevel,2*li];
					if(l.src==X&&l.primary&&l.wAt==a&&l.count==size_t.max) evs~=[l.level,2*li+1];
				}
				evs.sort!((x,y)=>x[0]<y[0],SwapStrategy.stable);
				foreach(ev;evs){
					auto l=logs[ev[1]/2];
					if(ev[1]%2==0){
						alignTo(atoms[a].ites[0..l.rLevel],atoms[a].inElse[0..l.rLevel],a);
						foreach(e;readLog(l)) emit(e);
					}else{
						alignTo(atoms[a].ites[0..l.level],atoms[a].inElse[0..l.level],a);
						foreach(e;appendLog(l)) emit(e);
						if(l.slot!=Id.init){
							foreach(d;l.rLevel..l.level){
								auto sdef=define(mkId(l.slot),l.viaDummy?dummyOf(l.type):logEntry(l));
								if(open[d].inElse) open[d].thenPre~=sdef;
								else open[d].elsePre~=sdef;
							}
							open[l.rLevel].after~=appendOf(l,mkId(l.slot));
						}
					}
				}
				foreach(l;logs) if(l.stm==i&&l.src==X&&l.consume&&l.wAt==a){
					alignTo(atoms[a].ites[0..l.level],atoms[a].inElse[0..l.level],a);
					auto fid=mkId(l.var);
					auto fe=new ForgetExp(fid,null);
					fe.loc=loc;
					emit(fe);
				}
				if(a in isPseudo||!keepIn(a,X)) continue;
				alignTo(atoms[a].ites,atoms[a].inElse,a);
				foreach(u;ainfos[a].uses) if(u in outOfScope){
					auto ty=ainfos[a].types.get(u,null);
					auto ci=u in closedIn;
					if(!ci||!ty||!isQuantum(ty)) return null;
					auto cite=ci.copy;
					if(!ci.inElse&&!cite.othw){
						cite.othw=new CompoundExp([]);
						cite.othw.loc=loc;
					}
					(ci.inElse?cite.then:cite.othw).s~=define(mkId(u),dummyOf(ty));
					outOfScope.remove(u);
					extended[u]=*ci;
					if(auto cl=ci.ite in closedLocals) cl.remove(u);
					closedIn.remove(u);
				}
				foreach(u;ainfos[a].consumed) if(auto ci=u in extended){
					auto ty=ainfos[a].types.get(u,null);
					foreach(ref f;open) if(f.ite==ci.ite&&f.inElse==ci.inElse){
						auto fe=new ForgetExp(mkId(u),dummyOf(ty));
						fe.loc=loc;
						if(f.inElse) f.thenPre~=fe;
						else f.elsePre~=fe;
					}
					extended.remove(u);
				}
				foreach(dname;ainfos[a].defs){
					outOfScope.remove(dname);
					if(dname in isCarried||dname in topLocals||open.any!(f=>dname in f.locals)) continue;
					if(open.length) open[$-1].locals.insert(dname);
					else topLocals.insert(dname);
				}
				emit(cp(atoms[a].e));
			}
			while(open.length) popFrame();
			if(!ok) return null;
			bdy~=top;
		}
		if(readsLogs){
			auto inc=new AddAssignExp(mkId(counter),LiteralExp.makeInteger(1));
			inc.loc=loc;
			bdy~=inc;
		}
		static if(is(T==WhileExp)) if(X==0){
			auto inc=new AddAssignExp(mkId(num),LiteralExp.makeInteger(1));
			inc.loc=loc;
			bdy~=inc;
		}
		auto nbdy=new CompoundExp(bdy);
		nbdy.loc=loop.bdy.loc;
		static if(is(T==ForExp)){
			auto nrange=ForRange(range.leftExclusive,mkId(lo),range.step?mkId(st):null,range.rightExclusive,mkId(hi));
			auto nl=new ForExp(mkId(loop.loopVar.name.id),null,ForAggregate(nrange),nbdy);
		}else static if(is(T==WhileExp)){
			Expression nl;
			if(X==0){
				auto nw=new WhileExp(loop.cond.copy(),nbdy);
				nw.noSplit=true;
				nl=nw;
			}else{
				auto nr=new RepeatExp(mkId(num),nbdy);
				nr.noSplit=true;
				nl=nr;
			}
		}else auto nl=new RepeatExp(mkId(num),nbdy);
		nl.loc=loc;
		static if(!is(T==WhileExp)) nl.noSplit=true;
		stmts~=nl;
	}
	foreach(v,fv;fNames){
		auto fe=new ForgetExp(mkId(fv),dupOf(mkId(v)));
		fe.loc=loc;
		stmts~=fe;
	}
	auto split=new CompoundExp(stmts);
	split.loc=loc;
	sc.restoreStateSnapshot(state.origStateSnapshot);
	static if(__traits(hasMember,astopt,"dumpLoops")) if(astopt.dumpLoops){
		import util.io:stderr;
		stderr.writeln(loop);
		stderr.writeln("-loop-splitting→");
		stderr.writeln(split);
	}
	return statementSemantic(split,sc,flags);
}

Expression lowerLoop(T)(T loop,FixedPointIterState state,Scope sc,ref StmFlags flags)in{
	assert(loop.isSemCompleted());
}do{
	if(auto r=splitLoop(loop,state,sc,flags)) return r;
	enum returnOnlyMoved=false; // (experimental)
	enum separateConstParams=true; // (necessary inside a `with` transformation)
	SetX!Declaration accessedDecls;
	if(separateConstParams){
		void collectAccesses(Expression e){
			if(!e) return;
			foreach(sub;e.subexpressions){
				if(auto id=cast(Identifier)sub)
					if(id.meaning) accessedDecls.insert(id.meaning.canonicalSource);
			}
		}
		collectAccesses(loop.bdy);
	}
	// continuation-passing lowering for loops with early returns:
	// the statements after the loop (which end in a `return`) become the base case of the recursion
	Expression[] continuation=null;
	static if(language==silq){
		static if(is(T==WhileExp)) bool contInfinite=isTrue(loop.cond);
		else enum contInfinite=false;
		if(!contInfinite&&containsReturn(loop.bdy))
			continuation=sc.loopContinuation.take(loop);
	}
	// with a continuation, lifted loop-carried variables are threaded through the recursion as `const`
	// parameters, so that they are still lifted in the code after the loop and in join points in the body
	auto loopParams_=state.prevStateSnapshot.loopParams(loop.bdy.blscope_,state.dummyAnalysisRan&&!continuation?&state.mustBeConstFromDummies:null,separateConstParams,&accessedDecls);
	auto constParams=loopParams_[0], movedParams=loopParams_[1];
	static if(is(T==WhileExp)){
		Q!(Id,Declaration,Expression,bool)[] loopParams=[];
	}else static if(is(T==ForExp)){
		auto loopVarId=loop.var.id;
		Expression loopVarType;
		Q!(Id,Declaration,Expression,bool)[] loopParams;
		if(auto range=loop.aggr.isRange){
			loopVarType=loop.aggr.elementType();
			assert(!!loopVarType);
			auto loopParamType=loopVarType;
			if(loopParamType is Bool(true)) loopParamType=ℕt(true);
			if(range.step){
				if(auto at=arithmeticType!false(loopParamType,range.step.type))
					loopParamType=at;
			}
			Declaration loopVarDecl=loop.loopVar;
			loopParams=[q(loopVarId,loopVarDecl,loopParamType,true)];
		}else{
			sc.error("aggregate type not yet supported by loop lowering pass",loop.aggr.loc);
			loop.setSemForceError();
			return loop;
		}
	}else static if(is(T==RepeatExp)){
		auto loopVarId=freshName();
		Expression loopVarType=ℕt(true);
		auto loopVarDeclName=new Identifier(loopVarId);
		loopVarDeclName.loc=loop.num.loc;
		auto loopVarDecl=new VarDecl(loopVarDeclName);
		loopVarDecl.loc=loop.num.loc;
		loopVarDecl.vtype=loop.num.type;
		loopVarDecl.sstate=SemState.completed;
		auto loopParams=[q(loopVarId,cast(Declaration)loopVarDecl,loopVarType,true)];
	}else static assert(0);
	Expression.CopyArgs cargsDefault;
	//imported!"util.io".writeln(constParams,movedParams,nsbdy);
	Identifier[] ids(Q!(Id,Declaration,Expression,bool)[] prms,bool checkDefined){
		return prms.map!((p){
			auto id=new Identifier(p[1].name.id);
			id.loc=p[1].loc;
			if(!checkDefined||!sc.canInsert(p[1].name.id)) return id;
			return null;
		}).filter!(id=>!!id).array;
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
		auto returnTpl=new TupleExp(cast(Expression[])ids(constMovedParams.filter!(p=>p[3]).array,true));
		returnTpl.loc=loop.loc;
	}
	auto cee=new Identifier(fi);
	cee.loc=loop.loc;
	Identifier[] constTmpNames;
	Parameter[] params;
	foreach(i,p;allParams){
		bool isConst=i<loopParams.length+constParams.length;
		bool mayChange=p[3];
		auto id=isConst&&mayChange?freshName:p[1].name.id;
		auto pname=new Identifier(id);
		pname.loc=p[1].loc;
		if(isConst&&mayChange) constTmpNames~=pname.copy(cargsDefault);
		auto ptype=p[2];
		auto param=new Parameter(isConst,pname,ptype);
		param.loc=p[1].loc;
		params~=param;
	}
	auto paramTmpTpl=new TupleExp(cast(Expression[])chain(constTmpNames[loopParams.length..$].map!(id=>id.copy(cargsDefault)),ids(movedParams,false)).array);
	DefineExp constParamDef=null;
	if(constTmpNames.length){
		static if(is(T==ForExp)) auto tmpNames=constTmpNames[loopParams.length..$];
		else auto tmpNames=constTmpNames;
		auto constTmpTpl=new TupleExp(cast(Expression[])tmpNames);
		constTmpTpl.loc=loop.loc;
		static if(is(T==ForExp)) auto cParams=constParams;
		else auto cParams=loopConstParams;
		auto constTpl=new TupleExp(cast(Expression[])ids(cParams.filter!(p=>p[3]).array,false));
		constTpl.loc=loop.loc;
		constParamDef=new DefineExp(constTpl,constTmpTpl);
		constParamDef.loc=loop.loc;
	}
	bool isInfinite=false;
	bool isCertainReturn=definitelyReturns(loop.bdy);
	static if(is(T==WhileExp)){
		isInfinite=isTrue(loop.cond);
		auto ncond=loop.cond.copy(cargsDefault);
	}else static if(is(T==ForExp)){
		//writeln("?? ",constParams);
		Expression ncond;
		Identifier leftName;
		Expression leftDef;
		Identifier stepName=null;
		Expression stepDef=null;
		Identifier rightName;
		Expression rightDef;
		Identifier modMatchName=null;
		Expression modMatchDef=null;
		Expression adjDef=null;
		Expression adjIte=null;
		Expression adjUpd=null;
		if(auto range=loop.aggr.isRange){
			leftName=new Identifier(freshName());
			leftName.loc=range.left.loc;
			auto leftInit=range.left.copy(cargsDefault);
			leftInit.loc=range.left.loc;
			leftDef=new DefineExp(leftName,leftInit);
			leftDef.loc=range.left.loc;
			rightName=new Identifier(freshName());
			rightName.loc=range.right.loc;
			auto rightInit=range.right.copy(cargsDefault);
			rightInit.loc=range.right.loc;
			rightDef=new DefineExp(rightName,rightInit);
			rightDef.loc=range.right.loc;
			if(range.step){
				stepName=new Identifier(freshName());
				auto stepInit=range.step.copy(cargsDefault);
				stepInit.loc=range.step.loc;
				stepDef=new DefineExp(stepName,stepInit);
				stepDef.loc=range.step.loc;
				if(range.leftExclusive==range.rightExclusive){
					auto two=LiteralExp.makeInteger(2);
					two.loc=range.step.loc;
					auto add=new AddExp(leftName.copy(cargsDefault),rightName.copy(cargsDefault));
					add.loc=range.step.loc;
					modMatchName=new Identifier(freshName());
					modMatchName.loc=range.step.loc;
					auto modMatchInit=new IDivExp(add,two);
					modMatchInit.loc=range.step.loc;
					modMatchDef=new DefineExp(modMatchName,modMatchInit);
					modMatchDef.loc=range.step.loc;
				}else{
					bool isOne=false;
					if(auto v=range.step.eval().asIntegerConstant())
						isOne=util.among(v.get(),-1,1);
					if(!isOne) modMatchName=range.leftExclusive?rightName:leftName;
					else modMatchName=leftName;
				}
				Expression adjName=null;
				if(modMatchName !is leftName){
					auto sub=new SubExp(modMatchName.copy(cargsDefault),leftName.copy(cargsDefault));
					sub.brackets++;
					sub.loc=range.step.loc;
					adjName=new Identifier(freshName());
					adjName.loc=range.step.loc;
					auto adjInit=new ModExp(sub,stepName.copy(cargsDefault));
					adjDef=new DefineExp(adjName,adjInit);
					adjDef.loc=range.step.loc;
				}
				if(range.leftExclusive){
					if(adjName){
						auto zero=LiteralExp.makeInteger(0);
						zero.loc=range.step.loc;
						auto adjCond=new EqExp(adjName.copy(cargsDefault),zero);
						adjCond.loc=range.step.loc;
						auto setAdj=new AssignExp(adjName.copy(cargsDefault),stepName.copy(cargsDefault));
						setAdj.loc=range.step.loc;
						auto setAdjBdy=new CompoundExp([setAdj]);
						setAdjBdy.loc=range.step.loc;
						adjIte=new IteExp(adjCond,setAdjBdy,null);
						adjIte.loc=range.step.loc;
					}else{
						adjUpd=new AddAssignExp(leftName.copy(cargsDefault),stepName.copy(cargsDefault));
						adjUpd.loc=range.step.loc;
					}
				}
				if(adjName){
					adjUpd=new AddAssignExp(leftName.copy(cargsDefault),adjName.copy(cargsDefault));
					adjUpd.loc=range.step.loc;
				}
			}else if(range.leftExclusive){
				auto one=LiteralExp.makeInteger(1);
				one.loc=range.left.loc;
				adjUpd=new AddAssignExp(leftName.copy(cargsDefault),one);
				adjUpd.loc=range.left.loc;
			}
			auto loopVarName=constTmpNames[0].copy(cargsDefault);
			loopVarName.loc=loop.var.loc;
			Expression makeForCond(){
				auto makePositive(){
					auto ncond=range.rightExclusive?
						new LtExp(loopVarName,rightName.copy(cargsDefault))
						:   new LeExp(loopVarName,rightName.copy(cargsDefault));
					ncond.loc=range.loc;
					return ncond;
				}
				auto makeNegative(){
					auto ncond=range.rightExclusive?
						new GtExp(loopVarName,rightName.copy(cargsDefault))
						:   new GeExp(loopVarName,rightName.copy(cargsDefault));
					ncond.loc=range.loc;
					return ncond;
				}
				if(!range.step||isSubtype(range.step.type,ℕt(true))){
					return makePositive();
				}
				if(auto v=range.step.eval().asIntegerConstant()){
					if(v.get()<0){
						return makeNegative();
					}
				}
				auto zero=LiteralExp.makeInteger(0);
				zero.loc=range.loc;
				assert(!!stepName);
				auto stepPos=new GeExp(stepName.copy(cargsDefault),zero);
				stepPos.loc=range.loc;
				auto posBdy=new CompoundExp([makePositive()]);
				posBdy.loc=range.loc;
				auto negBdy=new CompoundExp([makeNegative()]);
				negBdy.loc=range.loc;
				auto ite=new IteExp(stepPos,posBdy,negBdy);
				ite.loc=range.loc;
				ite.brackets++;
				return ite;
			}
			ncond=makeForCond();
		}else{
			assert(0,"unknown aggregate type");
		}
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
	auto paramTpl=new TupleExp(cast(Expression[])ids(allParams,false));
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
	static if(is(T==ForExp)){
		auto lhs=cast(Expression[])ids(loopParams,false);
		if(loopParams[0][3]&&loopParams[0][2]!is loopVarType){
			auto tae=new TypeAnnotationExp(lhs[0],loopVarType,TypeAnnotationType.coercion);
			tae.loc=lhs[0].loc;
			lhs[0]=tae;
		}
		if(loopParams.length==1){
			auto loopParamDef=new DefineExp(lhs[0],constTmpNames[0]);
			loopParamDef.loc=loop.loc;
			nbdy.s=loopParamDef~nbdy.s;
		}else if(loopParams.length>1){
			auto loopTpl=new TupleExp(lhs);
			loopTpl.loc=loop.var.loc;
			auto loopTmpTpl=new TupleExp(cast(Expression[])constTmpNames[0..loopParams.length]);
			loopTmpTpl.loc=loop.var.loc;
			auto loopParamDef=new DefineExp(loopTpl,loopTmpTpl);
			loopParamDef.loc=loop.loc;
			nbdy.s=loopParamDef~nbdy.s;
		}
	}

	if(!isCertainReturn){
		if(continuation){
			auto thene=new ReturnExp(ce);
			thene.loc=ce.loc;
			nbdy.s~=thene;
			static if(language==silq) if(auto ns=erpTransform(nbdy.s)) nbdy.s=ns;
		}else{
			auto thene=new DefineExp(retName,ce);
			thene.loc=ce.loc;
			nbdy.s~=thene;
		}
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
	if(continuation){
		auto othw=new CompoundExp(continuation.map!(st=>st.copy(cargsDefault)).array);
		othw.loc=loop.loc;
		auto ite=new IteExp(ncond,nbdy,othw);
		ite.loc=loop.loc;
		bdy=ite;
	}else if(!isInfinite){
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
	Expression ret=null;
	if(!continuation&&(!isInfinite||!isCertainReturn)){
		ret=new ReturnExp(retName.copy(cargsDefault)); // avoid non-toplevel return
		ret.loc=loop.loc;
	}
	auto cmpbdy=cast(CompoundExp)bdy;
	auto fbdy=new CompoundExp((constParamDef?[cast(Expression)constParamDef]:[])~(cmpbdy?cmpbdy.s:[bdy])~(ret?[ret]:[]));
	fbdy.loc=bdy.loc;
	auto fd=new FunctionDef(fdn,params,true,null,fbdy);
	foreach(p;constParams) if(p[3]) fd.loweredConstIds.insert(p[0]);
	fd.attributes[Id.s!"silq-loop"] = LiteralExp.makeString(lowerf(T.stringof[0..$-"Exp".length]));
	fd.annotation=pure_;
	fd.inferAnnotation=true;
	fd.loc=loop.loc;
	static if(is(T==ForExp)){
		auto paramTpl2=new TupleExp([cast(Expression)leftName.copy(cargsDefault)]~cast(Expression[])ids(constMovedParams,false));
	}else static if(is(T==RepeatExp)){
		auto zero=LiteralExp.makeInteger(0);
		zero.loc=loop.loc;
		auto paramTpl2=new TupleExp([cast(Expression)zero]~cast(Expression[])ids(constMovedParams,false));
	}else{
		auto paramTpl2=new TupleExp(cast(Expression[])ids(allParams,false));
	}
	paramTpl2.loc=loop.loc;
	auto ce2=new CallExp(cee.copy(cargsDefault),paramTpl2,false,false);
	ce2.loc=loop.loc;
	static if(returnOnlyMoved){
		auto defTpl=new TupleExp(cast(Expression[])ids(movedParams,true));
		defTpl.loc=movedTpl.loc;
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
				auto assgnTpl1=new TupleExp(cast(Expression[])ids(constParams.filter!(p=>p[3]).array,false));
				assgnTpl1.loc=loop.loc;
				auto assgnTpl2=new TupleExp(cast(Expression[])constTmpNames[loopParams.length..$].map!(id=>id.copy(cargsDefault)).array);
				assgnTpl2.loc=loop.loc;
				auto assgn=new AssignExp(assgnTpl1,assgnTpl2);
				assgn.loc=loop.loc;
				stmts~=assgn;
			}
		}
	}
	if(continuation){
		auto fret=new ReturnExp(ce2);
		fret.loc=loop.loc;
		stmts~=fret;
		sc.loopContinuation.used=true;
	}else if(hasEarlyReturns){
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
	}else if(isInfinite){
		auto fret=new ReturnExp(ce2);
		fret.loc=loop.loc;
		stmts~=fret;
	}else if(defTpl.e.length){
		defineLocals(stmts,ce2);
	}else{
		stmts~=ce2;
	}
	static if(is(T==ForExp)){
		stmts=[cast(Expression)leftDef]~(stepDef?[stepDef]:[])~[cast(Expression)rightDef]~(modMatchDef?[modMatchDef]:[])~(adjDef?[adjDef]:[])~(adjIte?[adjIte]:[])~(adjUpd?[adjUpd]:[])~stmts;
	}else static if(is(T==RepeatExp)){
		stmts=[cast(Expression)numDef]~stmts;
	}
	auto lowered=new CompoundExp(stmts);
	lowered.loc=loop.loc;
	sc.restoreStateSnapshot(state.origStateSnapshot);
	//imported!"util.io".writeln("BEFORE SEMANTIC: ",lowered);
	auto result=statementSemantic(lowered,sc,flags);
	if(result.isSemError()){
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

static if(language==silq){
// Early-return elimination (ERP).
// A function with loops that contain `return` statements is first analyzed with its loops kept (stage 1),
// recording the variables in scope after each statement that contains such a loop and is followed by more code.
// Then the code following such statements is moved into local join-point functions, called at the end of each
// branch (with parameters derived from the recorded information), and the function is analyzed again, lowering
// its loops (stage 2). Every loop with an early return is then followed by code that ends in a `return`, which the
// loop lowering uses as the base case of the recursion (see `lowerLoop`).
struct ERPVar{
	Id name;
	Expression type;
	bool lifted,isConst;
}
ERPVar[][size_t] erpJoins; // by location of the statement
size_t erpKey(Location loc){ return cast(size_t)loc.rep.ptr^(cast(size_t)loc.rep.length<<48); }
bool containsReturn(Expression e){
	bool r=false;
	visitStm(e,(Expression x){ if(cast(ReturnExp)x) r=true; });
	return r;
}
bool hasLoopWithReturn(Expression e){
	bool r=false;
	visitStm(e,(Expression x){
		if(cast(ForExp)x||cast(WhileExp)x||cast(RepeatExp)x) if(containsReturn(x)) r=true;
	});
	return r;
}
// Code after a loop with an early return (ending in a `return`), offered to `lowerLoop` by `compoundExpSemantic`.
struct LoopContinuation{
	Expression[] stms;
	Expression target; // the loop statement the continuation is offered to
	bool used; // set by `lowerLoop` if it absorbed the continuation
	Expression absorbedBy; // set if the desugaring of `target` passed the continuation on
	// offer `stms[i+1..$]` to the loop statement `stms[i]`, if applicable
	bool offer(Expression[] block,size_t i){
		auto e=block[i];
		if(!astopt.removeLoops||!(cast(ForExp)e||cast(WhileExp)e||cast(RepeatExp)e)) return false;
		if(i+1>=block.length||!endsWithReturn(block[$-1])||!containsReturn(e)) return false;
		stms=block[i+1..$];
		target=e;
		used=false;
		absorbedBy=null;
		return true;
	}
	// take the continuation offered to `loop` (if any)
	Expression[] take(Expression loop){
		if(!stms.length||target !is loop) return null;
		auto r=stms;
		stms=null;
		target=null;
		return r;
	}
	// after analyzing the loop statement `original`: whether the continuation was absorbed
	bool finish(Expression original){
		bool r=used||absorbedBy is original;
		this=LoopContinuation.init;
		return r;
	}
}
bool erpRecording(Scope sc){
	for(auto fd=sc.getFunction();fd;fd=fd.scope_?fd.scope_.getFunction():null)
		if(fd.erpStage==1) return true;
	return false;
}
void erpRecordJoin(Expression stm,Scope sc){
	ERPVar[] vars;
	SetX!Id seen;
	auto fun=sc.getFunction();
	for(Scope c=sc;c;c=c.parentScope()){
		foreach(_,d;c.rnsymtab){
			auto vd=cast(VarDecl)d;
			if(!vd||vd.isSemError()||cast(DeadDecl)d||!vd.name) continue;
			if(vd.name.id in seen) continue;
			seen.insert(vd.name.id);
			if(!vd.scope_||vd.scope_.getFunction() !is fun) continue;
			auto type=typeForDecl(vd);
			if(!type) continue;
			vars~=ERPVar(vd.name.id,type,!type.isClassical()&&sc.canForget(vd),vd.isConst);
		}
		if(cast(FunctionScope)c) break;
	}
	erpJoins[erpKey(stm.loc)]=vars;
}
// stage 1 starts before the body of `fd` is analyzed
void erpBeforeBody(FunctionDef fd){
	if(astopt.removeLoops&&fd.erpStage==0&&!fd.keepLoops&&fd.body_&&!fd.body_.isSemStarted()&&hasLoopWithReturn(fd.body_)){
		fd.erpStage=1;
		fd.keepLoops=true;
	}
}
// record join-point information after statement `stms[i]` (originally `original`) has been analyzed
void erpAfterStatement(Expression original,Expression[] stms,size_t i,Scope sc){
	if(i+1<stms.length&&(cast(IteExp)original||cast(CompoundExp)original)&&hasLoopWithReturn(original)&&erpRecording(sc))
		erpRecordJoin(original,sc);
}
// Stage 2: rewrites `fd.origBody_` (to be analyzed again with loops lowered). Returns false if the function has errors.
bool erpRewrite(FunctionDef fd){
	fd.keepLoops=false;
	fd.erpStage=2;
	if(fd.isSemError()||!fd.origBody_) return false;
	auto nb=fd.origBody_.copy();
	if(nb.s.length&&!endsWithReturn(nb)){
		// make the implicit `return` at the end explicit, so that loops can absorb it as part of their continuation
		bool onlyUnit=true;
		visitStm(nb,(Expression x){
			if(auto ret=cast(ReturnExp)x){
				auto tpl=cast(TupleExp)ret.e;
				if(ret.e&&!(tpl&&!tpl.e.length)) onlyUnit=false;
			}
		});
		if(onlyUnit){
			auto unitv=new TupleExp([]);
			unitv.loc=nb.loc;
			auto ret=new ReturnExp(unitv);
			ret.loc=nb.loc;
			nb.s~=ret;
		}
	}
	if(auto ns=erpTransform(nb.s)) nb.s=ns;
	fd.origBody_=nb;
	return true;
}
// Moves the code after statements that contain loops with early returns into join points.
// Returns `null` if some needed information is missing.
Expression[] erpTransform(Expression[] stms){
	bool ok;
	auto r=erpTransformImpl(stms,[],ok);
	return ok?(r?r:[]):null;
}
// `tail`: statements to execute at the end of `stms` (a call to an enclosing join point)
Expression[] erpTransformImpl(Expression[] stms,Expression[] tail,out bool ok){
	Expression.CopyArgs cargs;
	Expression[] r;
	foreach(i,s;stms){
		bool nested=(cast(IteExp)s||cast(CompoundExp)s)&&hasLoopWithReturn(s);
		if(!nested){
			r~=s;
			continue;
		}
		auto rest=stms[i+1..$];
		Expression[] ntail=tail;
		Expression kdef=null;
		if(rest.length){
			auto vars=erpKey(s.loc) in erpJoins;
			if(!vars) return null;
			bool rok;
			auto ntrest=erpTransformImpl(rest,tail,rok);
			if(!rok) return null;
			kdef=erpJoinPoint(s,ntrest,*vars,ntail);
			if(!kdef) return null;
		}
		bool transformBlock(CompoundExp b){
			bool bok;
			auto nb=erpTransformImpl(b.s,ntail,bok);
			if(!bok) return false;
			b.s=nb;
			return true;
		}
		if(auto ite=cast(IteExp)s){
			if(!transformBlock(ite.then)) return null;
			if(!ite.othw&&ntail.length){
				ite.othw=new CompoundExp([]);
				ite.othw.loc=ite.loc;
			}
			if(ite.othw&&!transformBlock(ite.othw)) return null;
		}else if(auto cmp=cast(CompoundExp)s){
			if(!transformBlock(cmp)) return null;
		}
		if(kdef) r~=kdef;
		r~=s;
		ok=true;
		return r; // `s` absorbed the rest and the tail
	}
	if(tail.length&&!(r.length&&endsWithReturn(r[$-1])))
		r~=tail.map!(t=>t.copy(cargs)).array;
	ok=true;
	return r;
}
// builds `def k(params){ rest }` and the call `return k(args)` (in `tail`)
Expression erpJoinPoint(Expression s,Expression[] rest,ERPVar[] vars,out Expression[] tail){
	import ast.substitute:statementFreeVarsImpl;
	Expression.CopyArgs cargs;
	SetX!Id used;
	foreach(st;rest) statementFreeVarsImpl(st,(Identifier y){ used.insert(y.id); return 0; });
	Parameter[] params;
	Expression[] args,prologue;
	foreach(v;vars){
		if(v.name !in used||v.isConst) continue;
		auto pname=new Identifier(v.name);
		pname.loc=s.loc;
		if(v.lifted){
			auto tmp=new Identifier(freshName());
			tmp.loc=s.loc;
			auto param=new Parameter(true,tmp,v.type.copy(cargs));
			param.loc=s.loc;
			params~=param;
			auto dupe=new CallExp(new Identifier(Id.s!"dup"),tmp.copy(),false,false);
			dupe.loc=s.loc;
			auto def=new DefineExp(pname,dupe);
			def.loc=s.loc;
			prologue~=def;
		}else{
			auto param=new Parameter(false,pname,v.type.copy(cargs));
			param.loc=s.loc;
			params~=param;
		}
		auto arg=new Identifier(v.name);
		arg.loc=s.loc;
		args~=arg;
	}
	auto kname=new Identifier(freshName());
	kname.loc=s.loc;
	auto body_=new CompoundExp(prologue~rest);
	body_.loc=rest[0].loc;
	auto fd=new FunctionDef(kname,params,true,null,body_);
	fd.annotation=pure_;
	fd.inferAnnotation=true;
	fd.loc=s.loc;
	auto call=new CallExp(kname.copy(),new TupleExp(args),false,false);
	call.loc=s.loc;
	auto ret=new ReturnExp(call);
	ret.loc=s.loc;
	tail=[ret];
	return fd;
}
}
// syntactic check whether a statement always ends in a `return`
bool endsWithReturn(Expression e){
	if(cast(ReturnExp)e) return true;
	if(auto ae=cast(AssertExp)e){
		if(ae.e.type) return isFalse(ae.e);
		if(auto id=cast(Identifier)ae.e) return id.id==Id.s!"false"; // not yet analyzed
		if(auto le=cast(LiteralExp)ae.e) return le.lit.type==Tok!"0"&&le.lit.str=="0";
		return false;
	}
	if(auto ce=cast(CompoundExp)e) return ce.s.length&&endsWithReturn(ce.s[$-1]);
	if(auto ite=cast(IteExp)e) return ite.othw&&endsWithReturn(ite.then)&&endsWithReturn(ite.othw);
	return false;
}
