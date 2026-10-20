// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

// Lowering of loops to recursive functions (`--remove-loops`):
//  - `sliceLoop`: lowers a loop with loop-carried lifted state into a main loop and loops that recompute the lifted state
//    (each lowered into a recursive function)
//  - `splitLoop`: splits a loop into several loops, such that loop-carried lifted state can be lowered
//    into `qfree` recursive functions (with logs communicating values between the loops; used where `sliceLoop` is not)
//  - `lowerLoop`: lowers a single loop into a recursive function
//  - early-return elimination: prepares functions whose loops contain `return` statements for `lowerLoop`
module ast.looplowering;
import astopt;

import std.array,std.algorithm,std.range,std.exception;
import std.format, std.conv, util.tuple:Q=Tuple,q=tuple;
import ast.lexer,ast.scope_,ast.expression,ast.type,ast.conversion;
import ast.declaration,ast.error,util;
import ast.semantic_;

// Conservative check that evaluating `e` cannot fail (e.g., an `assert` or out-of-bounds access) or diverge.
// Only such code may be removed, or executed where the original program would not execute it.
bool cannotFail(Expression e){
	bool ok=true;
	// calls in definition targets are reversed: e.g., `dup(a):=z` checks that `z` equals `a`, which may fail
	SetX!CallExp targetCalls;
	visitStm(e,(Expression x){
		if(auto de=cast(DefineExp)x) visitStm(de.e1,(Expression y){ if(auto ce=cast(CallExp)y) targetCalls.insert(ce); });
	});
	visitStm(e,(Expression x){
		if(!ok) return;
		if(auto ce=cast(CallExp)x){
			if(ce.isSquare) return;
			Expression f=ce.e;
			while(auto sq=cast(CallExp)f){
				if(!sq.isSquare) break;
				f=sq.e;
			}
			auto id=cast(Identifier)f;
			auto fd=id?cast(FunctionDef)id.meaning:null;
			if(!fd){ ok=false; return; }
			if(ce in targetCalls){ // only reversed unitary primitives cannot fail
				auto prim=isPrimitive(fd);
				if(!prim||!util.among(prim,"H","X","Y","Z","rX","rY","rZ")) ok=false;
				return;
			}
			if(auto prim=isPrimitive(fd)){
				if(!util.among(prim,"dup","M","H","X","Y","Z","P","rX","rY","rZ")) ok=false;
			}else{
				// (the prelude's `dup` and `measure` are curried: the called function is the one returned by the outer
				// definition, which the parser marks `artificial` without a value)
				import ast.modules:isInPrelude;
				if(!(isInPrelude(fd)&&fd.attributes.getPtr(Id.s!"artificial")&&util.among(fd.getName,"dup","measure","rotZ"))) ok=false;
			}
		}else if(cast(IndexExp)x||cast(SliceExp)x||cast(DivExp)x||cast(IDivExp)x||cast(ModExp)x||cast(PowExp)x
			||cast(AssertExp)x||isLoopStatement(x)||cast(ReturnExp)x){
			ok=false;
		}else if(auto tae=cast(TypeAnnotationExp)x){
			if(tae.annotationType==TypeAnnotationType.coercion) ok=false;
		}else if(auto fe=cast(ForgetExp)x){
			// an explicit value may be correct only on some basis states (e.g., where a guarding condition holds)
			if(fe.val) ok=false;
		}
	});
	return ok;
}
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
	if(isLoopStatement(e)){ // (`for` loops are handled above)
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

// Whether a lifted copy of the loop-carried variable `decl` with dependencies `dep` could not be forgotten after the loop,
// as its (transitive) dependencies are changed by the loop
private bool dependsTransitivelyOnLoopState(ref FixedPointIterState state,Scope sc,bool[Declaration] loopState,Declaration decl,Dependency dep){
	bool[Declaration] visited;
	Declaration[] todo;
	foreach(d;dep.dependencies) todo~=d;
	while(todo.length){
		auto d=todo[$-1];
		todo=todo[0..$-1];
		if(d in visited) continue;
		visited[d]=true;
		if(d !is decl&&d in loopState) return true;
		auto dd=state.prevStateSnapshot.dependencyOf(d);
		if(dd.isTop){
			// a dependency that was recomputable at the loop entry but is not after an iteration (as the loop consumes
			// one of its dependencies) could no longer be forgotten after the loop
			if(!state.origStateSnapshot.dependencyOf(d).isTop) return true;
			// a variable that could still be forgotten at its last use (before it became non-recomputable) may be
			// forgotten there, before the loop: it is not available after the loop unless it is consumed later
			if(auto lu=sc.lastUses.get(d,false)){
				for(;;){ // (the last use itself, not a split into a nested scope)
					while(lu.forwardTo) lu=lu.forwardTo;
					if(lu.kind!=imported!"ast.lastuse".LastUse.Kind.lazySplit) break;
					lu=lu.getSplitFrom();
				}
				if(lu.isConsumption()||!lu.dep.isTop) return true;
			}
			continue; // (not recomputable anyway, but available: the traversal ends here)
		}
		foreach(e;dd.dependencies) todo~=e;
	}
	return false;
}

// (for diagnostics, the variables after a lowered loop are linked to those of the analysis of the loop itself)
private void linkLoweredVariables(Scope sc,ref MapX!(Id,Declaration) before){
	foreach(id,d;sc.rnsymtab)
		if(auto vd=cast(VarDecl)d) if(auto od=cast(VarDecl)before.get(id,null))
			if(od !is vd&&!vd.loweredFrom&&!vd.typeSource&&!od.isSemError()) vd.loweredFrom=od;
}
Expression splitLoop(T)(T loop,ref FixedPointIterState state,Scope sc,ref StmFlags flags){
	static if(is(T==ForExp)){
		auto range=loop.aggr.isRange;
		if(!range||!loop.loopVar) return null;
	}
	if(loop.noSplit) return null;
	static if(language==silq) if(containsDoWhile(loop.bdy)) return null;
	enum NONE=-3,LSH=-2,SHARED=-1;
	auto carried=state.prevStateSnapshot.loopParams(loop.bdy.blscope_,null,false,null);
	if(!carried[0].length) return null;
	bool[Declaration] loopState;
	foreach(q;carried[0]~carried[1]) loopState[q[1]]=true;
	// Versions of quantum variables: within a block, a variable that is defined several times at the top level
	// of the block gets fresh names for its intermediate values; its last definition in the loop body restores the name
	// (definitions in nested blocks are handled recursively: a conditional all of whose branches define the variable is a
	// definition, and other nested definitions update the current name in place). The partitioning below is by name: this allows values of
	// different classes to pass through the same variable within an iteration (e.g., with swaps). (No renaming is needed
	// to keep intermediate values alive: a quantum variable cannot be redefined before it is consumed.)
	Id[const(void)*] versionOf;
	Id vname(Identifier id){
		if(auto v=cast(const(void)*)id in versionOf) return *v;
		return varName(id);
	}
	{
		// (loop-carried and loop-local variables)
		Id[] candidates;
		SetX!Id seen;
		void candidate(Id n){
			if(n in seen) return;
			seen.insert(n);
			candidates~=n;
		}
		foreach(p;carried[0]~carried[1]){
			auto ty=typeForDecl(p[1]);
			if(ty&&!ty.isClassical()) candidate(p[1].name.id);
		}
		visitStm(loop.bdy,(Expression y){
			if(auto de=cast(DefineExp)y) visitStm(de.e1,(Expression z){
				if(auto id=cast(Identifier)z) if(!id.constLookup&&id.type&&!id.type.isClassical()) candidate(varName(id));
			});
		});
		foreach(x;candidates){
			Id[const(void)*] vers;
			bool isX(Expression e){
				auto id=cast(Identifier)e;
				return id&&varName(id)==x;
			}
			Identifier simpleDef(Expression s){ // `x` defined by a component of the left-hand side of a definition
				auto de=cast(DefineExp)s;
				if(!de||de.isSwap) return null;
				Identifier r=null;
				size_t count=0;
				visitStm(de.e1,(Expression y){ if(isX(y)) count++; });
				if(count!=1) return null;
				if(isX(de.e1)) r=cast(Identifier)de.e1;
				else if(auto tpl=cast(TupleExp)de.e1) foreach(c;tpl.e) if(isX(c)) r=cast(Identifier)c;
				return r&&!r.constLookup?r:null;
			}
			Expression[] flatten(CompoundExp b){ // (as in `addStm`)
				Expression[] r;
				void add(Expression s){
					if(auto ce=cast(CompoundExp)s) if(!ce.blscope_){
						foreach(t;ce.s) add(t);
						return;
					}
					r~=s;
				}
				foreach(s;b.s) add(s);
				return r;
			}
			// a definition of `x`, or a conditional all of whose branches define it (the branches then end with the same
			// new version)
			bool isDef(Expression s){
				if(simpleDef(s)) return true;
				auto ite=cast(IteExp)s;
				return ite&&ite.othw&&flatten(ite.then).any!(t=>isDef(t))&&flatten(ite.othw).any!(t=>isDef(t));
			}
			// `entry`/`exit`: names of `x` at the start and end of the block
			void renameBlock(CompoundExp b,Id entry,Id exit){
				void renameAll(Expression e,Id name){
					visitStmSkip(e,(Expression y){
						if(auto ce=cast(CompoundExp)y){
							renameBlock(ce,name,name);
							return false;
						}
						if(isX(y)&&name!=x) vers[cast(const(void)*)y]=name;
						return true;
					});
				}
				auto flat=flatten(b);
				auto numDefs=flat.count!(s=>isDef(s));
				assert(numDefs||entry==exit);
				Id name=entry;
				size_t j=0;
				foreach(s;flat){
					if(!isDef(s)){
						renameAll(s,name);
						continue;
					}
					auto next=++j==numDefs?exit:freshName();
					if(auto lhs=simpleDef(s)){
						renameAll((cast(DefineExp)s).e2,name);
						if(next!=x) vers[cast(const(void)*)lhs]=next;
					}else{
						auto ite=cast(IteExp)s;
						renameAll(ite.cond,name);
						renameBlock(ite.then,name,next);
						renameBlock(ite.othw,name,next);
					}
					name=next;
				}
				assert(name==exit);
			}
			renameBlock(loop.bdy,x,x);
			foreach(k,v;vers) versionOf[k]=v;
		}
	}
	bool versionCopyFailed=false;
	// copy of `e` with the versions of variables applied
	Expression vcopy(Expression e){
		auto c=e.copy();
		if(!versionOf.length) return c;
		Expression[] on,cn;
		walkShallow(e,(Expression x){ on~=x; });
		walkShallow(c,(Expression x){ cn~=x; });
		if(on.length!=cn.length){
			if(on.any!(x=>cast(const(void)*)x in versionOf)) versionCopyFailed=true; // (checked before the split is used)
			return c;
		}
		foreach(k,x;on) if(auto v=cast(const(void)*)x in versionOf) (cast(Identifier)cn[k]).id=*v;
		return c;
	}
	Dependency[] classDeps;
	int[] classOf;
	typeof(carried[0]) lifted;
	foreach(p;carried[0]){
		auto dep=state.prevStateSnapshot.dependencyOf(p[1]);
		// the lifted copies of `p` are forgotten after the loop, which requires its dependencies, and eventually theirs:
		// the transitive dependencies must not be modified by the loop (e.g., consumed by an early return within it)
		if(dep.isTop||dependsTransitivelyOnLoopState(state,sc,loopState,p[1],dep)){ // (then `p` is not lifted)
			carried[1]~=p;
			continue;
		}
		lifted~=p;
		int c=-1;
		foreach(j,ref d;classDeps) if(sameDeps(d,dep)){ c=cast(int)j; break; }
		if(c==-1){
			c=cast(int)classDeps.length;
			classDeps~=dep;
		}
		classOf~=c;
	}
	carried[0]=lifted;
	if(!carried[0].length) return null;
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
		SetX!Id defs,uses,nonConst,consumed,strong,fresh; // (`fresh`: defined by `:=`)
		MapX!(Id,Expression) types;
		bool nonQfree=false,isForget=false,effects=false;
	}
	Id[const(void)*] extracted;
	bool[const(void)*] reanalyze,isExtractAtom;
	bool hasQuantumReturn=false;
	StmInfo analyzeStm(Expression s,out bool bad){
		StmInfo info;
		info.isForget=!!cast(ForgetExp)s;
		SetX!Identifier targets;
		void strongDef(Id n){
			info.defs.insert(n);
			info.strong.insert(n);
		}
		void addDefs(Expression lhs,bool fresh){
			visitStm(lhs,(Expression x){
				if(auto ie=cast(IndexExp)x){
					Expression r=ie;
					while(cast(IndexExp)r) r=(cast(IndexExp)r).e;
					if(auto id=cast(Identifier)r) strongDef(vname(id));
				}else if(auto id=cast(Identifier)x) if(!id.constLookup){
					strongDef(vname(id));
					if(fresh) info.fresh.insert(vname(id));
					targets.insert(id);
					if(id.type) info.types[vname(id)]=id.type;
				}
			});
		}
		visitStmSkip(s,(Expression x){
			if(auto f=cast(const(void)*)x in extracted){
				info.uses.insert(*f);
				if(x.type) info.types[*f]=x.type;
				return false;
			}
			if(auto ret=cast(ReturnExp)x){
				// Loops with classically controlled early returns are not split: a separate loop computing lifted state
				// would also run the iterations after the return, which may fail or diverge where the original program does
				// not. (Such loops are rewritten without early returns first, see `erpExplicitExits`.) The code after
				// quantum-controlled returns is reachable in the original program anyway.
				auto ri=erpKey(ret) in erpReturns;
				if(!ri||!ri.quantum){
					bad=true;
					return false;
				}
				info.effects=true; // (stays in the main loop)
				hasQuantumReturn=true;
			}
			if(auto fd=cast(FunctionDef)x) if(fd.name) strongDef(fd.name.id);
			if(cast(AssertExp)x) info.effects=true;
			if(auto de=cast(DefineExp)x) addDefs(de.e1,true);
			else if(auto we=cast(WithExp)x){
				visitStm(we.trans,(Expression y){
					if(auto id=cast(Identifier)y)
						if(id.type&&!id.type.isClassical())
							strongDef(vname(id));
				});
			}else if(auto ae=cast(AAssignExp)x){
				Expression lhs=ae.e1;
				while(cast(IndexExp)lhs) lhs=(cast(IndexExp)lhs).e;
				if(auto id=cast(Identifier)lhs) strongDef(vname(id));
				else addDefs(ae.e1,false);
			}else if(auto ce=cast(CallExp)x){
				if(auto ft=cast(FunTy)ce.e.type)
					if(!ft.isSquare&&ft.annotation<Annotation.qfree) info.nonQfree=true;
			}else if(auto id=cast(Identifier)x){
				if(id in targets||cast(DatDecl)id.meaning) return true;
				auto n=vname(id);
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
			if(auto id=cast(Identifier)x) r[vname(id)]=r.get(vname(id),0)+1;
		});
		return r;
	}
	auto totalOcc=occurrences(stms);
	Expression[const(void)*] replacedBy;
	StmInfo[const(void)*] synthInfo;
	bool dceRemoved=false; // (whether the loop has dead code)
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
		foreach(i,ref info;infos) dead[i]=!info.isForget&&!info.nonQfree&&!info.effects&&info.defs.length&&cannotFail(stms[i]);
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
			dceRemoved=true;
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
			auto n=vname(id);
			if(roots.canFind(n)) return false;
			roots~=n;
		}
		foreach(k;0..lhs.e.length){
			bool ok=true;
			void check(Expression e){
				visitStm(e,(Expression x){
					if(auto id=cast(Identifier)x){
						auto n=vname(id);
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
			if(cast(CompoundExp)x||cast(IteExp)x||isLoopStatement(x)||cast(WithExp)x) simple=false;
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
					if(!simple&&(id.constLookup||id.implicitDup)&&vname(id) in rootInfo.defs) ok=false;
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
		if(auto fe=cast(ForgetExp)e) if(!fe.val&&fe.var.type&&fe.var.type.isClassical()) return; // (the split loops forget classical variables where needed)
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
			size_t[] ctx;
			foreach(ai,ref at;atoms){
				auto x=at.ites.countUntil(k);
				if(x<0) continue;
				if(f==size_t.max){
					f=ai;
					ctx=at.ites[0..x];
				}else ctx=ctx[0..commonPrefix(ctx,at.ites[0..x]).length]; // (the controls moved into loops differ between atoms)
			}
			if(f==size_t.max) continue;
			if(!it.isWith) it.first=f;
			it.ctx=ctx;
		}
	}
	bool hoistLocal(size_t q,Id t){
		if(t in isCarried) return false;
		size_t occ=0;
		walkCond(ites[q].e,false,(Expression x,bool c){
			if(auto id=cast(Identifier)x) if(vname(id)==t) occ++;
		});
		if(occ!=totalOcc.get(t,0)) return false;
		size_t[] defs;
		foreach(ai,ref at;atoms) if(at.ites.canFind(q)&&t in ainfos[ai].defs) defs~=ai;
		if(!defs.length) return false;
		foreach(ai;defs){
			auto inf=&ainfos[ai];
			if(inf.nonQfree||inf.effects||ai in isPseudo) return false;
			if(!cannotFail(atoms[ai].e)) return false; // (executed also where the original skips the branch)
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
			// (the moved classical controls are reachable in the original even where the quantum branch has amplitude zero)
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
	MapX!(Id,Declaration) invariants; // (quantum variables the loop reads but does not change)
	{
		SetX!Id defined;
		foreach(ref info;ainfos) foreach(d;info.defs) defined.insert(d);
		visitStm(loop.bdy,(Expression x){
			auto id=cast(Identifier)x;
			if(!id||!id.meaning||!id.type||id.type.isClassical()||cast(FunctionDef)id.meaning||cast(DatDecl)id.meaning) return;
			auto n=vname(id);
			if(n !in isCarried&&n !in defined) invariants[n]=id.meaning;
		});
	}
	bool rankDependsOn(int r,Declaration d){
		foreach(j;0..classDeps.length)
			if(rank[j]==r) foreach(x;classDeps[j].dependencies) if(x.canonicalSource is d.canonicalSource) return true;
		return false;
	}
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
		if(0<=c&&c<P) foreach(u;info.uses) if(auto d=invariants.get(u,null)) if(!rankDependsOn(c,d)) c=P; // (the lifted state would depend on `d`)
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
	// (the results of a main loop that is not `qfree` cannot be forgotten: it cannot log quantum values)
	bool mainNonQfree=ainfos.any!(i=>i.nonQfree)||ites.any!(it=>it.info.nonQfree);
	static if(is(T==WhileExp)) visitStm(loop.cond,(Expression x){
		if(auto ce=cast(CallExp)x) if(auto ft=cast(FunTy)ce.e.type) if(!ft.isSquare&&ft.annotation<Annotation.qfree) mainNonQfree=true;
	});
	bool logsOK(){
		if(!mainNonQfree) return true;
		foreach(a,c;atomColor) if(c>P) foreach(u;ainfos[a].uses) if(colorOf(u)==P&&!isClassicalName(u,ainfos[a])) return false;
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
					auto c=colorOf(vname(id));
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
		if(colorAtoms(false,true)&&guardOK()&&logsOK()||colorAtoms(true,true)&&guardOK()&&logsOK()||colorAtoms(false,false)&&guardOK()&&logsOK()||colorAtoms(true,false)&&guardOK()&&logsOK()) break;
		bool progress=false;
		if(lateAll) foreach(ref x;late) if(!x){ x=true; progress=true; }
		foreach(c;lateReq) if(!late[c]){ late[c]=true; progress=true; }
		if(!progress) return null;
		setupRanks();
	}
	// (a loop whose lifted state is computed by a single loop is still rewritten without its dead code: otherwise, the
	// results of the recursive function it is lowered to would depend on the quantum variables the dead code reads)
	if((atomColor.filter!(c=>c>=0).array~(atomColor.any!(c=>c>P)?[P]:[])).sort.uniq.walkLength<2&&!dceRemoved) return null;
	foreach(a,c;atomColor) if(c==P) foreach(u;ainfos[a].consumed) if(u in isCarried&&colorOf(u)>P) return null; // (the main loop runs on copies of late lifted state)
	if(hasQuantumReturn){
		// The split-off loops also run for basis states that have returned already: their computations must not fail
		// on such quantum data (e.g., a division by zero that the return guards against).
		foreach(a,c;atomColor) if(c!=P&&!cannotFail(atoms[a].e)) return null;
		foreach(ref it;ites) if(!it.heads.all!cannotFail) return null;
	}
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
				if(colorOf(vname(id))!=NONE) ok=false;
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
				auto c=colorOf(vname(id));
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
		if(cast(WhileExp)ites[j].e) return logs.any!(l=>l.dst==Y&&l.count==j); // (replayed with the logged iteration counts)
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
				auto c=colorOf(vname(id));
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
		foreach(ai,ref a;atoms) if(a.stm==i&&cast(const(void)*)a.e in isExtractAtom) // (the arguments of an extracted call)
			walkCond(a.parts[0],false,(Expression x,bool c){
				if(x !is a.parts[0]) if(auto p=cast(const(void)*)x in pos) owner[*p]=cast(int)ai;
			});
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
						auto c=colorOf(vname(id));
						if(native(c,X)) return;
						if(Y!=NONE&&c!=Y) ok=false;
						Y=c;
						vars~=vname(id);
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
						auto c=colorOf(vname(id));
						if(native(c,X)) return;
						if(Y!=NONE&&c!=Y) ok=false;
						Y=c;
						vars~=vname(id);
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
				// A late atom also runs in the main loop (on copies of the lifted state), which consumes the quantum value
				// there; the late loop could only receive a copy of it, which cannot be uncomputed after the main loop.
				if(consume&&X>P&&Y==P) return null;
				foreach(n,x;nodes) if(condOf[n]>=0&&cast(WhileExp)ites[condOf[n]].e&&inScope(n)&&x !in condCovered)
					if(auto id=cast(Identifier)x) if(vname(id)==u) return null;
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
								if(atoms[b].stm!=i||cb.length<g.rLevel||cb[0..g.rLevel]!=c0[0..g.rLevel]||atoms[b].inElse[0..g.rLevel]!=atoms[g.rAt].inElse[0..g.rLevel]) same=false;
							}
							if(!same) continue;
							auto first=g.reads[0];
							if(defPos.get(u,[]).any!(d=>first<=d&&d<n)) continue;
							auto cn=owner[n]>=0?atoms[owner[n]].ites:ites[condOf[n]].ctx;
							bool redefined=false; // (by a later iteration of a loop that the shared read is outside of)
							foreach(k;cn[min(g.rLevel,cn.length)..$]) if(ites[k].isLoop){
								auto start=pos[cast(const(void)*)ites[k].e],end=endOf(k);
								if(defPos.get(u,[]).any!(d=>start<=d&&d<end)) redefined=true;
							}
							if(redefined) continue;
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
						if(vname(id)==u&&!anchor(n)) return null;
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
					if(!rid||vname(rid)!=u) continue;
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
				if(auto id=cast(Identifier)x) if(colorOf(vname(id))!=NONE) vars~=vname(id);
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
	{ // (the logs are defined before the loop)
		SetX!Id changed;
		foreach(ref inf;ainfos) foreach(d;inf.defs) changed.insert(d);
		static if(is(T==ForExp)) changed.insert(loop.loopVar.name.id);
		foreach(ref l;logs){
			if(!l.primary||!l.type) continue;
			bool ok=true;
			l.type.freeVarsImpl((Identifier id){
				if(varName(id) in changed) ok=false;
				return 0;
			});
			if(!ok) return null;
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
			if(l.ite!=size_t.max) return dupOf(vcopy(ites[l.ite].heads[0]));
			if(!l.access) return dupOf(mkId(l.var));
			auto one=new VectorExp([dupOf(vcopy(l.access))]);
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
			Expression bound=vcopy(l.bound);
			if(l.bound is l.access.e){
				auto len=new Identifier(Id.s!"length");
				len.loc=loc;
				bound=new FieldExp(bound,len);
				bound.loc=loc;
			}
			Expression cond=new LtExp(vcopy(l.access.a),bound);
			cond.loc=loc;
			if(!isSubtype(l.access.a.type,ℕt(true))){
				auto zero=LiteralExp.makeInteger(0);
				zero.loc=loc;
				auto nonneg=new GeExp(vcopy(l.access.a),zero);
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
		// A shared atom is only replicated into the loops that use what it defines: otherwise, a loop computing lifted state
		// could read quantum variables that the lifted state does not depend on, as the results of the recursive function the
		// loop is lowered to depend on all of its arguments.
		auto neededShared=new bool[](atoms.length);
		static bool intersect(ref SetX!Id x,ref SetX!Id y){
			foreach(n;x) if(n in y) return true;
			return false;
		}
		SetX!Id evaluated; // (read by the conditions of the loops and conditionals in this loop and by the logs it writes)
		foreach(k,ref it;ites) if(hasIn(k)) foreach(u;it.info.uses) evaluated.insert(u);
		foreach(l;logs) if(l.src==X&&l.primary){
			if(l.ite!=size_t.max) foreach(u;ites[l.ite].info.uses) evaluated.insert(u);
			foreach(e;only(l.access,l.bound)) visitStm(e,(Expression x){ if(auto id=cast(Identifier)x) evaluated.insert(vname(id)); });
		}
		foreach(a;0..atoms.length){
			if(atomColor[a]!=SHARED) continue;
			auto inf=&ainfos[a];
			if(!inf.isForget&&(inf.effects||inf.nonQfree||!cannotFail(atoms[a].e))) neededShared[a]=true; // (not removed)
			foreach(l;logs) if(l.src==X&&l.var in inf.defs) neededShared[a]=true;
			if(!inf.isForget&&intersect(inf.defs,evaluated)) neededShared[a]=true;
		}
		for(bool changed=true;changed;){
			changed=false;
			foreach(a;0..atoms.length){
				if(atomColor[a]!=SHARED||neededShared[a]) continue;
				if(ainfos[a].isForget){ // (a shared forget is dropped with the shared atoms computing what it forgets)
					bool computed=false,needed=false;
					foreach(b;0..atoms.length){
						if(b==a||atomColor[b]!=SHARED||ainfos[b].isForget) continue;
						if(!intersect(ainfos[a].defs,ainfos[b].defs)) continue; // (`defs`: the forgotten variables)
						computed=true;
						needed|=neededShared[b];
					}
					if(!computed||needed){
						neededShared[a]=true;
						changed=true;
					}
					continue;
				}
				foreach(b;0..atoms.length){
					if(b==a||!keepAtom(b,X)) continue;
					if(atomColor[b]==SHARED&&(!neededShared[b]||ainfos[b].isForget)) continue; // (see above)
					if(!intersect(ainfos[a].defs,ainfos[b].uses)) continue;
					neededShared[a]=true;
					changed=true;
					break;
				}
			}
		}
		bool keepIn(size_t a,int X){
			if(!keepAtom(a,X)) return false;
			if(atomColor[a]!=SHARED) return true;
			if(!neededShared[a]) return false;
			foreach_reverse(k;atoms[a].ites) if(ites[k].isLoop) return hasIn(k);
			return true;
		}
		foreach(a;0..atoms.length){ // (a needed shared atom in a nested loop that does not run here is dropped)
			if(atomColor[a]!=SHARED||!neededShared[a]||ainfos[a].isForget||keepIn(a,X)) continue;
			auto defs=&ainfos[a].defs;
			foreach(b;0..atoms.length) if(b!=a&&keepIn(b,X)&&intersect(*defs,ainfos[b].uses)) return null;
			foreach(k,ref it;ites) if(hasIn(k)&&intersect(*defs,it.info.uses)) return null;
			foreach(l;logs) if(l.src==X&&l.var in *defs) return null;
		}
		Expression[] bdy;
		SetX!Id bodyLocals; // (defined by earlier statements)
		foreach(i,s;stms){
			Expression[] nodes;
			walkCond(s,false,(Expression x,bool c){ nodes~=x; });
			Id[const(void)*] elemOf,renameOf;
			foreach(l;logs) if(l.stm==i&&l.dst==X){
				if(l.access) elemOf[cast(const(void)*)nodes[l.node]]=l.tmp;
				else foreach(n;l.rnodes) renameOf[cast(const(void)*)nodes[n]]=l.tmp;
			}
			foreach(n;nodes) if(auto v=cast(const(void)*)n in versionOf) if(cast(const(void)*)n !in renameOf) renameOf[cast(const(void)*)n]=*v;
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
						if(cast(const(void)*)x in elemOf||cast(const(void)*)x in extracted||cast(const(void)*)x in versionOf) ok=false;
						if(auto t=cast(const(void)*)x in renameOf) if(auto id=cast(Identifier)x) names[vname(id)]=*t;
						FunctionDef fd=cast(FunctionDef)x;
						if(auto le=cast(LambdaExp)x) fd=le.fd;
						if(fd) foreach(decl;fd.capturedDecls) foreach(id;fd.captures[decl]) if(auto t=cast(const(void)*)id in renameOf) names[vname(id)]=*t;
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
							auto name=vname(id),tmp=*t;
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
						itransNames[vname(cast(Identifier)x)]=*t;
						(cast(Identifier)cn[k]).id=*t;
					}
				}
				visitStm(o,(Expression x){
					if(auto t=cast(const(void)*)x in renameOf) if(auto id=cast(Identifier)x) itransNames[vname(id)]=*t;
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
						if(keepIn(ites[chain[d]].pseudo,X)){ // (the transformation runs in this loop)
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
				foreach(d;ainfos[a].fresh){ // (classical variables that the loop body forgets explicitly)
					auto ty=ainfos[a].types.get(d,null);
					if(!ty||!ty.isClassical()||d !in isCarried&&d !in bodyLocals&&d !in topLocals&&!open.any!(f=>d in f.locals)) continue;
					auto fe=new ForgetExp(mkId(d),null);
					fe.loc=loc;
					emit(fe);
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
			if(!ok||versionCopyFailed) return null;
			bdy~=top;
			foreach(d;topLocals) bodyLocals.insert(d);
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
	// the code after a loop with quantum-controlled returns follows the main loop, which is lowered with it as its continuation
	auto cont=hasQuantumReturn?sc.loopContinuation.take(loop):null;
	stmts~=cont;
	auto split=new CompoundExp(stmts);
	split.loc=loc;
	auto before=sc.rnsymtab.dup;
	scope(success) linkLoweredVariables(sc,before);
	sc.restoreStateSnapshot(state.origStateSnapshot);
	static if(__traits(hasMember,astopt,"dumpLoops")) if(astopt.dumpLoops){
		import util.io:stderr;
		stderr.writeln(loop);
		stderr.writeln("-loop-splitting→");
		stderr.writeln(split);
	}
	auto r=statementSemantic(split,sc,flags);
	if(cont.length) sc.loopContinuation.used=true; // (after analyzing `split`, which may offer continuations itself)
	return r;
}

// statements of a loop body, for `sliceLoop`
private final class SliceNode{
	enum Kind{ atom, ite, loop, with_, block }
	Kind kind;
	Expression e;
	SliceNode[] a,b; // (branches of a conditional, bodies of loops, `with` statements and blocks)
	size_t id;
	bool quantum; // (conditional with a quantum condition)
	bool inR; // (in a quantum region, i.e., under quantum control: the main loop cannot write logs there)
	SliceNode region; // (the outermost quantum conditional containing the statement)
	// the atom, the condition, the loop header or the `with` transformation reads `uses` and `cuses`, defines `defs` and
	// `cdefs` (`strong` and `cstrong`: without reading them), and consumes `consumed` (`pconsumed`: partially)
	SetX!Id uses,defs,strong,consumed,pconsumed; // (quantum values and functions: they are recomputed)
	SetX!Id cuses,cdefs,cstrong,cfresh; // (other classical values: they are logged; `cfresh`: defined by `:=`)
	bool nonQfree;
	// classical results of calls that are not `qfree`: the main loop evaluates them before the atom and logs them
	CallExp[] extracted;
	SetX!Id xconsumed; // (consumed by the extracted calls)
	// components of a definition of a tuple of variables, which are recomputed separately
	SliceNode[] comps;
	Expression[] lhs,rhs;
	Id measured,result; // (`result:=measure(measured)`)
	MapX!(Id,Expression) ctypes; // (types of the values of `cuses`)
	Expression resultType;
	this(Kind kind,Expression e,size_t id,bool inR,SliceNode region){
		this.kind=kind; this.e=e; this.id=id; this.inR=inR; this.region=region;
	}
}

// Lowering of a loop with lifted state (loop-carried quantum variables that can be forgotten at the loop header, see
// `dependsTransitivelyOnLoopState`) by recomputation. The lifted state cannot simply be threaded through the recursive
// function of `lowerLoop`: its results depend on all of its arguments, and cannot be forgotten at all if the loop body
// is not `qfree`. Instead:
//  - a main loop runs the loop body on copies of the lifted variables and logs the classical values that the lifted
//    state depends on (at the statements that read them, or before quantum conditionals that read them); it omits the
//    statements that only compute values that neither the other loop state, nor the logs, nor any effects depend on
//  - for each class of lifted variables (with the same dependencies), a `qfree` loop recomputes them from their values
//    at the loop entry, the logs and the quantum variables that the loop does not change, using the statements of the
//    loop body that the class depends on (other lifted variables they read are recomputed from copies)
//  - the copies are forgotten using the recomputed values.
// A lifted variable can be forgotten given its dependencies, so the statements that compute it are `qfree` (apart from
// the classical values they read), and its value only depends on quantum values that are either lifted themselves or
// not changed by the loop. (The recomputing loops are not split again: their results only depend on what they read.)
// For a `do`-`while` loop, the recomputations are `do`-`while` loops whose resets run as often as those of the main loop,
// and the lifted definitions of the body that are available after the loop are recomputed as well.
Expression sliceLoop(T)(T loop,ref FixedPointIterState state,Scope sc,ref StmFlags flags){
	alias K=SliceNode.Kind;
	static if(language==silq) enum isDoWhile=is(T==DoWhileExp);
	else enum isDoWhile=false;
	static if(is(T==ForExp)){
		auto range=loop.aggr.isRange;
		if(!range||!loop.loopVar) return null;
	}
	if(loop.noSplit||containsReturn(loop.bdy)) return null;
	static if(isDoWhile){
		if(!loop.exitScope||isTrue(loop.cond)||containsReturn(loop.reset)) return null;
		bool definedInLoop(Declaration d){ // (a definition of the body, not a variable from before the loop)
			return d.derivedSequence.all!(x=>!x.scope_||x.scope_.isNestedIn(loop.bdy.blscope_));
		}
	}
	auto carried=state.prevStateSnapshot.loopParams(loop.bdy.blscope_,null,false,null);
	if(!carried[0].length&&!isDoWhile) return null;
	bool[Declaration] loopState;
	foreach(p;carried[0]~carried[1]) loopState[p[1]]=true;
	SetX!Id carriedNames,liftedNames;
	Dependency[] classDeps;
	Id[][] classVars;
	bool allLifted=true;
	foreach(p;carried[0]~carried[1]) carriedNames.insert(p[1].name.id);
	foreach(p;carried[1]) if(!typeForDecl(p[1]).isClassical()) allLifted=false;
	foreach(p;carried[0]){
		auto dep=state.prevStateSnapshot.dependencyOf(p[1]);
		if(dep.isTop||dependsTransitivelyOnLoopState(state,sc,loopState,p[1],dep)){
			allLifted=false;
			continue;
		}
		auto n=p[1].name.id;
		liftedNames.insert(n);
		size_t c=classDeps.length;
		foreach(j,ref d;classDeps) if(sameDeps(d,dep)){ c=j; break; }
		if(c==classDeps.length){
			classDeps~=dep;
			classVars~=null;
		}
		classVars[c]~=n;
	}
	static if(isDoWhile){
		// lifted definitions of the body that are available after the loop: the main loop computes copies of them, as the
		// results of its recursive function are not lifted, and the recomputations define them
		Id[][] classExits=new Id[][](classDeps.length);
		SetX!Id exitLifted;
		MapSX!(Id,Expression) exitTypes;
		foreach(d;loop.exitScope.mergedVars){
			auto decl=d.mergedInto;
			if(!decl||!decl.name||decl.name.id in carriedNames||decl.name.id in exitLifted||!definedInLoop(d)) continue;
			auto type=typeForDecl(decl);
			if(!type||type.isClassical()||!sc.canSplit(decl)||!sc.dependencyTracked(decl)) continue;
			auto dep=sc.getDependency(decl);
			if(dep.isTop) continue;
			exitLifted.insert(decl.name.id);
			exitTypes[decl.name.id]=type;
			size_t c=classDeps.length;
			foreach(j,ref cd;classDeps) if(sameDeps(cd,dep)){ c=j; break; }
			if(c==classDeps.length){
				classDeps~=dep;
				classVars~=null;
				classExits~=null;
			}
			classExits[c]~=decl.name.id;
		}
		if(!liftedNames.length&&!exitLifted.length) return null;
	}else if(!liftedNames.length) return null;
	static Id[] sorted(ref SetX!Id s){
		Id[] r;
		foreach(x;s) r~=x;
		r.sort!((a,b)=>a.str<b.str);
		return r;
	}
	// statements
	static bool nonQfreeCall(Expression x){
		if(auto ce=cast(CallExp)x) if(auto ft=cast(FunTy)ce.e.type) return !ft.isSquare&&ft.annotation<Annotation.qfree;
		return false;
	}
	static bool isVar(Identifier id){
		if(!id.meaning||cast(DatDecl)id.meaning) return false;
		if(auto fd=cast(FunctionDef)id.meaning) return !fd.isToplevelDeclaration();
		return !!cast(VarDecl)id.meaning;
	}
	static bool recomputed(Identifier id){ // (quantum values and functions are recomputed, other classical values are logged)
		if(cast(FunctionDef)id.meaning||!id.type) return true;
		return !id.type.isClassical()||!!cast(FunTy)id.type;
	}
	MapX!(Id,Declaration) invariantDecl; // (quantum variables that the loop reads)
	bool consumes(Identifier id){ return isVar(id)&&id.type&&!id.type.isClassical()&&!id.constLookup&&!id.implicitDup; }
	// calls that are not `qfree` with classical results that can be extracted from the statement `s`
	CallExp[] extractable(Expression s){
		SetX!Expression lhsNodes;
		visitStm(s,(Expression x){
			Expression l=null;
			if(auto de=cast(DefineExp)x) l=de.e1;
			else if(auto ae=cast(AAssignExp)x) l=ae.e1;
			if(l) visitStm(l,(Expression y){ lhsNodes.insert(y); });
		});
		CallExp[] calls;
		visitStmSkip(s,(Expression x){
			if(cast(LambdaExp)x||cast(FunctionDef)x||x in lhsNodes) return false;
			if(auto ce=cast(CallExp)x) if(nonQfreeCall(ce)&&ce.type&&ce.type.isClassical()&&!cast(FunTy)ce.type){
				calls~=ce;
				return false;
			}
			return true;
		});
		if(!calls.length) return null;
		// (they are evaluated before the statement: they must not consume variables that it reads otherwise; the copies of
		// the statement have to correspond to it)
		SetX!Expression inCalls;
		SetX!Id consumed;
		foreach(ce;calls) visitStm(ce,(Expression y){
			inCalls.insert(y);
			if(auto id=cast(Identifier)y) if(consumes(id)) consumed.insert(varName(id));
		});
		bool ok=true;
		visitStm(s,(Expression x){
			if(x in inCalls) return;
			if(auto id=cast(Identifier)x) if(isVar(id)&&varName(id) in consumed) ok=false;
		});
		Expression[] on,cn;
		walkShallow(s,(Expression x){ on~=x; });
		walkShallow(s.copy(),(Expression x){ cn~=x; });
		if(on.length!=cn.length) ok=false;
		foreach(ce;calls) if(!on.canFind!((x,y)=>x is y)(ce)) ok=false;
		return ok?calls:null;
	}
	void analyze(SliceNode n,Expression s,CallExp[] ext=null){
		SetX!Expression extSet;
		foreach(ce;ext) extSet.insert(ce);
		SetX!Identifier targets,partial,assigned,indexed;
		void lhs(Expression e,bool strong,bool fresh){
			if(auto id=cast(Identifier)e){
				if(id.constLookup) return;
				if(!strong) partial.insert(id);
				else if(fresh) targets.insert(id);
				else assigned.insert(id);
			}else if(auto ie=cast(IndexExp)e){
				Expression r=ie;
				while(auto ie2=cast(IndexExp)r) r=ie2.e;
				if(auto id=cast(Identifier)r) partial.insert(id);
				else lhs(r,false,false);
			}else if(auto tae=cast(TypeAnnotationExp)e) lhs(tae.e,strong,fresh);
			else if(auto tpl=cast(TupleExp)e) foreach(c;tpl.e) lhs(c,strong,fresh);
			else if(auto vec=cast(VectorExp)e) foreach(c;vec.e) lhs(c,strong,fresh);
			else if(auto cat=cast(CatExp)e){ lhs(cat.e1,strong,fresh); lhs(cat.e2,strong,fresh); }
			else if(auto ce=cast(CallExp)e) lhs(ce.arg,strong,fresh); // (reversed call)
		}
		visitStm(s,(Expression x){
			if(auto de=cast(DefineExp)x) lhs(de.e1,true,true);
			else if(auto ae=cast(AAssignExp)x) lhs(ae.e1,!!cast(AssignExp)x,false);
			else if(auto ie=cast(IndexExp)x){
				Expression r=ie;
				while(auto ie2=cast(IndexExp)r) r=ie2.e;
				if(auto id=cast(Identifier)r) indexed.insert(id);
			}
		});
		SetX!Id fresh;
		foreach(id;targets) if(isVar(id)&&!recomputed(id)) fresh.insert(varName(id));
		visitStmSkip(s,(Expression x){
			if(x in extSet){
				n.extracted~=cast(CallExp)x;
				visitStm(x,(Expression y){
					if(auto id=cast(Identifier)y) if(consumes(id)) n.xconsumed.insert(varName(id));
				});
				return false;
			}
			if(nonQfreeCall(x)) n.nonQfree=true;
			if(auto fd=cast(FunctionDef)x) if(fd.name){
				n.defs.insert(fd.name.id);
				n.strong.insert(fd.name.id);
			}
			auto id=cast(Identifier)x;
			if(!id||!isVar(id)) return true;
			auto name=varName(id);
			bool def=id in targets||id in assigned;
			if(recomputed(id)){
				if(def){
					n.defs.insert(name);
					n.strong.insert(name);
					return true;
				}
				n.uses.insert(name);
				if(id.type&&!id.type.isClassical()&&!cast(FunctionDef)id.meaning) if(name !in invariantDecl) invariantDecl[name]=id.meaning;
				if(id in partial) n.defs.insert(name);
				else if(!id.constLookup&&!id.implicitDup&&id.type&&!id.type.isClassical()){
					if(id in indexed){ // (the rest of it is still defined)
						n.defs.insert(name);
						n.pconsumed.insert(name);
					}else n.consumed.insert(name);
				}
			}else{
				if(def){
					n.cdefs.insert(name);
					n.cstrong.insert(name);
					if(id in targets) n.cfresh.insert(name);
					return true;
				}
				if(id in partial) n.cdefs.insert(name);
				if(name in fresh) return true; // (defined within the statement)
				n.cuses.insert(name);
				if(name !in n.ctypes) n.ctypes[name]=id.type;
			}
			return true;
		});
	}
	// analysis of an atom (with components for definitions of tuples of variables)
	void analyzeAtom(SliceNode n,Expression s){
		if(auto de=cast(DefineExp)s) if(auto m=cast(Identifier)de.e1) if(auto ce=cast(CallExp)de.e2) if(!ce.isSquare){
			Expression f=ce.e;
			while(cast(CallExp)f&&(cast(CallExp)f).isSquare) f=(cast(CallExp)f).e;
			auto fid=cast(Identifier)f;
			auto fd=fid?cast(FunctionDef)fid.meaning:null;
			import ast.modules:isInPrelude;
			if(fd&&isInPrelude(fd)&&fd.getName=="measure"&&isVar(m)&&m.type&&m.type.isClassical())
				if(auto u=cast(Identifier)ce.arg) if(consumes(u)){
					n.measured=varName(u);
					n.result=varName(m);
					n.resultType=m.type;
				}
		}
		auto ext=n.inR?null:extractable(s);
		auto de=cast(DefineExp)s;
		auto l=de?cast(TupleExp)de.e1:null,r=de?cast(TupleExp)de.e2:null;
		if(!de||de.isSwap||!l||!r||l.e.length!=r.e.length||l.e.length<2||!l.e.all!(x=>cast(Identifier)x&&!x.constLookup)){
			analyze(n,s,ext);
			return;
		}
		foreach(j;0..l.e.length){
			auto c=new SliceNode(K.atom,r.e[j],0,n.inR,n.region);
			analyze(c,r.e[j],ext);
			auto id=cast(Identifier)l.e[j];
			if(isVar(id)){
				auto name=varName(id);
				if(recomputed(id)){
					c.defs.insert(name);
					c.strong.insert(name);
				}else{
					c.cdefs.insert(name);
					c.cstrong.insert(name);
					c.cfresh.insert(name);
				}
			}
			n.comps~=c;
			n.lhs~=l.e[j];
			n.rhs~=r.e[j];
			foreach(x;only(&n.uses,&n.defs,&n.strong,&n.consumed,&n.pconsumed,&n.cuses,&n.cdefs,&n.cstrong,&n.cfresh,&n.xconsumed).zip(only(&c.uses,&c.defs,&c.strong,&c.consumed,&c.pconsumed,&c.cuses,&c.cdefs,&c.cstrong,&c.cfresh,&c.xconsumed)))
				foreach(v;*x[1]) x[0].insert(v);
			foreach(u,t;c.ctypes) if(u !in n.ctypes) n.ctypes[u]=t;
			n.nonQfree|=c.nonQfree;
			n.extracted~=c.extracted;
		}
	}
	// analysis of a sequence of statements (`strong`: defined by it, for a `with` transformation)
	void analyzeSeq(SliceNode n,Expression[] stms,bool isAtom){
		SetX!Id defined,cdefined,touched,firstStrong;
		foreach(t;stms){
			auto x=new SliceNode(K.atom,t,0,n.inR,n.region);
			analyze(x,t);
			foreach(u;x.uses) if(u !in defined) n.uses.insert(u);
			foreach(u;x.consumed) if(u !in defined) n.consumed.insert(u);
			foreach(u;x.pconsumed) if(u !in defined) n.pconsumed.insert(u);
			foreach(u;x.cuses) if(u !in cdefined){
				n.cuses.insert(u);
				if(u !in n.ctypes) n.ctypes[u]=x.ctypes[u];
			}
			foreach(d;x.strong) if(d !in touched) firstStrong.insert(d);
			foreach(u;x.consumed) defined.remove(u);
			foreach(d;x.defs) if(d !in x.consumed||d in x.strong) defined.insert(d);
			foreach(u;x.uses) touched.insert(u);
			foreach(d;x.defs) touched.insert(d);
			foreach(d;x.cdefs){
				cdefined.insert(d);
				n.cdefs.insert(d);
			}
			foreach(d;x.cstrong) n.cstrong.insert(d);
			foreach(d;x.cfresh) n.cfresh.insert(d);
			n.nonQfree|=x.nonQfree;
		}
		foreach(d;defined){
			n.defs.insert(d);
			if(!isAtom||d in firstStrong) n.strong.insert(d);
		}
		foreach(d;n.pconsumed) n.defs.insert(d);
	}
	SliceNode[] nodes;
	SetX!Id loopVarNames; // (variables of nested `for` loops)
	bool unsupported=false;
	SliceNode[] build(Expression[] stms,bool inR,SliceNode region){
		SliceNode[] r;
		SliceNode mk(K kind,Expression e){
			auto n=new SliceNode(kind,e,nodes.length,inR,region);
			nodes~=n;
			r~=n;
			return n;
		}
		void add(Expression s){
			static if(language==silq) if(auto dw=cast(DoWhileExp)s){ // (`a`: the body, `b`: the reset)
				auto n=mk(K.loop,s);
				analyze(n,dw.cond);
				n.a=build(dw.bdy.s,inR,region);
				if(dw.reset) n.b=build(dw.reset.s,inR,region);
				return;
			}
			if(auto ce=cast(CompoundExp)s){
				if(!ce.blscope_){
					foreach(t;ce.s) add(t);
					return;
				}
				auto n=mk(K.block,s);
				n.a=build(ce.s,inR,region);
			}else if(auto ite=cast(IteExp)s){
				auto n=mk(K.ite,s);
				n.quantum=!(ite.cond.type&&ite.cond.type.isClassical());
				analyze(n,ite.cond);
				auto nregion=region?region:n.quantum?n:null;
				n.a=build(ite.then.s,inR||n.quantum,nregion);
				if(ite.othw) n.b=build(ite.othw.s,inR||n.quantum,nregion);
			}else if(auto fe=cast(ForExp)s){
				auto rng=fe.aggr.isRange;
				if(!rng||!fe.loopVar){
					unsupported=true;
					return;
				}
				auto n=mk(K.loop,s);
				analyze(n,rng.left);
				if(rng.step) analyze(n,rng.step);
				analyze(n,rng.right);
				loopVarNames.insert(fe.loopVar.name.id);
				n.a=build(fe.bdy.s,inR,region);
			}else if(auto re=cast(RepeatExp)s){
				auto n=mk(K.loop,s);
				analyze(n,re.num);
				n.a=build(re.bdy.s,inR,region);
			}else if(auto we=cast(WhileExp)s){
				auto n=mk(K.loop,s);
				analyze(n,we.cond);
				n.a=build(we.bdy.s,inR,region);
			}else if(auto we=cast(WithExp)s){
				if(we.isIndices){ // (replacement of components: an atom)
					auto n=mk(K.atom,s);
					analyzeSeq(n,we.trans.s~we.bdy.s~(we.itrans?we.itrans.s:[]),true);
					return;
				}
				// (the transformation is kept as a whole)
				auto n=mk(K.with_,s);
				analyzeSeq(n,we.trans.s,false);
				n.a=build(we.bdy.s,inR,region);
			}else{
				auto n=mk(K.atom,s);
				analyzeAtom(n,s);
			}
		}
		foreach(s;stms) add(s);
		return r;
	}
	auto body_=build(loop.bdy.s,false,null);
	static if(isDoWhile) auto reset_=build(loop.reset.s,false,null); // (runs after the condition, before each further iteration)
	else SliceNode[] reset_=null;
	if(unsupported) return null;
	SetX!Id bodyDefs; // (names that the loop body changes)
	foreach(n;nodes){
		foreach(d;n.defs) bodyDefs.insert(d);
		foreach(d;n.consumed) bodyDefs.insert(d);
		foreach(d;n.cdefs) bodyDefs.insert(d);
	}
	foreach(v;loopVarNames) bodyDefs.insert(v);
	static if(is(T==ForExp)){
		auto mainVar=loop.loopVar.name.id;
		if(mainVar in bodyDefs) return null;
	}
	static if(is(T==WhileExp)||isDoWhile){
		auto cnode=new SliceNode(K.atom,loop.cond,0,false,null);
		analyze(cnode,loop.cond);
		if(cnode.consumed.length||cnode.pconsumed.length) return null; // (the recomputation does not evaluate the condition)
	}
	// classical values that the recomputation can read directly (the others are logged or, in quantum regions, recomputed)
	bool available(Id u){
		static if(is(T==ForExp)) if(u==mainVar) return true;
		return u in loopVarNames||u !in bodyDefs;
	}
	// (the whole loop is lowered precisely if its body is `qfree` and only carries the lifted state of a single class
	// whose dependencies include all quantum variables that the loop reads)
	{
		bool bodyQfree=!nodes.any!(n=>n.nonQfree||n.extracted.length);
		static if(is(T==WhileExp)||isDoWhile) bodyQfree&=!cnode.nonQfree;
		if(bodyQfree&&allLifted&&classDeps.length==1){
			bool precise=true;
			foreach(u,d;invariantDecl){
				if(u in bodyDefs) continue;
				bool found=false;
				foreach(x;classDeps[0].dependencies) if(x.canonicalSource is d.canonicalSource) found=true;
				if(!found) precise=false;
			}
			if(precise) return null;
		}
	}
	SetX!Id[] regionLocal=new SetX!Id[](nodes.length); // (classical variables that a quantum region defines)
	foreach(n;nodes) if(n.region) foreach(d;n.cfresh) regionLocal[n.region.id].insert(d);
	// consumption within statements (for statements that are not part of a recomputation)
	SetX!Id[] subConsumed=new SetX!Id[](nodes.length);
	SetX!Id consumedIn(SliceNode n){
		auto r=n.consumed.dup;
		foreach(u;n.xconsumed) r.insert(u);
		foreach(c;n.a~n.b) foreach(u;consumedIn(c)) r.insert(u);
		subConsumed[n.id]=r.dup;
		return r;
	}
	foreach(n;body_~reset_) consumedIn(n);
	// backward slicing for each class
	struct Live{ SetX!Id q,c; } // (names whose values are needed: `c` for classical values in quantum regions)
	static Live dupL(Live l){ return Live(l.q.dup,l.c.dup); }
	static Live joinL(Live x,Live y){
		auto r=dupL(x);
		foreach(v;y.q) r.q.insert(v);
		foreach(v;y.c) r.c.insert(v);
		return r;
	}
	static bool eqL(ref Live x,ref Live y){ return x.q==y.q&&x.c==y.c; }
	struct Slice{
		size_t cls;
		bool[] kept;
		SetX!Id[] entryLogs; // (classical values that quantum regions and `with` transformations read)
		SetX!Id[] disp,dispAfter; // (values to forget before or after the statement: what the original computation consumes)
		bool[][] compKept; // (recomputed components of atoms)
		bool[] measDisp; // (the value consumed by a measurement is forgotten using its logged result)
		SetX!Id carried; // (the class and the other lifted variables it reads)
		SetX!Id locals; // (carried variables whose values the recomputation only needs within iterations)
		Q!(Id,Expression)[][] reads; // (logged classical values that the recomputation reads before the statements)
	}
	Slice S;
	bool fwdFailed=false;
	SetX!Id droppedDefs; // (values that statements which are not part of the recomputation change)
	bool anyKept(SliceNode[] ns){ return ns.any!(c=>S.kept[c.id]); }
	Live backNode(SliceNode n,Live live){
		Live back(SliceNode[] ns,Live l){
			foreach_reverse(c;ns) l=backNode(c,l);
			return l;
		}
		final switch(n.kind){
			case K.atom:{
				if(n.comps.length){
					auto ck=new bool[](n.comps.length);
					foreach(j,c;n.comps){
						foreach(d;c.defs) if(d in live.q) ck[j]=true;
						if(n.inR) foreach(d;c.cdefs) if(d in live.c) ck[j]=true;
					}
					if(!ck.any) return live;
					S.kept[n.id]=true;
					S.compKept[n.id]=ck;
					auto r=dupL(live);
					foreach(c;n.comps){
						foreach(d;c.strong) r.q.remove(d);
						foreach(d;c.cstrong) r.c.remove(d);
					}
					foreach(j,c;n.comps) if(ck[j]){
						foreach(u;c.uses) r.q.insert(u);
						if(n.inR) foreach(u;c.cuses) if(!available(u)) r.c.insert(u);
					}
					return r;
				}
				bool k=false;
				foreach(d;n.defs) if(d in live.q) k=true;
				if(n.inR) foreach(d;n.cdefs) if(d in live.c) k=true;
				if(!k) return live;
				S.kept[n.id]=true;
				auto r=dupL(live);
				foreach(d;n.strong) r.q.remove(d);
				foreach(d;n.cstrong) r.c.remove(d);
				foreach(u;n.uses) r.q.insert(u);
				if(n.inR) foreach(u;n.cuses) if(!available(u)) r.c.insert(u);
				return r;
			}
			case K.ite:{
				auto lt=back(n.a,dupL(live)),le=back(n.b,dupL(live));
				if(!anyKept(n.a)&&!anyKept(n.b)) return live;
				S.kept[n.id]=true;
				auto r=joinL(lt,le);
				if(n.quantum||n.inR){ // (otherwise, the condition is logged)
					foreach(u;n.uses) r.q.insert(u);
					foreach(u;n.cuses) if(!available(u)) r.c.insert(u);
				}
				if(n.quantum&&!n.inR){
					S.entryLogs[n.id]=r.c;
					r.c=SetX!Id.init;
				}
				return r;
			}
			case K.loop:{
				static if(language==silq) if(cast(DoWhileExp)n.e){ // (`a`: the body, after which the loop exits, `b`: the reset)
					auto lx=dupL(live); // (needed after the body)
					if(n.inR){ // (otherwise, the number of iterations is logged)
						foreach(u;n.uses) lx.q.insert(u);
						foreach(u;n.cuses) if(!available(u)) lx.c.insert(u);
					}
					Live ls; // (needed at the start of the body)
					for(;;){
						auto ls2=joinL(ls,back(n.a,joinL(lx,back(n.b,dupL(ls)))));
						if(eqL(ls2,ls)) break;
						ls=ls2;
					}
					if(!anyKept(n.a)&&!anyKept(n.b)) return live;
					S.kept[n.id]=true;
					return ls;
				}
				auto lc=dupL(live); // (needed at the end of the body)
				if(n.inR&&cast(WhileExp)n.e){ // (the condition is evaluated after each iteration)
					foreach(u;n.uses) lc.q.insert(u);
					foreach(u;n.cuses) if(!available(u)) lc.c.insert(u);
				}
				auto le=dupL(lc);
				Live ls;
				for(;;){
					ls=back(n.a,dupL(le));
					auto le2=joinL(lc,ls);
					if(eqL(le2,le)) break;
					le=le2;
				}
				if(!anyKept(n.a)) return live;
				S.kept[n.id]=true;
				auto r=le;
				if(n.inR){ // (otherwise, the header is logged)
					foreach(u;n.uses) r.q.insert(u);
					foreach(u;n.cuses) if(!available(u)) r.c.insert(u);
				}
				return r;
			}
			case K.with_:{
				// (the inverse transformation consumes what the transformation defines, to restore what it consumes)
				bool restores=false;
				foreach(u;n.consumed) if(u in live.q) restores=true;
				foreach(u;n.pconsumed) if(u in live.q) restores=true;
				auto lb=dupL(live);
				if(restores) foreach(d;n.strong) lb.q.insert(d);
				auto ls=back(n.a,lb);
				if(!anyKept(n.a)) return live;
				if(!restores){
					lb=dupL(live);
					foreach(d;n.strong) lb.q.insert(d);
					ls=back(n.a,lb);
				}
				S.kept[n.id]=true;
				auto r=ls;
				foreach(d;n.strong) r.q.remove(d);
				foreach(d;n.cdefs) r.c.remove(d);
				foreach(u;n.uses) r.q.insert(u);
				SetX!Id cl;
				foreach(u;n.cuses) if(!available(u)) cl.insert(u);
				if(n.inR) foreach(u;cl) r.c.insert(u);
				else S.entryLogs[n.id]=cl;
				return r;
			}
			case K.block:{
				auto r=back(n.a,dupL(live));
				if(!anyKept(n.a)) return live;
				S.kept[n.id]=true;
				return r;
			}
		}
	}
	// forward pass: values that the recomputation computes but the original computation consumes in statements that are
	// not part of the recomputation are forgotten there
	SetX!Id fwdNode(SliceNode n,SetX!Id avail){
		SetX!Id fwd(SliceNode[] ns,SetX!Id l){
			foreach(c;ns) l=fwdNode(c,l);
			return l;
		}
		S.disp[n.id]=SetX!Id.init;
		S.dispAfter[n.id]=SetX!Id.init;
		void dispose(ref SetX!Id names,bool after=false){
			SetX!Id d;
			foreach(u;names) if(u in avail) d.insert(u);
			foreach(u;d){
				(after?S.dispAfter:S.disp)[n.id].insert(u);
				avail.remove(u);
			}
		}
		if(!S.kept[n.id]){
			dispose(subConsumed[n.id]);
			// (the recomputed value is the measured one unless other statements change it)
			S.measDisp[n.id]=n.measured!=Id.init&&n.measured in S.disp[n.id]&&n.measured !in droppedDefs;
			return avail;
		}
		final switch(n.kind){
			case K.atom:
				if(n.comps.length){
					// (what the components that are not recomputed consume is forgotten after the atom, unless another
					// component redefines it)
					auto ck=S.compKept[n.id];
					SetX!Id before,after,redefined,read;
					foreach(j,c;n.comps) if(ck[j]){
						foreach(d;c.strong) redefined.insert(d);
						foreach(u;c.uses) read.insert(u);
						foreach(u;c.xconsumed) before.insert(u);
					}
					foreach(j,c;n.comps) if(!ck[j]) foreach(cs;only(&c.consumed,&c.xconsumed)) foreach(u;*cs){
						if(u !in redefined) after.insert(u);
						else if(u in read&&u in avail) fwdFailed=true;
						else before.insert(u);
					}
					dispose(before);
					foreach(j,c;n.comps) if(ck[j]) foreach(u;c.consumed) avail.remove(u);
					foreach(j,c;n.comps) if(ck[j]) foreach(d;c.defs) if(d !in c.consumed||d in c.strong) avail.insert(d);
					dispose(after,true);
					return avail;
				}
				dispose(n.xconsumed);
				foreach(u;n.consumed) avail.remove(u);
				foreach(d;n.defs) if(d !in n.consumed||d in n.strong) avail.insert(d);
				return avail;
			case K.ite:{
				if(n.quantum||n.inR) foreach(u;n.consumed) avail.remove(u);
				else dispose(n.consumed);
				auto at=fwd(n.a,avail.dup),ae=fwd(n.b,avail.dup);
				SetX!Id r;
				foreach(u;at) if(u in ae) r.insert(u);
				return r;
			}
			case K.loop:{
				if(n.inR) foreach(u;n.consumed) avail.remove(u);
				else dispose(n.consumed);
				auto entry=avail.dup;
				static if(language==silq) if(cast(DoWhileExp)n.e){
					for(;;){
						auto exit=fwd(n.a,entry.dup);
						auto end=fwd(n.b,exit.dup);
						SetX!Id lost;
						foreach(u;entry) if(u !in end) lost.insert(u);
						if(!lost.length) return exit;
						foreach(u;lost){
							S.disp[n.id].insert(u);
							entry.remove(u);
						}
					}
				}
				for(;;){
					auto end=fwd(n.a,entry.dup);
					SetX!Id lost;
					foreach(u;entry) if(u !in end) lost.insert(u);
					if(!lost.length) break;
					foreach(u;lost){
						S.disp[n.id].insert(u);
						entry.remove(u);
					}
				}
				return entry;
			}
			case K.with_:
				foreach(u;n.consumed) avail.remove(u);
				foreach(d;n.strong) avail.insert(d);
				avail=fwd(n.a,avail);
				foreach(d;n.strong) avail.remove(d);
				foreach(u;n.consumed) avail.insert(u);
				return avail;
			case K.block:{
				auto inner=fwd(n.a,avail.dup);
				SetX!Id r;
				foreach(u;inner) if(u in avail) r.insert(u);
				return r;
			}
		}
	}
	Live back(SliceNode[] ns,Live live){
		foreach_reverse(n;ns) live=backNode(n,live);
		return live;
	}
	SetX!Id fwd(SliceNode[] ns,SetX!Id avail){
		foreach(n;ns) avail=fwdNode(n,avail);
		return avail;
	}
	Live backIteration(size_t cls,Live le){ // (needed at the start of an iteration, from what is needed at its end)
		static if(isDoWhile){
			auto lx=back(reset_,le);
			foreach(v;classVars[cls]~classExits[cls]) lx.q.insert(v); // (the loop exits after the body)
			return back(body_,lx);
		}else return back(body_,le);
	}
	Slice[] slices;
	bool sliceClass(size_t cls){
		fwdFailed=false;
		S=Slice(cls,new bool[](nodes.length),new SetX!Id[](nodes.length),new SetX!Id[](nodes.length),new SetX!Id[](nodes.length),new bool[][](nodes.length),new bool[](nodes.length));
		Live le;
		foreach(v;classVars[cls]) le.q.insert(v);
		for(;;){
			auto ls=backIteration(cls,dupL(le));
			auto le2=dupL(le);
			foreach(v;ls.q) if(v in carriedNames) le2.q.insert(v);
			if(eqL(le2,le)) break;
			le=le2;
		}
		S.kept[]=false;
		S.entryLogs=new SetX!Id[](nodes.length);
		S.compKept=new bool[][](nodes.length);
		auto ls=backIteration(cls,dupL(le));
		foreach(v;le.q) if(v !in liftedNames) return false; // (the class depends on a carried variable that is not lifted)
		foreach(v;ls.q) if(v in bodyDefs&&v !in liftedNames) return false;
		if(ls.c.length) return false;
		S.carried=le.q.dup;
		foreach(n;nodes){
			if(!S.kept[n.id]) continue;
			final switch(n.kind){
				case K.atom:
					foreach(c;n.comps.length?n.comps.zip(S.compKept[n.id]).filter!(x=>x[1]).map!(x=>x[0]).array:[n]){
						if(c.nonQfree) return false;
						if(n.inR){
							foreach(d;c.cdefs) if(d !in regionLocal[n.region.id]) return false;
						}else foreach(d;c.cdefs) if((d !in c.cuses||available(d))&&(d in carriedNames||d !in c.cfresh)) return false; // (values read from the logs can be changed)
					}
					break;
				case K.ite:
					if((n.quantum||n.inR)&&n.nonQfree) return false;
					if(n.quantum&&!n.inR) foreach(u;S.entryLogs[n.id]) if(u in regionLocal[n.id]) return false;
					break;
				case K.loop:
					if(n.inR&&n.nonQfree) return false;
					if(n.consumed.length||n.pconsumed.length) return false;
					break;
				case K.with_:
					if(n.nonQfree) return false;
					foreach(d;n.cdefs) if(d !in n.cfresh&&(n.inR||d !in n.cuses||available(d))) return false;
					break;
				case K.block:
					break;
			}
		}
		foreach(n;nodes) if(S.kept[n.id]) foreach(d;n.strong) if(d in carriedNames&&d !in S.carried) S.locals.insert(d);
		droppedDefs=SetX!Id.init;
		foreach(n;nodes){
			if(n.kind!=K.atom&&n.kind!=K.with_) continue;
			if(!S.kept[n.id]) foreach(d;n.defs) droppedDefs.insert(d);
			else foreach(j,c;n.comps) if(!S.compKept[n.id][j]) foreach(d;c.defs) droppedDefs.insert(d);
		}
		static if(isDoWhile){
			auto exit=fwd(body_,S.carried.dup);
			foreach(v;S.carried) if(v !in exit) return false; // (the recomputation exits after the body as well)
			foreach(v;classExits[cls]) if(v !in exit) return false;
			auto end=fwd(reset_,exit);
		}else auto end=fwd(body_,S.carried.dup);
		if(fwdFailed) return false;
		foreach(v;S.carried) if(v !in end) return false;
		slices~=S;
		return true;
	}
	foreach(cls;0..classDeps.length){
		if(sliceClass(cls)) continue;
		static if(isDoWhile) if(classExits[cls].length){ // (the main loop computes these definitions instead)
			foreach(v;classExits[cls]) exitLifted.remove(v);
			classExits[cls]=null;
			if(!classVars[cls].length||sliceClass(cls)) continue;
		}
		return null;
	}
	if(!slices.length) return null;
	// logs
	enum LogKey{ value, call, cond, left, step, right, num, count, measurement }
	struct Log{
		size_t node;
		LogKey key;
		Id var,name;
		Expression type,stored;
		size_t idx; // (of an extracted call)
	}
	Log[] logs;
	size_t logOf(size_t node,LogKey key,Id var,Expression type,size_t idx=0){
		foreach(i,ref l;logs) if(l.node==node&&l.key==key&&l.var==var&&l.idx==idx) return i;
		logs~=Log(node,key,var,freshName(),type,null,idx);
		return logs.length-1;
	}
	// (the recomputed parts of an atom)
	SliceNode[] keptParts(SliceNode n,ref Slice sl){
		if(!n.comps.length) return [n];
		SliceNode[] r;
		foreach(j,c;n.comps) if(sl.compKept[n.id][j]) r~=c;
		return r;
	}
	// (classical conditions and loop headers that only read values that the loop does not change are not logged: the
	// recomputations evaluate them as well)
	bool direct(Expression e){
		auto t=new SliceNode(K.atom,e,0,false,null);
		analyze(t,e);
		if(t.uses.length||t.defs.length||t.consumed.length||t.pconsumed.length||t.cdefs.length||t.nonQfree) return false;
		foreach(u;t.cuses) if(!available(u)) return false;
		return true;
	}
	SetX!Id[] writesOf=new SetX!Id[](nodes.length); // (classical values that the statements change)
	SetX!Id writes(SliceNode n){
		auto r=n.cdefs.dup;
		foreach(c;n.a~n.b) foreach(u;writes(c)) r.insert(u);
		writesOf[n.id]=r.dup;
		return r;
	}
	foreach(n;body_~reset_) writes(n);
	// (logged values that the type `t` mentions)
	Q!(Id,Expression)[] typeVars(Expression t){
		Q!(Id,Expression)[] r;
		t.freeVarsImpl((Identifier id){
			auto v=varName(id);
			if(isVar(id)&&!available(v)&&id.type&&!r.canFind!(x=>x[0]==v)) r~=q(v,id.type);
			return 0;
		});
		return r;
	}
	// (classical values that the recomputation of `n` reads from before `n` and cannot read directly, with their types)
	MapX!(Id,Expression) readBefore(SliceNode n){
		MapX!(Id,Expression) r;
		if(!S.kept[n.id]) return r;
		void add(SliceNode c,Id u){ if(!available(u)&&u !in r) r[u]=c.ctypes[u]; }
		void seq(SliceNode[] ns,SetX!Id killed){
			killed=killed.dup;
			foreach(c;ns){
				foreach(u,t;readBefore(c)) if(u !in killed&&u !in r) r[u]=t;
				foreach(u;writesOf[c.id]) killed.insert(u);
			}
		}
		final switch(n.kind){
			case K.atom:
				foreach(c;n.inR?[n]:keptParts(n,S)) foreach(u;c.cuses) add(c,u);
				break;
			case K.ite:
				if(n.quantum||n.inR) foreach(u;n.cuses) add(n,u);
				seq(n.a,SetX!Id.init);
				seq(n.b,SetX!Id.init);
				break;
			case K.loop:{
				if(n.inR) foreach(u;n.cuses) add(n,u);
				SetX!Id changed;
				if(!n.inR) foreach(c;n.a~n.b) foreach(u;writesOf[c.id]) changed.insert(u); // (read in each iteration)
				seq(n.a~n.b,changed);
				break;
			}
			case K.with_:
				foreach(u;n.cuses) add(n,u);
				seq(n.a,n.cdefs);
				break;
			case K.block:
				seq(n.a,SetX!Id.init);
				break;
		}
		return r;
	}
	foreach(ref sl;slices){
		S=sl;
		auto otherTypes=new Expression[][](nodes.length); // (of the logs other than values)
		void other(size_t node,LogKey key,Id var,Expression type,size_t idx=0){
			logOf(node,key,var,type,idx);
			otherTypes[node]~=type;
		}
		foreach(n;nodes){
			if(sl.measDisp[n.id]) other(n.id,LogKey.measurement,n.result,n.resultType);
			if(!sl.kept[n.id]||n.inR) continue;
			final switch(n.kind){
				case K.atom:
					foreach(c;keptParts(n,sl)) foreach(ce;c.extracted) other(n.id,LogKey.call,Id.init,ce.type,n.extracted.countUntil!((x,y)=>x is y)(ce));
					break;
				case K.ite:
					if(!n.quantum&&!direct((cast(IteExp)n.e).cond)) other(n.id,LogKey.cond,Id.init,Bool(true));
					break;
				case K.loop:
					if(auto fe=cast(ForExp)n.e){
						auto rng=fe.aggr.isRange;
						if(!direct(rng.left)) other(n.id,LogKey.left,Id.init,rng.left.type);
						if(rng.step&&!direct(rng.step)) other(n.id,LogKey.step,Id.init,rng.step.type);
						if(!direct(rng.right)) other(n.id,LogKey.right,Id.init,rng.right.type);
					}else if(auto re=cast(RepeatExp)n.e){
						if(!direct(re.num)) other(n.id,LogKey.num,Id.init,re.num.type);
					}else other(n.id,LogKey.count,Id.init,ℕt(true));
					break;
				case K.with_,K.block:
					break;
			}
		}
		// (each version of a value is read once, before the outermost statement that reads it: types mentioning it agree)
		sl.reads=new Q!(Id,Expression)[][](nodes.length);
		void plan(SliceNode[] ns,SetX!Id have){
			have=have.dup;
			foreach(n;ns){
				Q!(Id,Expression)[] rd;
				SetX!Id seen;
				void visit(Id u,Expression t){
					if(!t||u in have||u in seen) return;
					seen.insert(u);
					foreach(v;typeVars(t)) visit(v[0],v[1]);
					rd~=q(u,t);
				}
				if(sl.kept[n.id]&&!n.inR){
					auto rb=readBefore(n);
					Id[] us;
					foreach(u,_;rb) us~=u;
					us.sort!((a,b)=>a.str<b.str);
					foreach(u;us) visit(u,rb[u]);
				}
				foreach(t;otherTypes[n.id]) foreach(v;typeVars(t)) visit(v[0],v[1]);
				sl.reads[n.id]=rd;
				foreach(x;rd){
					have.insert(x[0]);
					logOf(n.id,LogKey.value,x[0],x[1]);
				}
				if(sl.kept[n.id]&&!n.inR) final switch(n.kind){
					case K.atom: break;
					case K.ite:
						if(!n.quantum){
							plan(n.a,have);
							plan(n.b,have);
						}
						break;
					case K.loop:{
						auto h=have.dup;
						foreach(c;n.a~n.b) foreach(u;writesOf[c.id]) h.remove(u);
						plan(n.a~n.b,h);
						break;
					}
					case K.with_:{
						auto h=have.dup;
						foreach(u;n.cdefs) h.remove(u);
						plan(n.a,h);
						break;
					}
					case K.block:
						plan(n.a,have);
						break;
				}
				foreach(u;writesOf[n.id]) have.remove(u);
			}
		}
		plan(body_~reset_,SetX!Id.init);
	}
	// (the logs are defined before the loop: types mentioning values that the loop changes are weakened, and so are other
	// types mentioning variables where possible, as enclosing loops may change them)
	bool mentions(Expression t,bool onlyChanged){
		bool r=false;
		t.freeVarsImpl((Identifier id){
			auto v=varName(id);
			if(!onlyChanged&&isVar(id)||v in bodyDefs) r=true;
			static if(is(T==ForExp)) if(v==mainVar) r=true;
			return 0;
		});
		return r;
	}
	Expression weakened(Expression t){
		if(!mentions(t,false)) return t;
		if(auto ft=isFixedIntTy(t)) return ft.isSigned?ℤt(true):ℕt(true);
		Expression elem(Expression e){
			auto w=weakened(e);
			return w?arrayTy(w):null;
		}
		if(auto vt=cast(VectorTy)t) return elem(vt.next);
		if(auto at=cast(ArrayTy)t) return elem(at.next);
		if(auto tt=cast(TupleTy)t){
			Expression[] ws;
			foreach(c;tt.types){
				auto w=weakened(c);
				if(!w) return null;
				ws~=w;
			}
			return tupleTy(ws);
		}
		return null;
	}
	foreach(ref l;logs){
		if(!l.type||!l.type.isClassical()) return null;
		l.stored=weakened(l.type);
		if(!l.stored){
			if(mentions(l.type,true)) return null;
			l.stored=l.type;
		}
	}
	size_t[][] logsAt=new size_t[][](nodes.length);
	foreach(i,ref l;logs) logsAt[l.node]~=i;
	auto hasLogs=new bool[](nodes.length); // (in the subtree)
	bool computeHasLogs(SliceNode n){
		bool r=logsAt[n.id].length!=0;
		foreach(c;n.a~n.b) r|=computeHasLogs(c);
		return hasLogs[n.id]=r;
	}
	foreach(n;body_~reset_) computeHasLogs(n);
	// statements that the main loop keeps: they may fail, have effects or change values that the loop state that is not
	// lifted or the logs depend on (the lifted variables that no kept statement accesses are not copied)
	auto mayFail=new bool[](nodes.length); // (the atom, the condition, the loop header or the transformation)
	foreach(n;nodes){
		final switch(n.kind){
			case K.atom: mayFail[n.id]=!cannotFail(n.e); break;
			case K.ite: mayFail[n.id]=!cannotFail((cast(IteExp)n.e).cond); break;
			case K.loop:
				if(auto fe=cast(ForExp)n.e){
					auto rng=fe.aggr.isRange;
					mayFail[n.id]=!cannotFail(rng.left)||rng.step&&!cannotFail(rng.step)||!cannotFail(rng.right);
				}else if(auto re=cast(RepeatExp)n.e) mayFail[n.id]=!cannotFail(re.num);
				else mayFail[n.id]=true; // (it may diverge)
				break;
			case K.with_:{
				auto we=cast(WithExp)n.e;
				mayFail[n.id]=!cannotFail(we.trans)||we.itrans&&!cannotFail(we.itrans);
				break;
			}
			case K.block: break;
		}
	}
	auto mKept=new bool[](nodes.length);
	SetX!Id mLive;
	{
		foreach(v;carriedNames) if(v !in liftedNames) mLive.insert(v);
		foreach(ref l;logs) if(l.var!=Id.init) mLive.insert(l.var);
		static if(is(T==WhileExp)||isDoWhile) foreach(s;only(&cnode.uses,&cnode.cuses)) foreach(u;*s) mLive.insert(u);
		static if(isDoWhile) foreach(d;loop.exitScope.mergedVars) if(d.mergedInto&&d.mergedInto.name) mLive.insert(d.mergedInto.name.id); // (available after the loop)
		bool changed=true;
		void add(Id u){
			if(u in mLive) return;
			mLive.insert(u);
			changed=true;
		}
		bool mark(SliceNode n){
			bool k=false;
			foreach(c;n.a~n.b) k|=mark(c)||hasLogs[c.id];
			bool writes=false,writesLive=false;
			foreach(s;only(&n.defs,&n.consumed,&n.pconsumed,&n.cdefs,&n.xconsumed)) foreach(u;*s){
				writes=true;
				if(u in mLive) writesLive=true;
			}
			foreach(li;logsAt[n.id]) if(logs[li].key!=LogKey.value) k=true;
			final switch(n.kind){
				case K.atom: k|=n.nonQfree||n.extracted.length||!writes||writesLive; break;
				case K.ite,K.loop: k|=n.nonQfree||writesLive; break;
				case K.with_,K.block: break; // (a transformation without a body is undone)
			}
			k|=mayFail[n.id];
			if(k&&!mKept[n.id]){
				mKept[n.id]=true;
				changed=true;
				foreach(s;only(&n.uses,&n.defs,&n.consumed,&n.pconsumed,&n.cuses,&n.cdefs,&n.xconsumed)) foreach(u;*s) add(u);
				foreach(ce;n.extracted) visitStm(ce,(Expression y){ if(auto id=cast(Identifier)y) if(isVar(id)) add(varName(id)); });
			}
			return mKept[n.id];
		}
		while(changed){
			changed=false;
			foreach(n;body_~reset_) mark(n);
		}
	}
	// emission
	auto loc=loop.loc;
	E setLoc(E:Expression)(E e){ e.loc=loc; return e; }
	Identifier mkId(Id n){ return setLoc(new Identifier(n)); }
	Expression annot(Expression e,Expression t){ return setLoc(new TypeAnnotationExp(e,t,TypeAnnotationType.annotation)); }
	Expression define(Expression l,Expression r){ return setLoc(new DefineExp(l,r)); }
	Expression dupOf(Expression e){ return setLoc(new CallExp(mkId(Id.s!"dup"),e,false,false)); }
	Expression forgetOf(Id n,Expression v=null){ return setLoc(new ForgetExp(mkId(n),v)); }
	Expression zero(){ return annot(setLoc(LiteralExp.makeInteger(0)),ℕt(true)); }
	Expression inc(Id n){ return setLoc(new AddAssignExp(mkId(n),setLoc(LiteralExp.makeInteger(1)))); }
	Expression appendLog(size_t li,Expression e){
		if(logs[li].stored!is logs[li].type) e=setLoc(new TypeAnnotationExp(e,logs[li].stored,TypeAnnotationType.conversion));
		return setLoc(new CatAssignExp(mkId(logs[li].name),setLoc(new VectorExp([e]))));
	}
	CompoundExp block(Expression[] s){ return setLoc(new CompoundExp(s)); }
	void renameItrans(Expression c,Id[Id] names){
		walkShallow(c,(Expression x){
			if(auto we=cast(WithExp)x) if(we.itrans)
				walkShallow(we.itrans,(Expression y){
					if(auto id=cast(Identifier)y) if(auto t=id.id in names) id.id=*t;
				});
		});
	}
	void renameSkipped(Expression c,Id[Id] names){
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
	// (renames variables in the copy `c`)
	Expression rename(Expression c,Id[Id] names){
		if(!names.length) return c;
		import ast.substitute:statementFreeVarsImpl;
		statementFreeVarsImpl(c,(Identifier y){
			if(auto t=y.id in names) y.id=*t;
			return 0;
		});
		walkShallow(c,(Expression x){
			if(auto le=cast(LambdaExp)x) le.orig=le.fd.copy();
			if(auto id=cast(Identifier)x) if(auto t=id.id in names) id.id=*t;
		});
		renameItrans(c,names);
		renameSkipped(c,names);
		return c;
	}
	Expression cp(Expression o,Id[Id] names){ return rename(o.copy(),names); }
	// copy of `o` with the extracted `calls` replaced by the values of `temps`
	Expression cpX(Expression o,CallExp[] calls,Id[] temps,Id[Id] names){
		auto c=o.copy();
		if(calls.length){
			Expression[] on,cn;
			walkShallow(o,(Expression x){ on~=x; });
			walkShallow(c,(Expression x){ cn~=x; });
			assert(on.length==cn.length);
			foreach(k,x;on) foreach(j,ce;calls) if(x is ce){
				auto cc=cast(CallExp)cn[k];
				cc.e=mkId(Id.s!"dup");
				cc.arg=mkId(temps[j]);
				cc.isSquare=false;
				static if(language==silq) cc.isClassical_=false;
			}
		}
		return rename(c,names);
	}
	Expression[] stmts;
	static if(is(T==ForExp)){
		auto lo=freshName(),hi=freshName(),st=range.step?freshName():Id.init;
		stmts~=define(mkId(lo),annot(range.left.copy(),range.left.type));
		if(range.step) stmts~=define(mkId(st),annot(range.step.copy(),range.step.type));
		stmts~=define(mkId(hi),annot(range.right.copy(),range.right.type));
		Expression mkLoop(CompoundExp b){
			auto r=setLoc(new ForExp(mkId(mainVar),null,ForAggregate(ForRange(range.leftExclusive,mkId(lo),range.step?mkId(st):null,range.rightExclusive,mkId(hi))),b));
			r.noSplit=true;
			return r;
		}
	}else{
		auto num=freshName();
		static if(is(T==RepeatExp)) stmts~=define(mkId(num),annot(loop.num.copy(),loop.num.type));
		else stmts~=define(mkId(num),zero());
		Expression mkLoop(CompoundExp b){
			auto r=setLoc(new RepeatExp(mkId(num),b));
			r.noSplit=true;
			return r;
		}
		static if(isDoWhile){
			Expression[] mkDoWhileLoop(CompoundExp b,CompoundExp rst,Id[] outputs){ // (the reset runs `num` times)
				Id[Id] exitNames; // (the other definitions of the body that are available after the loop get fresh names)
				foreach(d;loop.exitScope.mergedVars) if(d.mergedInto&&d.mergedInto.name&&definedInLoop(d)){
					auto v=d.mergedInto.name.id;
					if(v !in carriedNames&&!outputs.canFind(v)&&v !in exitNames) exitNames[v]=freshName();
				}
				auto c=freshName();
				rst.s=inc(c)~rst.s;
				auto r=setLoc(new DoWhileExp(b,setLoc(new BinaryExp!(Tok!"<")(mkId(c),mkId(num))),rst));
				r.noSplit=true;
				return [define(mkId(c),zero()),rename(r,exitNames)];
			}
		}
	}
	// the main loop
	Id[Id] copyOf;
	auto liftedOrder=sorted(liftedNames).filter!(v=>v in mLive).array;
	foreach(v;liftedOrder){
		copyOf[v]=freshName();
		stmts~=define(mkId(copyOf[v]),dupOf(mkId(v)));
	}
	static if(isDoWhile) foreach(v;sorted(exitLifted)) copyOf[v]=freshName(); // (defined by the main loop)
	foreach(ref l;logs) stmts~=define(mkId(l.name),annot(setLoc(new VectorExp([])),arrayTy(l.stored)));
	auto mRebuild=new bool[](nodes.length);
	bool computeRebuild(SliceNode n){
		bool r=logsAt[n.id].length!=0;
		foreach(c;n.a~n.b){
			r|=computeRebuild(c);
			r|=!mKept[c.id];
		}
		return mRebuild[n.id]=r;
	}
	foreach(n;body_~reset_) computeRebuild(n);
	size_t logAt(SliceNode n,LogKey key,Id var=Id.init){
		foreach(li;logsAt[n.id]) if(logs[li].key==key&&logs[li].var==var) return li;
		return size_t.max;
	}
	Expression[] emitM(SliceNode[] ns){
		Expression[] r;
		foreach(n;ns){
			foreach(li;logsAt[n.id]) if(logs[li].key==LogKey.value) r~=appendLog(li,dupOf(mkId(logs[li].var)));
			if(!mKept[n.id]) continue;
			if(n.kind==K.atom){
				CallExp[] calls;
				Id[] temps;
				foreach(li;logsAt[n.id]) if(logs[li].key==LogKey.call){
					auto ce=n.extracted[logs[li].idx],t=freshName();
					r~=define(mkId(t),cp(ce,copyOf));
					r~=appendLog(li,dupOf(mkId(t)));
					calls~=ce;
					temps~=t;
				}
				r~=cpX(n.e,calls,temps,copyOf);
				auto ml=logAt(n,LogKey.measurement,n.result);
				if(ml!=size_t.max) r~=appendLog(ml,dupOf(mkId(n.result)));
				continue;
			}
			if(!mRebuild[n.id]){
				r~=cp(n.e,copyOf);
				continue;
			}
			final switch(n.kind){
				case K.atom: assert(0);
				case K.ite:{
					auto ite=cast(IteExp)n.e;
					auto then=block(emitM(n.a));
					CompoundExp othw=ite.othw?block(emitM(n.b)):null;
					auto cl=logAt(n,LogKey.cond);
					if(cl!=size_t.max){
						if(!othw) othw=block([]);
						then.s=appendLog(cl,setLoc(LiteralExp.makeBoolean(true)))~then.s;
						othw.s=appendLog(cl,setLoc(LiteralExp.makeBoolean(false)))~othw.s;
					}
					r~=setLoc(new IteExp(cp(ite.cond,copyOf),then,othw));
					break;
				}
				case K.loop:{
					auto bdy=block(emitM(n.a));
					Expression logged(LogKey key,Expression e,Expression type){
						auto li=logAt(n,key);
						if(li==size_t.max) return e;
						auto t=freshName();
						r~=define(mkId(t),annot(e,type));
						r~=appendLog(li,dupOf(mkId(t)));
						return mkId(t);
					}
					bool empty=!bdy.s.length&&!n.nonQfree&&!mayFail[n.id]; // (only the header is logged)
					static if(language==silq) if(auto dw=cast(DoWhileExp)n.e){
						auto rst=block(emitM(n.b));
						auto cl=logAt(n,LogKey.count);
						Id cnt;
						if(cl!=size_t.max){ // (the number of resets)
							cnt=freshName();
							r~=define(mkId(cnt),zero());
							rst.s=inc(cnt)~rst.s;
						}
						auto nl=setLoc(new DoWhileExp(bdy,cp(dw.cond,copyOf),rst));
						nl.noSplit=dw.noSplit;
						r~=nl;
						if(cl!=size_t.max) r~=appendLog(cl,dupOf(mkId(cnt)));
						break;
					}
					if(auto fe=cast(ForExp)n.e){
						auto rng=fe.aggr.isRange;
						auto left=logged(LogKey.left,cp(rng.left,copyOf),rng.left.type);
						auto step=rng.step?logged(LogKey.step,cp(rng.step,copyOf),rng.step.type):null;
						auto right=logged(LogKey.right,cp(rng.right,copyOf),rng.right.type);
						if(empty) break;
						auto nl=setLoc(new ForExp(mkId(fe.loopVar.name.id),null,ForAggregate(ForRange(rng.leftExclusive,left,step,rng.rightExclusive,right)),bdy));
						nl.noSplit=fe.noSplit;
						r~=nl;
					}else if(auto re=cast(RepeatExp)n.e){
						auto num=logged(LogKey.num,cp(re.num,copyOf),re.num.type);
						if(empty) break;
						auto nl=setLoc(new RepeatExp(num,bdy));
						nl.noSplit=re.noSplit;
						r~=nl;
					}else{
						auto we=cast(WhileExp)n.e;
						auto cl=logAt(n,LogKey.count);
						Id cnt;
						if(cl!=size_t.max){
							cnt=freshName();
							r~=define(mkId(cnt),zero());
							bdy.s~=inc(cnt);
						}
						auto nl=setLoc(new WhileExp(cp(we.cond,copyOf),bdy));
						nl.noSplit=we.noSplit;
						r~=nl;
						if(cl!=size_t.max) r~=appendLog(cl,dupOf(mkId(cnt)));
					}
					break;
				}
				case K.with_:{
					auto we=cast(WithExp)n.e;
					r~=setLoc(new WithExp(cast(CompoundExp)cp(we.trans,copyOf),block(emitM(n.a))));
					break;
				}
				case K.block:
					r~=block(emitM(n.a));
					break;
			}
		}
		return r;
	}
	{
		auto mbdy=block(emitM(body_));
		mbdy.loc=loop.bdy.loc;
		static if(is(T==WhileExp)){
			mbdy.s~=inc(num);
			auto ml=setLoc(new WhileExp(cp(loop.cond,copyOf),mbdy));
			ml.noSplit=true;
			stmts~=ml;
		}else static if(isDoWhile){
			auto mrst=block(inc(num)~emitM(reset_));
			mrst.loc=loop.reset.loc;
			auto ml=setLoc(new DoWhileExp(mbdy,cp(loop.cond,copyOf),mrst));
			ml.noSplit=true;
			stmts~=ml;
		}else if(mbdy.s.length) stmts~=mkLoop(mbdy);
	}
	// the recomputations
	Id[Id][] renames;
	foreach(ref sl;slices){
		Id[Id] names;
		foreach(w;sorted(sl.carried)) if(!classVars[sl.cls].canFind(w)){
			names[w]=freshName();
			stmts~=define(mkId(names[w]),dupOf(mkId(w)));
		}
		foreach(v;sorted(sl.locals)) names[v]=freshName();
		renames~=names;
	}
	foreach(si,ref sl;slices){
		S=sl;
		Id[size_t] counter;
		Id[] counters;
		Expression[] readLog(size_t li,out Id t,Id[Id] names){
			auto c=counter.get(li,Id.init);
			if(c==Id.init){
				c=counter[li]=freshName();
				counters~=c;
			}
			t=freshName();
			Expression v=dupOf(setLoc(new IndexExp(mkId(logs[li].name),mkId(c))));
			if(logs[li].stored!is logs[li].type) v=setLoc(new TypeAnnotationExp(v,cp(logs[li].type,names),TypeAnnotationType.coercion));
			return [define(mkId(t),v),inc(c)];
		}
		Id[Id] without(Id[Id] names,SetX!Id vars){
			names=names.dup;
			foreach(u;vars) names.remove(u);
			return names;
		}
		Expression[] emitS(SliceNode[] ns,Id[Id] names,Id[Id]* namesAfter=null){ // (`namesAfter`: the names at the end, e.g., for the reset of a `do`-`while` loop)
			Expression[] r;
			names=names.dup;
			foreach(n;ns){
				foreach(x;S.reads[n.id]){
					Id t;
					r~=readLog(logAt(n,LogKey.value,x[0]),t,names);
					names[x[0]]=t;
				}
				scope(success) foreach(u;writesOf[n.id]) names.remove(u);
				foreach(u;sorted(S.disp[n.id])){
					if(S.measDisp[n.id]&&u==n.measured){
						Id t;
						r~=readLog(logAt(n,LogKey.measurement,n.result),t,names);
						r~=forgetOf(names.get(u,u),mkId(t));
					}else r~=forgetOf(names.get(u,u));
				}
				scope(success) foreach(u;sorted(S.dispAfter[n.id])) r~=forgetOf(names.get(u,u));
				if(!S.kept[n.id]) continue;
				final switch(n.kind){
					case K.atom:{
						auto nnames=names;
						CallExp[] calls;
						Id[] temps;
						auto parts=keptParts(n,S);
						if(!n.inR){
							foreach(c;parts) foreach(ce;c.extracted){
								Id t;
								r~=readLog(logOf(n.id,LogKey.call,Id.init,ce.type,n.extracted.countUntil!((x,y)=>x is y)(ce)),t,names);
								calls~=ce;
								temps~=t;
							}
						}
						if(parts.length==n.comps.length||!n.comps.length){
							r~=cpX(n.e,calls,temps,nnames);
							break;
						}
						Expression[] ls,rs;
						foreach(j,c;n.comps) if(S.compKept[n.id][j]){
							ls~=n.lhs[j].copy();
							rs~=cpX(n.rhs[j],calls,temps,null);
						}
						auto def=ls.length==1?define(ls[0],rs[0]):define(setLoc(new TupleExp(ls)),setLoc(new TupleExp(rs)));
						def.loc=n.e.loc;
						r~=rename(def,nnames);
						break;
					}
					case K.ite:{
						auto ite=cast(IteExp)n.e;
						Expression cond;
						auto inner=names;
						if(!n.quantum&&!n.inR&&logAt(n,LogKey.cond)!=size_t.max){
							Id t;
							r~=readLog(logAt(n,LogKey.cond),t,names);
							cond=mkId(t);
						}else cond=cp(ite.cond,inner);
						auto then=block(emitS(n.a,inner));
						CompoundExp othw=ite.othw?block(emitS(n.b,inner)):null;
						r~=setLoc(new IteExp(cond,then,othw));
						break;
					}
					case K.loop:{
						Expression read(LogKey key,Expression e){
							if(n.inR||logAt(n,key)==size_t.max) return cp(e,names);
							Id t;
							r~=readLog(logAt(n,key),t,names);
							return mkId(t);
						}
						SetX!Id changed;
						if(!n.inR) foreach(c;n.a~n.b) foreach(u;writesOf[c.id]) changed.insert(u);
						auto bnames=without(names,changed);
						static if(language==silq) if(auto dw=cast(DoWhileExp)n.e){
							Id[Id] after;
							if(n.inR){
								auto nb=emitS(n.a,names,&after);
								auto nr=emitS(n.b,after);
								r~=setLoc(new DoWhileExp(block(nb),cp(dw.cond,after),block(nr)));
							}else{
								Id t;
								r~=readLog(logAt(n,LogKey.count),t,names);
								auto c=freshName();
								r~=define(mkId(c),zero());
								auto nb=emitS(n.a,bnames,&after);
								auto nr=emitS(n.b,after);
								r~=setLoc(new DoWhileExp(block(nb),setLoc(new BinaryExp!(Tok!"<")(mkId(c),mkId(t))),block(inc(c)~nr)));
							}
							break;
						}
						if(auto fe=cast(ForExp)n.e){
							auto rng=fe.aggr.isRange;
							auto left=read(LogKey.left,rng.left);
							auto step=rng.step?read(LogKey.step,rng.step):null;
							auto right=read(LogKey.right,rng.right);
							auto nl=setLoc(new ForExp(mkId(fe.loopVar.name.id),null,ForAggregate(ForRange(rng.leftExclusive,left,step,rng.rightExclusive,right)),block(emitS(n.a,bnames))));
							r~=nl;
						}else if(auto re=cast(RepeatExp)n.e){
							auto num=read(LogKey.num,re.num);
							auto nl=setLoc(new RepeatExp(num,block(emitS(n.a,bnames))));
							r~=nl;
						}else{
							auto we=cast(WhileExp)n.e;
							if(n.inR){
								auto nl=setLoc(new WhileExp(cp(we.cond,names),block(emitS(n.a,names))));
								r~=nl;
							}else{
								Id t;
								r~=readLog(logAt(n,LogKey.count),t,names);
								auto nl=setLoc(new RepeatExp(mkId(t),block(emitS(n.a,bnames))));
								r~=nl;
							}
						}
						break;
					}
					case K.with_:{
						auto we=cast(WithExp)n.e;
						r~=setLoc(new WithExp(cast(CompoundExp)cp(we.trans,names),block(emitS(n.a,without(names,n.cdefs)))));
						break;
					}
					case K.block:
						r~=block(emitS(n.a,names));
						break;
				}
			}
			if(namesAfter) *namesAfter=names;
			return r;
		}
		static if(isDoWhile){
			Id[Id] after;
			auto sbdy=emitS(body_,renames[si],&after);
			auto srst=emitS(reset_,after);
			if(sbdy.length||srst.length){
				foreach(c;counters) stmts~=define(mkId(c),zero());
				auto b=block(sbdy),rs=block(srst);
				b.loc=loop.bdy.loc;
				stmts~=mkDoWhileLoop(b,rs,classExits[sl.cls]);
			}
		}else{
			auto sbdy=emitS(body_,renames[si]);
			if(sbdy.length){
				foreach(c;counters) stmts~=define(mkId(c),zero());
				auto b=block(sbdy);
				b.loc=loop.bdy.loc;
				stmts~=mkLoop(b);
			}
		}
	}
	// (the copies of other lifted variables that the recomputations read end up with their recomputed values)
	foreach(si,ref sl;slices) foreach(w;sorted(sl.carried)) if(auto c=w in renames[si]) stmts~=forgetOf(*c,dupOf(mkId(w)));
	foreach(v;liftedOrder) stmts~=forgetOf(copyOf[v],dupOf(mkId(v)));
	static if(isDoWhile) foreach(v;sorted(exitLifted)){
		stmts~=forgetOf(copyOf[v],dupOf(mkId(v)));
		auto type=exitTypes[v];
		if(type.freeIdentifiers.any!(id=>true)) // (the recomputation may express the type in terms of logged values)
			stmts~=define(mkId(v),setLoc(new TypeAnnotationExp(mkId(v),cp(type,null),TypeAnnotationType.coercion)));
	}
	auto lowered=new CompoundExp(stmts);
	lowered.loc=loc;
	auto before=sc.rnsymtab.dup;
	scope(success) linkLoweredVariables(sc,before);
	sc.restoreStateSnapshot(state.origStateSnapshot);
	static if(__traits(hasMember,astopt,"dumpLoops")) if(astopt.dumpLoops){
		import util.io:stderr;
		stderr.writeln(loop);
		stderr.writeln("-loop-slicing→");
		stderr.writeln(lowered);
	}
	return statementSemantic(lowered,sc,flags);
}

Expression lowerLoop(T)(T loop,FixedPointIterState state,Scope sc,ref StmFlags flags)in{
	assert(loop.isSemCompleted());
}do{
	auto r=lowerLoopImpl(loop,state,sc,flags);
	static if(language==silq) if(auto ce=cast(CompoundExp)r) if(!loopContainsReturn(loop)) ce.loweredFrom=loop; // (e.g., reversed as the loop)
	return r;
}
private Expression lowerLoopImpl(T)(T loop,FixedPointIterState state,Scope sc,ref StmFlags flags){
	static if(language==silq) enum isDoWhile=is(T==DoWhileExp);
	else enum isDoWhile=false;
	if(auto r=sliceLoop(loop,state,sc,flags)) return r;
	static if(!isDoWhile) if(auto r=splitLoop(loop,state,sc,flags)) return r;
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
		static if(is(T==WhileExp)||isDoWhile) collectAccesses(loop.cond);
		static if(isDoWhile) collectAccesses(loop.reset);
	}
	SetX!Id namesInLoop; // names occurring in the loop
	void collectNames(Expression e){
		visitStm(e,(Expression x){ if(auto id=cast(Identifier)x) namesInLoop.insert(id.id); });
	}
	collectNames(loop.bdy);
	static if(is(T==WhileExp)||isDoWhile) collectNames(loop.cond);
	static if(isDoWhile) collectNames(loop.reset);
	// continuation-passing lowering for loops with early returns:
	// the statements after the loop (which end in a `return`) become the base case of the recursion
	Expression[] continuation=null;
	bool dropUnreachable=false; // code after an infinite loop
	static if(language==silq){
		bool contInfinite=isEmpty(loop); // (the loop does not exit normally, e.g., `repeat 2 { return 1; }`)
		if(!contInfinite&&loopContainsReturn(loop))
			continuation=sc.loopContinuation.take(loop);
		else if(contInfinite)
			dropUnreachable=sc.loopContinuation.take(loop).length!=0;
	}
	// with a continuation, lifted loop-carried variables are threaded through the recursion as `const`
	// parameters, so that they are still lifted in the code after the loop and in join points in the body
	foreach(st;continuation){ // (the continuation becomes part of the recursive function)
		import ast.substitute:statementFreeVarsImpl;
		statementFreeVarsImpl(st,(Identifier y){ namesInLoop.insert(y.id); return 0; });
	}
	SetX!Id unchangedConst; // (variables that are only consumed by early returns, see `loopParams`)
	auto loopParams_=state.prevStateSnapshot.loopParams(loop.bdy.blscope_,state.dummyAnalysisRan&&!continuation?&state.mustBeConstFromDummies:null,separateConstParams,&accessedDecls,&namesInLoop,&unchangedConst);
	auto constParams=loopParams_[0], movedParams=loopParams_[1];
	// (the loop bounds are passed as `const` parameters as well)
	Q!(Id,Declaration,Expression,bool) boundParam(Identifier name,Expression type){
		auto decl=new VarDecl(name.copy());
		decl.loc=name.loc;
		decl.vtype=type;
		decl.sstate=SemState.completed;
		Expression.CopyArgs cargs;
		return q(name.id,cast(Declaration)decl,type.copy(cargs),false);
	}
	static if(is(T==ForExp)){
		Identifier rightName=null,stepName=null;
		if(auto range=loop.aggr.isRange){
			rightName=temporaryIdentifier(range.right.loc);
			constParams~=boundParam(rightName,range.right.type);
			if(range.step){
				stepName=temporaryIdentifier(range.step.loc);
				constParams~=boundParam(stepName,range.step.type);
			}
		}
	}else static if(is(T==RepeatExp)){
		auto numName=temporaryIdentifier(loop.num.loc);
		constParams~=boundParam(numName,loop.num.type);
	}
	static if(is(T==WhileExp)||isDoWhile){
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
		auto returnTpl=new TupleExp(cast(Expression[])ids(constMovedParams.filter!(p=>p[3]&&p[0] !in unchangedConst).array,true));
		returnTpl.loc=loop.loc;
	}
	static if(isDoWhile){ // (the definitions of the body that are available after the loop are returned as well)
		Q!(Identifier,Expression,Expression)[] exitLocals; // (name, type, type in the result of the function)
		SetX!Id paramNames,changed; // (`changed`: names of the values that the loop defines or changes)
		foreach(p;allParams) paramNames.insert(p[1].name.id);
		Q!(Id,Expression)[] replays; // (definitions of the body that are computed again after the loop, see `liftedExitDefinitions`)
		if(auto xsc=loop.exitScope){ // (no exit if the body returns)
			foreach(d;chain(xsc.mergedVars,loop.bdy.blscope_.mergedVars)) if(d.mergedInto.name) changed.insert(d.mergedInto.name.id);
			if(!continuation) replays=liftedExitDefinitions(loop,sc,paramNames);
			foreach(d;xsc.mergedVars){
				auto name=d.mergedInto.name;
				if(!name||name.id in paramNames||replays.canFind!(r=>r[0]==name.id)) continue;
				auto id=new Identifier(name.id);
				id.loc=d.loc;
				auto type=typeForDecl(d.mergedInto);
				auto rtype=type?weakenedExitType(type,changed):null;
				exitLocals~=q(id,type,rtype?rtype:type);
			}
		}
		sort!((a,b)=>a[0].id.str<b[0].id.str)(exitLocals);
		foreach(e;exitLocals){ // (types mentioning local values of the function are weakened, see `exitCoercions`)
			Expression r=e[0].copy(cargsDefault);
			if(e[2] !is e[1]) r=new TypeAnnotationExp(r,e[2].copy(cargsDefault),TypeAnnotationType.annotation);
			r.loc=e[0].loc;
			returnTpl.e~=r;
		}
	}
	auto cee=new Identifier(fi);
	cee.loc=loop.loc;
	Identifier[] constTmpNames;
	Identifier[] resultConstTmpNames; // (the `const` parameters that the loop returns, see `unchangedConst`)
	Parameter[] params;
	foreach(i,p;allParams){
		bool isConst=i<loopParams.length+constParams.length;
		bool mayChange=p[3];
		auto id=isConst&&mayChange?freshName:p[1].name.id;
		auto pname=new Identifier(id);
		pname.loc=p[1].loc;
		if(isConst&&mayChange) constTmpNames~=pname.copy(cargsDefault);
		if(isConst&&mayChange&&i>=loopParams.length&&p[0] !in unchangedConst) resultConstTmpNames~=pname.copy(cargsDefault);
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
	bool isInfinite=isEmpty(loop);
	bool isCertainReturn=definitelyReturns(loop.bdy);
	static if(is(T==WhileExp)||isDoWhile){
		auto ncond=loop.cond.copy(cargsDefault);
	}else static if(is(T==ForExp)){
		//writeln("?? ",constParams);
		Expression ncond;
		Identifier leftName;
		Expression leftDef;
		Expression stepDef=null;
		Expression rightDef;
		Identifier modMatchName=null;
		Expression modMatchDef=null;
		Expression adjDef=null;
		Expression adjIte=null;
		Expression adjUpd=null;
		if(auto range=loop.aggr.isRange){
			leftName=temporaryIdentifier(range.left.loc);
			auto leftInit=range.left.copy(cargsDefault);
			leftInit.loc=range.left.loc;
			leftDef=new DefineExp(leftName,leftInit);
			leftDef.loc=range.left.loc;
			auto rightInit=range.right.copy(cargsDefault);
			rightInit.loc=range.right.loc;
			rightDef=new DefineExp(rightName,rightInit);
			rightDef.loc=range.right.loc;
			if(range.step){
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
	// (nested blocks used as statements share the enclosing scope, e.g., when the analysis wrapped a nested loop: flatten
	// them, so that nested loops are in the same block as the statements after them and can take continuations)
	nbdy.s=flattenStatementBlocks(nbdy.s);
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

	static if(isDoWhile){
		auto nrst=loop.reset.copy(cargsDefault);
		nrst.s=flattenStatementBlocks(nrst.s);
	}else if(!isCertainReturn){
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
		else static if(language==silq) if(auto dw=cast(DoWhileExp)e){
			adjustEarlyReturns(dw.bdy);
			if(dw.reset) adjustEarlyReturns(dw.reset);
		}
	}
	Expression bdy;
	static if(isDoWhile){{
		// `B; if c{}else{ exit } R; return f(…);`, or, with quantum definitions of the body that are available after the loop,
		// `B; if c{ R; v:=[]; }else{ v:=[(x₁,…,xₙ)]; } if v.length=0{ forget(v=[]); return f(…); } [(x₁,…,xₙ)]:=v; exit`
		// (the reset does not forget values in a branch while its sibling consumes what they depend on)
		if(!isCertainReturn){ // (otherwise, the condition and the reset are not reached)
			auto contr=new ReturnExp(ce); // (the reset continues with the next iteration)
			contr.loc=ce.loc;
			if(isInfinite){
				nbdy.s~=nrst.s~[cast(Expression)contr];
			}else{
				T at(T)(T e){ e.loc=loop.loc; return e; }
				Identifier mk(Id n){ return at(new Identifier(n)); }
				Expression[] exit;
				if(continuation) exit=continuation.map!(st=>st.copy(cargsDefault)).array;
				else{
					adjustEarlyReturns(nbdy);
					adjustEarlyReturns(nrst);
					Expression retexp=returnTpl;
					if(hasEarlyReturns) retexp=inj(retexp,false);
					exit=[at(new ReturnExp(retexp))];
				}
				Expression[] forgets; // (of recomputed definitions that the reset uses)
				foreach(r;replays){
					bool used=false;
					visitStm(loop.reset,(Expression x){ if(auto id=cast(Identifier)x) if(varName(id)==r[0]) used=true; });
					if(used) forgets~=at(new ForgetExp(mk(r[0]),r[1].copy(cargsDefault)));
				}
				bool hold=forgets.length||exitLocals.any!(e=>e[1]&&!e[1].isClassical());
				if(!hold){
					auto ite=at(new IteExp(ncond,at(new CompoundExp([])),at(new CompoundExp(forgets~exit))));
					nbdy.s~=[cast(Expression)ite]~nrst.s~[cast(Expression)contr];
				}else{
					auto v=freshName();
					Expression tupleOf(Expression[] es){ return es.length==1?es[0]:at(new TupleExp(es)); }
					// (the branch consumes the definitions, which are defined again after it: a definition precedes those its type mentions)
					typeof(exitLocals) packed,rest=exitLocals.dup;
					while(rest.length){
						auto i=rest.countUntil!(x=>!rest.any!(y=>y[1]&&y[1].freeIdentifiers.any!(fv=>fv.id==x[0].id)));
						if(i<0) i=0;
						packed~=rest[i];
						rest=rest[0..i]~rest[i+1..$];
					}
					Expression ety=packed.length==1?packed[0][2]:tupleTy(packed.map!(e=>e[2]).array);
					Expression empty(){ return at(new TypeAnnotationExp(at(new VectorExp([])),arrayTy(ety).copy(cargsDefault),TypeAnnotationType.annotation)); }
					Expression pack(Q!(Identifier,Expression,Expression) e){
						auto id=e[0].copy(cargsDefault);
						if(e[1]&&e[1].isClassical()) id.moved=true;
						if(e[2] is e[1]) return id;
						return at(new TypeAnnotationExp(id,e[2].copy(cargsDefault),TypeAnnotationType.annotation));
					}
					auto vals=packed.map!pack.array;
					auto then=at(new CompoundExp(nrst.s~[cast(Expression)at(new DefineExp(mk(v),empty()))]));
					auto othw=at(new CompoundExp(forgets~[cast(Expression)at(new DefineExp(mk(v),at(new VectorExp([tupleOf(vals)]))))]));
					nbdy.s~=at(new IteExp(ncond,then,othw));
					auto len=at(new FieldExp(mk(v),mk(Id.s!"length")));
					auto cont=at(new CompoundExp([at(new ForgetExp(mk(v),empty())),cast(Expression)contr]));
					nbdy.s~=at(new IteExp(at(new EqExp(len,at(LiteralExp.makeInteger(0)))),cont,null));
					Expression[] lhs,coercions;
					foreach(e;packed){
						if(e[2] is e[1]){
							lhs~=e[0].copy(cargsDefault);
							continue;
						}
						auto tmp=freshName();
						lhs~=mk(tmp);
						coercions~=at(new DefineExp(e[0].copy(cargsDefault),at(new TypeAnnotationExp(mk(tmp),e[1].copy(cargsDefault),TypeAnnotationType.coercion))));
					}
					nbdy.s~=at(new DefineExp(at(new VectorExp([tupleOf(lhs)])),mk(v)));
					nbdy.s~=coercions~exit;
				}
			}
			if(continuation) if(auto ns=erpTransform(nbdy.s)) nbdy.s=ns;
		}
		bdy=nbdy;
	}}else if(continuation){
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
	if(!isDoWhile&&!continuation&&(!isInfinite||!isCertainReturn)){
		ret=new ReturnExp(retName.copy(cargsDefault)); // avoid non-toplevel return
		ret.loc=loop.loc;
	}
	auto cmpbdy=cast(CompoundExp)bdy;
	auto fbdy=new CompoundExp((constParamDef?[cast(Expression)constParamDef]:[])~(cmpbdy?cmpbdy.s:[bdy])~(ret?[ret]:[]));
	fbdy.loc=bdy.loc;
	// (the return type and the annotation are given explicitly where possible, avoiding a second analysis of the function)
	Expression rret=null; // (inferred for a `do`-`while` loop, whose result includes definitions of the body)
	if(!isDoWhile&&!continuation&&!hasEarlyReturns&&!isInfinite){
		Expression[] rids;
		foreach(i,p;allParams){
			if(i<loopParams.length) continue;
			static if(returnOnlyMoved) bool returned=i>=loopConstParams.length;
			else bool returned=p[3]&&p[0] !in unchangedConst;
			if(!returned||sc.canInsert(p[1].name.id)) continue; // (see `returnTpl`)
			auto rid=new Identifier(params[i].name.id);
			rid.loc=loop.loc;
			rids~=rid;
		}
		auto rtpl=new TupleExp(rids);
		rtpl.loc=loop.loc;
		rret=new TypeofExp(rtpl);
		rret.loc=loop.loc;
	}
	auto fd=new FunctionDef(fdn,params,true,rret,fbdy);
	foreach(p;constParams) if(p[3]) fd.loweredConstIds.insert(p[0]);
	fd.attributes[Id.s!"silq-loop"] = LiteralExp.makeString(lowerf(T.stringof[0..$-"Exp".length]));
	fd.annotation=pure_;
	visitStm(loop.bdy,(Expression x){ if(auto ce=cast(CallExp)x) if(auto ft=cast(FunTy)ce.e.type) fd.weakenAnnotation(ft.annotation,ce); });
	static if(is(T==WhileExp)||isDoWhile) visitStm(loop.cond,(Expression x){ if(auto ce=cast(CallExp)x) if(auto ft=cast(FunTy)ce.e.type) fd.weakenAnnotation(ft.annotation,ce); });
	static if(isDoWhile) visitStm(loop.reset,(Expression x){ if(auto ce=cast(CallExp)x) if(auto ft=cast(FunTy)ce.e.type) fd.weakenAnnotation(ft.annotation,ce); });
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
		auto defTpl=new TupleExp(cast(Expression[])chain(resultConstTmpNames.map!(id=>id.copy(cargsDefault)),ids(movedParams,true)).array);
		defTpl.loc=loop.loc;
	}
	Expression[] exitCoercions; // (of the weakened definitions of the body, and of the quantum ones, which the function may compute classically)
	static if(isDoWhile) foreach(e;exitLocals){
		if(e[2] is e[1]&&(!e[1]||e[1].isClassical())){
			defTpl.e~=e[0].copy(cargsDefault);
			continue;
		}
		auto tmp=new Identifier(freshName());
		tmp.loc=e[0].loc;
		defTpl.e~=tmp;
		auto use=tmp.copy(cargsDefault);
		use.moved=true; // (the result of the function does not outlive the coercion)
		auto coerced=new TypeAnnotationExp(use,e[1].copy(cargsDefault),TypeAnnotationType.coercion);
		coerced.loc=e[0].loc;
		auto co=new DefineExp(e[0].copy(cargsDefault),coerced);
		co.loc=e[0].loc;
		exitCoercions~=co;
	}
	foreach(arg;paramTpl2.e[$-movedParams.length..$]){ // (a moved variable that is not available after the loop is consumed by it, e.g., by the final evaluation of the condition)
		auto id=cast(Identifier)arg;
		if(!id||defTpl.e.any!(d=>(cast(Identifier)d)&&(cast(Identifier)d).id==id.id)) continue;
		id.moved=true;
		static if(is(T==WhileExp)) id.loc=loop.cond.loc;
		else id.loc=loop.loc;
	}
	Expression[] stmts=[fd];
	Expression forgetFunction(){ // (its type may mention variables that it captures, which may change after the loop)
		auto fid=new Identifier(fi);
		fid.loc=loop.loc;
		auto fe=new ForgetExp(fid,null);
		fe.loc=loop.loc;
		return fe;
	}
	void defineLocals(ref Expression[] stmts,Expression locals){
		auto def=new DefineExp(defTpl,locals);
		def.loc=loop.loc;
		stmts~=def;
		static if(!returnOnlyMoved){
			if(resultConstTmpNames.length){
				auto assgnTpl1=new TupleExp(cast(Expression[])ids(constParams.filter!(p=>p[3]&&p[0] !in unchangedConst).array,false));
				assgnTpl1.loc=loop.loc;
				auto assgnTpl2=new TupleExp(cast(Expression[])resultConstTmpNames.map!(id=>id.copy(cargsDefault)).array);
				assgnTpl2.loc=loop.loc;
				auto assgn=new AssignExp(assgnTpl1,assgnTpl2);
				assgn.loc=loop.loc;
				stmts~=assgn;
			}
		}
		stmts~=exitCoercions;
		static if(isDoWhile) foreach(r;replays){
			auto rdef=new DefineExp(new Identifier(r[0]),r[1].copy(cargsDefault));
			rdef.loc=rdef.e1.loc=loop.loc;
			stmts~=rdef;
		}
		stmts~=forgetFunction();
	}
	if(continuation){
		auto fret=new ReturnExp(ce2);
		fret.loc=loop.loc;
		stmts~=fret;
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
		stmts~=forgetFunction();
	}
	static if(is(T==ForExp)){
		stmts=[cast(Expression)leftDef]~(stepDef?[stepDef]:[])~[cast(Expression)rightDef]~(modMatchDef?[modMatchDef]:[])~(adjDef?[adjDef]:[])~(adjIte?[adjIte]:[])~(adjUpd?[adjUpd]:[])~stmts;
	}else static if(is(T==RepeatExp)){
		stmts=[cast(Expression)numDef]~stmts;
	}
	auto lowered=new CompoundExp(stmts);
	lowered.loc=loop.loc;
	auto before=sc.rnsymtab.dup;
	scope(success) linkLoweredVariables(sc,before);
	sc.restoreStateSnapshot(state.origStateSnapshot);
	//imported!"util.io".writeln("BEFORE SEMANTIC: ",lowered);
	auto result=statementSemantic(lowered,sc,flags);
	if(continuation||dropUnreachable) sc.loopContinuation.used=true; // (after analyzing `lowered`)
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
// statements are identified across copies by `Expression.erpId` (0: not identified, e.g. generated code)
size_t erpKey(Expression e){ return e.erpId; }
size_t erpNextId=1;
// `a` and `b` are copies of each other: corresponding nodes get the same identifiers
void erpAssignIds(Expression a,Expression b){
	Expression[] xs,ys;
	visitStm(a,(Expression x){ xs~=x; });
	visitStm(b,(Expression y){ ys~=y; });
	assert(xs.length==ys.length);
	foreach(i;0..xs.length){
		auto id=erpNextId++;
		xs[i].erpId=id;
		ys[i].erpId=id;
	}
}
bool containsReturn(Expression e){
	bool r=false;
	visitStm(e,(Expression x){ if(cast(ReturnExp)x) r=true; });
	return r;
}
static if(language==silq)
bool containsDoWhile(Expression e){ // (not supported by `splitLoop`)
	bool r=false;
	visitStm(e,(Expression x){ if(cast(DoWhileExp)x) r=true; });
	return r;
}
bool hasLoopWithReturn(Expression e){
	bool r=false;
	visitStm(e,(Expression x){
		if(isLoopStatement(x)) if(containsReturn(x)) r=true;
	});
	return r;
}
// Lifted definitions of the body of a `do`-`while` loop that are available after it and that read only values that are available
// after it as well, which the rest of the body and the condition do not change: they are computed again after the recursive function
// returns instead of being returned (the result of the function is not lifted)
static if(language==silq)
Q!(Id,Expression)[] liftedExitDefinitions(DoWhileExp loop,Scope sc,ref SetX!Id paramNames){
	Q!(Id,Expression)[] r;
	auto xsc=loop.exitScope;
	MapSX!(Id,Declaration) exitDecls;
	foreach(d;xsc.mergedVars) if(d.mergedInto.name) exitDecls[d.mergedInto.name.id]=d.mergedInto;
	auto stms=flattenStatementBlocks(loop.bdy.s.dup);
	SetX!Id later; // (names that the rest of the body or the condition change)
	void writes(Expression e){
		void lhs(Expression l){
			visitStm(l,(Expression y){ if(auto id=cast(Identifier)y) later.insert(varName(id)); });
		}
		visitStm(e,(Expression x){
			if(auto de=cast(DefineExp)x) lhs(de.e1);
			else if(auto ae=cast(AAssignExp)x) lhs(ae.e1);
			else if(auto fe=cast(ForgetExp)x) lhs(fe.var);
			else if(auto we=cast(WithExp)x){ if(we.itrans) writes(we.itrans); } // (e.g., a component replacement)
			else if(auto id=cast(Identifier)x) if(id.type&&!id.type.isClassical()&&!id.constLookup&&!id.implicitDup) later.insert(varName(id));
		});
	}
	writes(loop.cond);
	foreach_reverse(i,st;stms){
		scope(exit) writes(st);
		auto de=cast(DefineExp)st;
		auto id=de?cast(Identifier)de.e1:null;
		if(!id||!id.meaning) continue;
		auto name=varName(id);
		auto decl=exitDecls.get(name,null);
		if(!decl||name in paramNames||name in later||r.canFind!(x=>x[0]==name)) continue;
		auto type=typeForDecl(decl);
		if(!type||type.isClassical()||!sc.dependencyTracked(decl)||sc.getDependency(decl).isTop) continue;
		bool ok=true;
		visitStm(loop.cond,(Expression x){ if(auto cid=cast(Identifier)x) if(varName(cid)==name) ok=false; });
		foreach(fv;de.e2.freeIdentifiers){
			if(fv.meaning&&fv.meaning.isToplevelDeclaration()) continue;
			auto v=varName(fv);
			if(v==name||v in later||v !in paramNames&&v !in exitDecls) ok=false; // (`v==name`: the definition consumes the previous version)
		}
		if(ok) r=q(name,de.e2)~r;
	}
	return r;
}
// the type in the result of a lowered `do`-`while` loop of a definition of the body of type `t` (`null` if not possible)
static if(language==silq)
Expression weakenedExitType(Expression t,ref SetX!Id changed){
	bool mentionsChanged(Expression t){
		foreach(id;t.freeIdentifiers)
			if(id.id in changed||id.meaning&&id.meaning.name&&id.meaning.name.id in changed) return true;
		return false;
	}
	Expression rec(Expression t){
		if(!mentionsChanged(t)) return t;
		if(auto ft=isFixedIntTy(t)) return t.isClassical()?(ft.isSigned?ℤt(true):ℕt(true)):null;
		if(auto vt=cast(VectorTy)t){ if(auto w=rec(vt.next)) return arrayTy(w); return null; }
		if(auto at=cast(ArrayTy)t){ if(auto w=rec(at.next)) return arrayTy(w); return null; }
		if(auto tt=cast(TupleTy)t){
			Expression[] ws;
			foreach(c;tt.types){
				auto w=rec(c);
				if(!w) return null;
				ws~=w;
			}
			return tupleTy(ws);
		}
		return null;
	}
	return rec(t);
}
bool loopContainsReturn(T)(T loop){
	static if(language==silq) static if(is(T==DoWhileExp)) return containsReturn(loop.bdy)||loop.reset&&containsReturn(loop.reset);
	return containsReturn(loop.bdy);
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
		if(!astopt.removeLoops||!isLoopStatement(e)) return false;
		if(i+1>=block.length) return false;
		// the code after an infinite loop is unreachable; it is dropped by the lowering
		if(!isInfiniteLoop(e)&&(!endsWithReturn(block[$-1])||!containsReturn(e))) return false;
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
// `while true` (syntactically, as the loop may not be analyzed yet)
bool isInfiniteLoop(Expression e){
	static if(language==silq) if(auto dw=cast(DoWhileExp)e) return endsWithReturn(dw.bdy)||isTrueCondition(dw.cond); // (or `do{ … return e; }while c`)
	auto we=cast(WhileExp)e;
	if(!we) return false;
	return isTrueCondition(we.cond);
}
private bool isTrueCondition(Expression cond){
	if(cond.type) return isTrue(cond);
	if(auto id=cast(Identifier)cond) return id.id==Id.s!"true";
	if(auto le=cast(LiteralExp)cond) return le.lit.type==Tok!"0"&&le.lit.str=="1";
	return false;
}
bool erpRecording(Scope sc){
	for(auto fd=sc.getFunction();fd;fd=fd.scope_?fd.scope_.getFunction():null)
		if(fd.erpStage==1) return true;
	return false;
}
void erpRecordJoin(Expression stm,Scope sc){
	ERPVar[] vars;
	VarDecl[] decls; // (parallel to `vars`)
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
			vars~=ERPVar(vd.name.id,type,!type.isClassical()&&sc.canForget(vd),vd.isPinned);
			decls~=vd;
		}
		if(cast(FunctionScope)c) break;
	}
	// A lifted variable is passed to the join point as `const`, and forgotten after the call. This is only possible if its
	// dependencies are still available then: the quantum variables that are not lifted are consumed by the call.
	for(bool changed=true;changed;){
		changed=false;
		foreach(k,ref v;vars){
			if(!v.lifted) continue;
			if(!sc.dependencyTracked(decls[k])){ v.lifted=false; changed=true; continue; }
			auto dep=sc.getDependency(decls[k]);
			if(dep.isTop){ v.lifted=false; changed=true; continue; }
			foreach(d;dep.dependencies){
				if(!d.name) continue;
				foreach(w;vars){
					if(w.name!=d.name.id||w.lifted||w.isConst||w.type.isClassical()) continue;
					v.lifted=false;
					changed=true;
				}
				if(!v.lifted) break;
			}
		}
	}
	if(erpKey(stm)) erpJoins[erpKey(stm)]=vars;
}
// functions that entered stage 1 (see `erpFinish`)
FunctionDef[] erpStage1Functions;
// stage 1 starts before the body of `fd` is analyzed
void erpBeforeBody(FunctionDef fd){
	// functions generated by the loop lowering and join points are covered by the enclosing function
	if(Id.s!"silq-loop" in fd.attributes||Id.s!"silq-join" in fd.attributes) return;
	if(astopt.removeLoops&&fd.erpStage==0&&!fd.keepLoops&&fd.body_&&!fd.body_.isSemStarted()&&hasLoopWithReturn(fd.body_)){
		fd.erpStage=1;
		fd.keepLoops=true;
		erpStage1Functions~=fd;
		if(fd.origBody_) erpAssignIds(fd.body_,fd.origBody_);
	}
}
// record join-point information after statement `stms[i]` (originally `original`) has been analyzed
void erpAfterStatement(Expression original,Expression[] stms,size_t i,Scope sc){
	if(!erpRecording(sc)) return;
	// (also for the last statement of a block: the loop lowering may place it before other statements, e.g., the recursive
	// call at the end of the body of a loop function)
	if((cast(IteExp)original||cast(CompoundExp)original)&&hasLoopWithReturn(original))
		erpRecordJoin(original,sc);
	if(isLoopStatement(original)&&containsReturn(original)){
		erpRecordJoin(original,sc); // (variables after the loop, see `erpExplicitExits`)
		if(stms[i].type==bottom&&erpKey(original)) erpDivergingLoops[erpKey(original)]=true; // (loop never exits normally)
		if(auto we=cast(WhileExp)stms[i]){ // (see `erpLoopExplicit`)
			bool consumes=false;
			visitStm(we.cond,(Expression x){
				if(auto id=cast(Identifier)x)
					if(cast(VarDecl)id.meaning&&!id.constLookup&&!id.implicitDup) consumes=true;
			});
			if(consumes&&erpKey(original)) erpConsumingGuards[erpKey(original)]=true;
		}
	}
}
bool[size_t] erpDivergingLoops;
bool[size_t] erpConsumingGuards; // `while` conditions that consume variables
// information about `return` statements, recorded in stage 1
struct ERPReturn{
	bool quantum; // under quantum control
	Q!(Id,Expression)[] consumed; // quantum variables consumed by the returned expression
}
ERPReturn[size_t] erpReturns;
SetX!Id[size_t] erpForgettableAtReturn; // quantum variables that can be forgotten before the returned expression is evaluated
SetX!Id[size_t] erpConsumedBeforeReturn; // variables consumed before a `return`, unless the explicit exits keep them (see `erpLoopExplicit`)
// For a long-running host (the language server): drop the early-return elimination state of
// previous checks. `erpNextId` keeps counting, so ids stay unique among nodes that survive a check.
void clearLoopLoweringState(){
	erpJoins=null;
	erpStage1Functions=null;
	erpDivergingLoops=null;
	erpConsumingGuards=null;
	erpReturns=null;
	erpForgettableAtReturn=null;
	erpConsumedBeforeReturn=null;
}
void erpBeforeReturn(ReturnExp ret,Scope sc){
	if(!erpRecording(sc)||!erpKey(ret)) return;
	SetX!Id forgettable,seen;
	auto fun=sc.getFunction();
	for(Scope c=sc;c;c=c.parentScope()){
		foreach(_,d;c.rnsymtab){
			auto vd=cast(VarDecl)d;
			if(!vd||vd.isSemError()||cast(DeadDecl)d||!vd.name) continue;
			if(vd.name.id in seen) continue;
			seen.insert(vd.name.id);
			if(!vd.scope_||vd.scope_.getFunction() !is fun) continue;
			auto type=typeForDecl(vd);
			if(!type||type.isClassical()) continue;
			if(sc.canForget(vd)) forgettable.insert(vd.name.id);
		}
		if(cast(FunctionScope)c) break;
	}
	erpForgettableAtReturn[erpKey(ret)]=forgettable;
	SetX!Id consumed,decided;
	for(Scope c=sc;c;c=c.parentScope()){
		foreach(_,d;c.rnsymtab){
			if(!d.name||d.name.id in decided) continue;
			decided.insert(d.name.id);
			auto cd=cast(ConsumedDecl)d;
			if(cd&&typeid(cd) is typeid(ConsumedDecl)&&!cd.use.moved&&!cd.use.byRef&&cd.use.type&&cd.use.type.isClassical())
				continue; // (the rewritten loop still uses it, so its analysis `dup`s it)
			if(cast(DeadDecl)d) consumed.insert(d.name.id);
		}
		if(cast(FunctionScope)c) break;
	}
	erpConsumedBeforeReturn[erpKey(ret)]=consumed;
}
void erpRecordReturn(ReturnExp ret,Scope sc){
	if(!erpRecording(sc)) return;
	ERPReturn r;
	r.quantum=sc.quantumControlled;
	if(ret.e) visitStm(ret.e,(Expression x){
		if(auto id=cast(Identifier)x)
			if(cast(VarDecl)id.meaning&&id.type&&!id.type.isClassical()&&!id.constLookup&&!id.implicitDup)
				r.consumed~=q(id.id,id.type);
	});
	if(erpKey(ret)) erpReturns[erpKey(ret)]=r;
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
	nb.s=erpExplicitExits(nb.s,fd);
	if(auto ns=erpTransform(nb.s)) nb.s=ns;
	fd.origBody_=nb;
	return true;
}
// Loops whose early returns are all under classical control are rewritten such that the loop itself does not return:
//   `for …{ S1; if c { return e; } S2 }` becomes
//   `done:=false; res:=⊥; for …{ if !done { S1; if c { res:=e; done=true; } if !done { S2 } } } if done { return res; } forget(res=⊥);`
// (`while` conditions are guarded as well). The resulting loop can be split like any other: the loops computing lifted state
// then stop exactly where the original loop returns.
Expression[] erpExplicitExits(Expression[] stms,FunctionDef fd){
	Expression[] r;
	foreach(s;stms){
		if((cast(ForExp)s||cast(WhileExp)s||cast(RepeatExp)s)&&containsReturn(s)){
			if(auto ns=erpLoopExplicit(s,fd)){
				r~=ns;
				continue;
			}
		}else if(auto ite=cast(IteExp)s){
			if(hasLoopWithReturn(ite)){
				ite.then.s=erpExplicitExits(ite.then.s,fd);
				if(ite.othw) ite.othw.s=erpExplicitExits(ite.othw.s,fd);
			}
		}else if(auto ce=cast(CompoundExp)s){
			if(hasLoopWithReturn(ce)) ce.s=erpExplicitExits(ce.s,fd);
		}
		r~=s;
	}
	return r;
}
Expression[] erpLoopExplicit(Expression loop,FunctionDef fd){
	auto R=fd.ret;
	if(!R) return null;
	enum Kind{ unit, quantum, classical }
	Kind kind;
	if(R==unit) kind=Kind.unit;
	else if(isQuantum(R)) kind=Kind.quantum;
	else if(R.isClassical()) kind=Kind.classical;
	else return null; // TODO: mixed classical/quantum return types
	// all returns must be under classical control, consuming only variables with placeholder values
	bool ok=true;
	visitStm(loop,(Expression x){
		if(auto ret=cast(ReturnExp)x){
			auto info=erpKey(ret) in erpReturns;
			if(!info||info.quantum) ok=false;
			else foreach(c;info.consumed) if(!isQuantum(c[1])) ok=false;
		}
	});
	static if(language==silq) visitStm(loop,(Expression x){ // (returns within `do`-`while` loops are not made explicit, TODO)
		if(cast(DoWhileExp)x&&containsReturn(x)) ok=false;
	});
	auto after=erpKey(loop) in erpJoins;
	if(!ok||!after) return null;
	visitStm(loop,(Expression x){ // (variables consumed before a return would need placeholders, TODO)
		if(auto ret=cast(ReturnExp)x){
			auto consumed=erpKey(ret) in erpConsumedBeforeReturn;
			if(!consumed||(*after).any!(v=>v.name in *consumed)) ok=false;
		}
	});
	if(!ok) return null;
	// A `while` condition is evaluated as `¬done && cond`, so that it is not evaluated after the return. If the condition
	// consumes variables, it would then consume them only on some paths: use `cond && ¬done` if the condition cannot fail,
	// and do not rewrite the loop otherwise.
	visitStm(loop,(Expression x){
		if(auto we=cast(WhileExp)x)
			if(erpKey(we) in erpConsumingGuards&&!cannotFail(we.cond)) ok=false;
	});
	if(auto we=cast(WhileExp)loop) if(erpKey(we) in erpConsumingGuards&&!cannotFail(we.cond)) ok=false;
	if(!ok) return null;
	// Consumed variables that are lifted after the loop and can be forgotten at each return consuming them keep their values
	// (the analysis `dup`s them, as they are still used); the others get placeholders. Returns consuming loop-local quantum
	// variables are not supported (TODO).
	bool forgettableAtReturns(Id n){
		bool r=true;
		visitStm(loop,(Expression x){
			if(auto ret=cast(ReturnExp)x) if(erpReturns[erpKey(ret)].consumed.any!(c=>c[0]==n)){
				auto f=erpKey(ret) in erpForgettableAtReturn;
				if(!f||n !in *f) r=false;
			}
		});
		return r;
	}
	bool needsPlaceholder(Id n){
		foreach(v;*after) if(v.name==n) return !v.lifted||!forgettableAtReturns(n);
		ok=false;
		return false;
	}
	visitStm(loop,(Expression x){
		if(auto ret=cast(ReturnExp)x) foreach(c;erpReturns[erpKey(ret)].consumed) needsPlaceholder(c[0]);
	});
	if(!ok) return null;
	auto loc=loop.loc;
	Expression.CopyArgs cargs;
	Identifier mk(Id n){ auto r=new Identifier(n); r.loc=loc; return r; }
	T at(T)(T e){ e.loc=loc; return e; }
	Expression dummy(Expression ty){ return at(new CallExp(mk(Id.s!"__dummy"),ty.copy(cargs),false,false)); }
	auto done=freshName(),res=freshName();
	Expression notDone(){ return at(new UNotExp(mk(done))); }
	Expression[] pre=[at(new DefineExp(mk(done),at(LiteralExp.makeBoolean(false))))];
	final switch(kind){
		case Kind.unit: break;
		case Kind.quantum: pre~=at(new DefineExp(mk(res),dummy(R))); break;
		case Kind.classical:
			pre~=at(new DefineExp(mk(res),at(new TypeAnnotationExp(at(new VectorExp([])),arrayTy(R),TypeAnnotationType.annotation))));
			break;
	}
	Q!(Id,Expression)[] consumedOuter;
	SetX!Id seen;
	visitStm(loop,(Expression x){
		if(auto ret=cast(ReturnExp)x) foreach(c;erpReturns[erpKey(ret)].consumed)
			if(c[0] !in seen&&needsPlaceholder(c[0])){
				seen.insert(c[0]);
				consumedOuter~=c;
			}
	});
	Expression[] exitWith(ReturnExp ret){
		Expression[] r;
		final switch(kind){
			case Kind.unit: break;
			case Kind.quantum:
				r~=at(new ForgetExp(mk(res),dummy(R)));
				r~=at(new DefineExp(mk(res),ret.e));
				break;
			case Kind.classical:
				r~=at(new AssignExp(mk(res),at(new VectorExp([ret.e]))));
				break;
		}
		r~=at(new AssignExp(mk(done),at(LiteralExp.makeBoolean(true))));
		foreach(c;erpReturns[erpKey(ret)].consumed) if(needsPlaceholder(c[0])) r~=at(new DefineExp(mk(c[0]),dummy(c[1])));
		return r;
	}
	Expression[] guard()(Expression[] stms){
		Expression[] r;
		foreach(i,s;stms){
			if(!containsReturn(s)){
				r~=s;
				continue;
			}
			r~=explicitStm(s);
			auto rest=guard(stms[i+1..$]);
			if(rest.length) r~=at(new IteExp(notDone(),at(new CompoundExp(rest)),null));
			break;
		}
		return r;
	}
	CompoundExp guardBlock()(CompoundExp b){
		auto nb=at(new CompoundExp(guard(b.s)));
		nb.loc=b.loc;
		return nb;
	}
	Expression[] explicitStm()(Expression s){
		if(auto ret=cast(ReturnExp)s) return exitWith(ret);
		if(auto ite=cast(IteExp)s){
			ite.then=guardBlock(ite.then);
			if(ite.othw) ite.othw=guardBlock(ite.othw);
			return [ite];
		}
		if(auto ce=cast(CompoundExp)s) return [guardBlock(ce)];
		// loops: skip iterations once done
		CompoundExp loopBody(CompoundExp b){
			auto nb=at(new CompoundExp([at(new IteExp(notDone(),guardBlock(b),null))]));
			nb.loc=b.loc;
			return nb;
		}
		if(auto fe=cast(ForExp)s){ fe.bdy=loopBody(fe.bdy); return [fe]; }
		if(auto re=cast(RepeatExp)s){ re.bdy=loopBody(re.bdy); return [re]; }
		if(auto we=cast(WhileExp)s){
			if(erpKey(we) in erpConsumingGuards) we.cond=at(new AndThenExp(we.cond,notDone()));
			else we.cond=at(new AndThenExp(notDone(),we.cond));
			we.bdy=guardBlock(we.bdy);
			return [we];
		}
		return [s]; // (e.g., `with`: not reached, as returns are not allowed there)
	}
	auto nloop=explicitStm(loop);
	Expression[] exitBlock;
	foreach(c;consumedOuter) exitBlock~=at(new ForgetExp(mk(c[0]),dummy(c[1])));
	final switch(kind){
		case Kind.unit: exitBlock~=at(new ReturnExp(at(new TupleExp([])))); break;
		case Kind.quantum: exitBlock~=at(new ReturnExp(mk(res))); break;
		case Kind.classical: exitBlock~=at(new ReturnExp(at(new IndexExp(mk(res),LiteralExp.makeInteger(0))))); break;
	}
	Expression[] post=[at(new IteExp(mk(done),at(new CompoundExp(exitBlock)),null))];
	if(kind==Kind.quantum) post~=at(new ForgetExp(mk(res),dummy(R)));
	if(erpKey(loop) in erpDivergingLoops) post~=at(new AssertExp(at(LiteralExp.makeBoolean(false)))); // (unreachable)
	return pre~nloop~post;
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
		// unwrap blocks that only anchor `const` forgets of an analyzed loop (see `anchorLoopConstForgets`)
		if(auto cmp=cast(CompoundExp)s)
			if(cmp.s.length==1&&isLoopStatement(cmp.s[0]))
				s=cmp.s[0];
		bool nested=(cast(IteExp)s||cast(CompoundExp)s)&&hasLoopWithReturn(s);
		if(!nested){
			r~=s;
			continue;
		}
		auto rest=stms[i+1..$];
		Expression[] ntail=tail;
		Expression kdef=null;
		if(rest.length){
			auto vars=erpKey(s) in erpJoins;
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
	fd.attributes[Id.s!"silq-join"]=LiteralExp.makeString("join");
	auto call=new CallExp(kname.copy(),new TupleExp(args),false,false);
	call.loc=s.loc;
	auto ret=new ReturnExp(call);
	ret.loc=s.loc;
	tail=[ret];
	return fd;
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

// splices nested blocks used as statements (which are analyzed in the enclosing scope) into the enclosing block
Expression[] flattenStatementBlocks(Expression[] stms){
	Expression[] r;
	foreach(x;stms){
		if(auto ce=cast(CompoundExp)x){
			r~=flattenStatementBlocks(ce.s);
			continue;
		}
		if(auto ite=cast(IteExp)x){ // (also in the branches of conditionals)
			ite.then.s=flattenStatementBlocks(ite.then.s);
			if(ite.othw) ite.othw.s=flattenStatementBlocks(ite.othw.s);
		}
		r~=x;
	}
	return r;
}
