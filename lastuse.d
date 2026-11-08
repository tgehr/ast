// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.lastuse;
import astopt;
import util: SetX, MapX, MapSX;
import util.tuple:Q=Tuple,q=tuple;

import std.range, std.algorithm, std.conv, std.format;
import ast.expression,ast.type,ast.declaration,ast.scope_;

bool canAddForget(Expression e){
	if(auto le=cast(LetExp)e)
		return !!le.isForward(true);
	if(auto ce=cast(CompoundExp)e) // (`[stmt]` or `[stmt, forget(...)]`)
		return !ce.blscope_&&(ce.s.length==1||ce.s.length==2&&cast(ForgetExp)ce.s[1]&&!(cast(ForgetExp)ce.s[1]).val);
	return false;
}

Identifier addForget(Expression e,Declaration decl,Scope sc){
	Identifier addToCompound(CompoundExp ce){
		assert(!ce.blscope_);
		if(ce.s.length==1){
			ForgetExp makeForget(){
				auto tpl=new TupleExp([]);
				tpl.loc=e.loc;
				tpl.constLookup=false;
				tpl.type=unit;
				tpl.setSemCompleted();
				auto fe=new ForgetExp(tpl,null);
				fe.loc=e.loc;
				fe.constLookup=true;
				fe.type=unit;
				fe.setSemCompleted();
				return fe;
			}
			ce.s~=makeForget();
		}
		assert(ce.s.length==2);
		auto fe=cast(ForgetExp)ce.s[1];
		assert(fe&&!fe.val);
		auto id=new Identifier(decl.getId);
		id.loc=e.loc;
		id.scope_=sc;
		id.meaning=decl;
		id.byRef=true;
		id.constLookup=false;
		id.type=id.typeFromMeaning;
		import ast.semantic_:propErr;
		propErr(decl,id);
		id.setSemCompleted();
		auto tpl=cast(TupleExp)fe.var;
		if(!tpl){ // (`forget` in the source, e.g., `let{ x:=e; forget(y); } in x`)
			tpl=new TupleExp([fe.var]);
			tpl.loc=fe.var.loc;
			tpl.constLookup=false;
			tpl.type=fe.var.type?tupleTy([fe.var.type]):null;
			if(fe.var.isSemError()||!tpl.type) tpl.setSemForceError();
			else tpl.setSemCompleted();
			fe.var=tpl;
		}
		tpl.e~=id;
		if(id.type&&tpl.type){
			tpl.type=tupleTy(tpl.e.map!(e=>e.type).array); // TODO: avoid quadratic scaling
        }else tpl.type=null;
		assert(id.type||id.isSemError());
		if(id.isSemError())
			tpl.setSemForceError();
		if(tpl.isSemError())
			fe.setSemForceError();
		if(fe.isSemError())
			e.setSemForceError();
		return id;
	}
	if(auto le=cast(LetExp)e){
		assert(!!le.isForward(true));
		return addToCompound(le.s);
	}
	if(auto ce=cast(CompoundExp)e)
		return addToCompound(ce);
	return null;
}

final class LastUse{
	private this(LastUse.Kind kind,Scope scope_,Declaration decl,Identifier use,Expression parent){
		this.kind=kind;
		this.scope_=scope_;
		this.decl=decl;
		this.use=use;
		this.parent=parent;
	}
	private this(LastUse.Kind kind,Scope scope_,Declaration decl,Identifier use,Expression parent,NestedScope[] nestedScopes){
		this(kind,scope_,decl,use,parent);
		this.nestedScopes=nestedScopes;
	}
	override string toString(){
		string r="LastUse(";
		static foreach(i,alias m;this.tupleof){
			static if(!is(typeof(m):LastUse)){
				static if(i) r~=",";
				r~=text(m);
			}
		}
		r~=")";
		return r;
	}
	LastUse dup(){
		// copies all fields; reference fields (decl, scope_, links, nested
		// scopes) still refer to the original graph—callers remap them as
		// needed (see LastUses.remapFrom)
		auto r=new LastUse(kind,scope_,decl,use,parent,nestedScopes.dup);
		r.constBlock=constBlock;
		r.dep=dep;
		r.depAtSplit=depAtSplit;
		r.forwardTo=forwardTo;
		r.constConsume=constConsume;
		r.prevImplicitDup=prevImplicitDup;
		r.splitFrom=splitFrom;
		r.splitSource=splitSource;
		r.prev=prev;
		r.next=next;
		r.index=index;
		r.consumedComponent=consumedComponent;
		r.loopGuard=loopGuard;
		r.discarded=discarded;
		r.atSplit=atSplit;
		r.time=time;
		r.consumedAt=consumedAt;
		return r;
	}
	enum Kind{
		definition,
		constPinned,
		lazySplitSink,
		lazySplit,
		lazyMerge,
		synthesizedForget,
		implicitDup,
		constUse,
		consumption,
		capture,
	}
	Kind kind; // TODO: sum type?
	bool discarded=false; // (from an analysis that was discarded, see `restoreSnapshot`)
	bool atSplit=false; // (a forget of a version that is not used after its split, which uncomputes it there)
	bool loopGuard=false; // (a use in a `while` condition, which is also evaluated on the path that exits the loop)
	bool cancelableRecorded=false; // (see `recordCancelable`; with the flags together, a `LastUse` fits into the 368-byte size class of the GC)
	size_t time,consumedAt; // (in the order of the analysis, see `LastUses.tick`)
	static bool isBranch(Scope sc){ auto bs=cast(BlockScope)sc; return bs&&bs.isBranch; }
	static bool inBranch(Scope sc){ // (or nested in one)
		for(auto nsc=cast(NestedScope)sc;nsc;nsc=cast(NestedScope)nsc.parent) if(isBranch(nsc)) return true;
		return false;
	}
	static bool interleavable(Scope sc){ auto bs=cast(BlockScope)sc; return bs&&bs.isBranch&&!bs.returningConditional; } // (the code generator can interleave the statements of the branches of its conditional, see `checkBranchOrder`)
	Scope scope_;
	Declaration decl=null;
	Identifier use=null;
	Identifier[] constBlock;
	Expression parent=null;
	auto dep=Dependency(true);
	auto depAtSplit=Dependency(true); // (of a version in a branch: its dependency at the split, which the consumptions in the branches do not change)
	LastUse forwardTo=null;
	LastUse constConsume=null;
	LastUse prevImplicitDup=null;
	BlockScope[] noted; // (the branches that record it as an event, see `noteBranchEvent`)
	LastUse splitFrom=null;
	LastUse splitSource=null;
	NestedScope[] nestedScopes;
	NestedScope[] nestedAfter;
	LastUse prev=null,next=null;
	size_t index; // (in the order the last uses of the scope were added)
	IndexExp consumedComponent=null; // (a consumption allowed because this specific component is not borrowed)

	bool isConsumption(){
		if(!!kind.among(Kind.consumption,Kind.synthesizedForget)) return true;
		if(forwardTo) return forwardTo.isConsumption();
		return false;
	}

	LastUse getSplitFrom()in{
		assert(kind==Kind.lazySplit);
	}do{
		if(splitFrom) return splitFrom;
		auto nsc=cast(NestedScope)scope_;
		assert(!!nsc);
		auto ndecl=nsc.parent.getSplit(decl);
		while(ndecl.splitFrom&&ndecl.splitFrom.scope_.isNestedIn(nsc.parent))
			ndecl=ndecl.splitFrom;
		auto plu=nsc.parent.lastUses.lastUses.get(ndecl,null);
		assert(!!plu,text(ndecl," ",decl," ",nsc.parent.lastUses.lastUses," ",nsc.parent.lastUses.lastUses.get(decl,null)," ",cast(void*)decl," ",cast(void*)ndecl));
		return splitFrom=plu;
	}

	static Declaration versionIn(Declaration decl,NestedScope nsc){
		foreach(d;decl.mergedFrom) if(d.scope_ is nsc) return d;
		foreach(d;decl.splitInto) if(d.scope_ is nsc) return d;
		return decl;
	}
	static bool isNontrivialMerge(Declaration decl,scope NestedScope[] nestedScopes){
		return iota(nestedScopes.length).any!((i){
			auto nsc=nestedScopes[i];
			auto cdecl=decl;
			foreach(d;decl.mergedFrom) if(d.scope_ is nsc) cdecl=d;
			if(decl !is cdecl) return true;
			auto nlu=nsc.lastUses.lastUses.get(cdecl,null);
			if(!nlu) return false;
			while(nlu.forwardTo) nlu=nlu.forwardTo;
			if(nlu.kind!=Kind.lazySplit) return true;
			return false;
		});
	}
	static Forgettability getMergeForgettability(Declaration decl,scope NestedScope[] nestedScopes,bool forceHere,bool forceConsumed=false){
		//imported!"util.io".writeln("CAN FORGET MERGE: ",decl," ",cast(void*)decl.scope_," ",decl.mergedFrom," ",nestedScopes.map!(sc=>cast(void*)sc));
		return iota(nestedScopes.length).map!((i){
			auto nsc=nestedScopes[i];
			auto cdecl=versionIn(decl,nestedScopes[i]);
			//imported!"util.io".writeln("CHECKING: ",decl," ",nsc.lastUses.getForgettability(cdecl,forceHere,false)," ",nsc.lastUses.getForgettability(decl,forceHere,false)," ",nsc.lastUses.lastUses.get(cdecl,null)," ",cdecl is decl);
			return nsc.lastUses.getForgettability(cdecl,forceHere,forceConsumed);
		}).fold!((a,b){
			auto r=min(a,b);
			if(r==Forgettability.none) return r;
			if(a==Forgettability.consumable||b==Forgettability.consumable) return Forgettability.consumable;
			return r;
		})(Forgettability.forgettable);
	}
	static bool canForgetMerge(Declaration decl,scope NestedScope[] nestedScopes,bool forceHere,bool forceConsumed){
		return getMergeForgettability(decl,nestedScopes,forceHere,forceConsumed)>=(forceConsumed?Forgettability.consumable:Forgettability.forgettable);
	}
	static bool mergesSameValue(Declaration decl,NestedScope nsc){ // (as `decl.isDerivedFrom(versionIn(decl,nsc).canonicalSource)`, but without going through the merges of the same value of all earlier conditionals)
		return decl.canonicalSource is versionIn(decl,nsc).canonicalSource;
	}
	static bool canCancelImplicitDupMerge(Declaration decl,scope NestedScope[] nestedScopes){
		return iota(nestedScopes.length).map!((i){
			auto nsc=nestedScopes[i];
			if(!mergesSameValue(decl,nsc)) return false;
			auto cdecl=versionIn(decl,nestedScopes[i]);
			return nsc.lastUses.canCancelImplicitDup(cdecl);
		}).any;
	}

	void remove(){
		assert(!prev||prev.next is this);
		assert(!next||next.prev is this);
		if(prev) prev.next=next;
		if(next) next.prev=prev;
		if(prev) prev.nestedAfter~=nestedAfter;
		nestedAfter=[];
		prev=next=null;
	}
	void prepend(LastUse prev)in{
		assert(!this.prev);
		assert(!prev.next);
	}do{
		this.prev=prev;
		prev.next=this;
		// TODO: perform necessary updates
	}
	void append(LastUse next)in{
		assert(!this.next);
		assert(!next.prev);
	}do{
		this.next=next;
		next.prev=this;
		// TODO: perform necessary updates
		//imported!"util.io".writeln("APPENDING: ",this," ⇒ ",next);
	}

	void pin(){
		if(forwardTo) forwardTo.pin();
		if(splitFrom) splitFrom.pin();
		if(isConsumption()) return;
		//imported!"util.io".writeln("PINNING: ",this);
		kind=Kind.constPinned;
	}
	void pinHere(){ // (not the versions it is split from)
		if(forwardTo) forwardTo.pinHere();
		if(isConsumption()) return;
		kind=Kind.constPinned;
	}

	private void removeFromUnusedSiblings(){
		auto nsc=cast(NestedScope)scope_;
		if(!nsc) return;
		foreach(sib;nsc.getSiblingScopes()){
			if(sib is nsc) continue;
			if(sib.rnsymtab.get(decl.getId,null) !is decl) continue;
			auto slu=sib.lastUses.lastUses.get(decl,null);
			while(slu&&slu.kind==Kind.lazySplitSink) slu=slu.forwardTo;
			if(!slu||slu.kind!=Kind.lazySplit||slu.forwardTo) continue;
			sib.symtabRemove(decl);
			slu.markConsumed(null,false);
		}
	}
	private void markConsumed(Identifier theUse,bool isForget,bool fromNested=false,IndexExp component=null,bool copy=false,Scope from=null){ // (`copy`: of a version that an enclosing scope consumes; `from`: the nested scope that consumes it)
		if(!use) use=theUse;
		if(!consumedComponent&&use is theUse) consumedComponent=component; // (consumed by the same use)
		//imported!"util.io".writeln("MARKING CONSUMED: ",this," ",use?text(use.loc):"<?>");
		if(isConsumption()) return;
		auto unread=kind==Kind.definition&&!splitFrom&&!splitSource&&!decl.splitInto.length; // (no other dependency mentions the variable, see `updateDependenciesOnConsumptionLocal`)
		if(splitSource&&splitSource.splitFrom)
			splitSource.splitFrom.markConsumed(theUse,false,true,component,false,scope_);
		if(splitFrom) splitFrom.markConsumed(theUse,false,true,component,false,scope_);
		if(isForget){
			assert(!dep.isTop);
			kind=Kind.synthesizedForget;
			scope_.noteDependencyResolved(dep);
		}else kind=Kind.consumption;
		consumedAt=fromNested?scope_.lastUses.tick():time; // (a nested scope consumes it now)
		if(!fromNested&&!copy) noteBranchEvent();
		recordCancelable();
		if(fromNested&&isBranchSplit()) updateDependenciesOnConsumption(from); // (consumed in a nested scope)
		else if(!unread||fromNested) updateDependenciesOnConsumptionLocal(!fromNested);
	}
	private void noteBranchEvent(){ // (for the order of the branches of the enclosing conditionals, see `checkBranchOrder`)
		void note(BlockScope bs){
			if(!isBranch(bs)) return;
			noted~=bs;
			if(kind==Kind.synthesizedForget) bs.uncomputations~=this;
			else if(auto outer=outerVersion(decl,bs)) bs.outerConsumptions~=q(outer,this);
		}
		for(auto nsc=cast(NestedScope)scope_;nsc;nsc=cast(NestedScope)nsc.parent){
			note(cast(BlockScope)nsc);
			foreach(bs;nsc.continuedBranches) note(bs);
		}
	}
	private static Declaration sourceVersion(Declaration x,bool continued){ // (`continued`: also the version of the branch that the code after a nested conditional whose other branch returns continues)
		return x.splitFrom?x.splitFrom:continued&&x.mergedFrom.length==1?x.mergedFrom[0]:null;
	}
	static Declaration outerVersion(Declaration d,NestedScope sc,bool continued=false){ // (the version of a variable of the enclosing scope of `sc` that `d` is split from, or that is split from `d`; `continued`: also through the code after nested conditionals whose other branch returns)
		while(d&&d.scope_&&d.scope_.isNestedIn(sc)) d=sourceVersion(d,continued);
		while(d&&d.scope_&&d.scope_ !is sc.parent&&d.scope_.isNestedIn(sc.parent)) d=d.splitFrom; // (in the code after the conditional, see `continuedBranches`)
		if(d&&d.scope_ is sc.parent&&d.mergedFrom.length==1&&d.mergedFrom[0].scope_ is sc){ // (the version of the branch, which the code after the conditional continues)
			d=d.mergedFrom[0];
			while(d&&d.scope_&&d.scope_.isNestedIn(sc)) d=d.splitFrom;
		}
		if(d&&d.scope_&&d.scope_ !is sc.parent&&sc.parent.isNestedIn(d.scope_)) d=sc.parent.getSplit(d); // (a version from further out)
		return d&&d.scope_ is sc.parent?d:null;
	}
	static BlockScope splitBranch(LastUse lu){ // (the innermost branch that splits the variable from its enclosing scope, through blocks that run once)
		for(auto nsc=cast(NestedScope)lu.scope_;nsc;nsc=cast(NestedScope)nsc.parent){
			auto bs=cast(BlockScope)nsc;
			if(!bs||bs.isLoopBody||bs.isLoopEntry||bs.isLoopReset) return null;
			if(bs.isBranch&&outerVersion(lu.decl,bs)) return interleavable(bs)?bs:null;
		}
		return null;
	}
	Q!(LastUse,Dependency)[] cancelable; // (last uses that could have been cancelled when this consumption happened, with their dependencies at that time)
	private void recordCancelable(){ // (only those that depend on `decl` indirectly, the others are cancelled directly)
		if(cancelableRecorded) return; // (an implicit `dup` that is cancelled later consumes at the time of the `dup`)
		cancelableRecorded=true;
		static bool version_(Declaration x,Declaration y){ return x is y||x.isSplitFrom(y)||y.isSplitFrom(x); }
		Declaration[] reached=[decl];
		LastUse[] indirect;
		auto candidates=scope_.lastUses.orderedCancelCandidates();
		for(bool changed=true;changed;){
			changed=false;
			foreach(d;candidates){
				auto lu=scope_.lastUses.lastUses[d];
				while(lu.forwardTo) lu=lu.forwardTo;
				if(lu is this||lu.dep.isTop||reached.canFind(d)) continue;
				bool viaReached=false,direct=false;
				foreach(x;lu.dep.dependencies){
					if(reached.any!(y=>version_(x,y))) viaReached=true;
					if(version_(x,decl)) direct=true;
				}
				if(!viaReached) continue;
				if(!direct) indirect~=lu;
				reached~=d;
				changed=true;
			}
		}
		foreach(lu;indirect) if(lu.canCancelImplicitDup()) cancelable~=q(lu,lu.dep.dup);
	}
	private static Identifier cancelUse(LastUse lu){ // (where `lu` goes out of scope if cancelled)
		if(lu.use) return lu.use;
		if(lu.constConsume) return cancelUse(lu.constConsume);
		foreach(nsc;lu.nestedScopes)
			if(auto nlu=nsc.lastUses.get(versionIn(lu.decl,nsc),true))
				if(auto r=cancelUse(nlu)) return r;
		return null;
	}
	static LastUse lostDependency(LastUse lu){ // (a last use, also of a version in a branch of a merge, whose dependency was lost through a known consumption, e.g., `x⊕=y` in `t:=x⊕c; if k==1 { u:=dup(t); x⊕=y; }`)
		while(lu.forwardTo) lu=lu.forwardTo;
		if(lu.dep.isTop&&lu.dep.lostVar) return lu;
		foreach(nsc;lu.nestedScopes)
			if(auto nlu=nsc.lastUses.get(versionIn(lu.decl,nsc),true))
				if(auto r=lostDependency(nlu)) return r;
		return null;
	}
	private bool forgottenOutside(){ // (by the same forget in an enclosing scope)
		if(!use) return false;
		for(auto lu=this;;){
			while(lu.forwardTo) lu=lu.forwardTo;
			if(!lu.splitFrom) return false;
			lu=lu.splitFrom;
			if(lu.isConsumption()&&lu.use is use) return true;
		}
	}
	private bool isBranchSplit(){
		return decl.splitFrom&&decl.splitFrom.splitInto.length>1&&decl.splitFrom.splitInto.canFind(decl);
	}
	private void updateDependenciesOnConsumption(Scope from=null){
		//imported!"util.io".writeln("UPDATING ALL: ",this);
		if(auto parent=decl.splitFrom){
			assert(parent.splitInto.canFind(decl));
			foreach(split;parent.splitInto){
				if(split !is decl&&interleavable(split.scope_)&&dep.isTop) continue; // (the other branches keep the version from before the split, see `checkBranchOrder`)
				if(auto lu=split.scope_.lastUses.get(split,true)){
					if(auto source=lu.splitSource)
						lu=source;
					lu.updateDependenciesOnConsumptionLocal(true,parent.splitInto.length>1,this,from); // (including forgets in nested scopes of the branches)
				}
			}
		}else updateDependenciesOnConsumptionLocal();
	}
	private static bool isClassicalDecl(Declaration d){ // (it depends on quantum values only through control)
		import ast.semantic_:typeForDecl;
		auto ty=typeForDecl(d);
		return ty&&ty.isClassical();
	}
	private bool definedInScope(Declaration d){ // (also the versions that it is derived from, see `Declaration.derivedSequence`)
		SetX!Declaration visited;
		bool visit(Declaration x){ // (stops at the first one that is not, e.g., a version from before the split)
			if(!x.scope_||!x.scope_.isNestedIn(scope_)) return false;
			if(x in visited) return true;
			visited.insert(x);
			if(x.splitFrom&&!visit(x.splitFrom)) return false;
			return x.mergedFrom.all!visit;
		}
		return visit(d);
	}
	private bool readSplitAtDefinition(Declaration d,ref Dependency forgetDep){
		return readsSplitAtDefinition(scope_,decl,d,forgetDep);
	}
	static bool readsSplitAtDefinition(Scope scope_,Declaration decl,Declaration d,ref Dependency forgetDep,bool continued=false){ // (whether the definition of `d` in `scope_` reads a version of `decl` in it, and depends on it only that way; `continued`: see `outerVersion`)
		bool version_(Declaration x,Declaration y){
			static bool derived(Declaration x,Declaration y,bool continued){
				for(;x;x=sourceVersion(x,continued)) if(x is y) return true;
				return false;
			}
			return derived(x,y,continued)||derived(y,x,continued);
		}
		bool inScope(Declaration x){ return x.scope_&&x.scope_.isNestedIn(scope_); }
		SetX!Declaration visited;
		bool reads=false;
		bool present(Declaration x){ // (not consumed before the forget)
			if(forgetDep.isTop) return false;
			foreach(y;forgetDep.dependencies) if(version_(y,x)) return true;
			return false;
		}
		bool isOuter(Declaration x){ // (a value from before the split, possibly split further)
			for(;x;x=x.splitFrom) if(!inScope(x)) return true;
			return false;
		}
		static Declaration current(Declaration x){ // (a merged version from an earlier fixed-point iteration of a loop stands for the one its splits were moved to, see `fixLoopSplitMergeGraph`)
			while(x.splitInto.length&&x.splitInto[0].splitFrom&&x.splitInto[0].splitFrom !is x) x=x.splitInto[0].splitFrom;
			return x;
		}
		bool ok(Declaration x){ // (read by the definitions)
			x=current(x);
			if(isClassicalDecl(x)) return true;
			if(version_(x,decl)){
				reads=true;
				return true;
			}
			if(present(x)) return true; // (read at the forget, its definition is not undone)
			if(isOuter(x)){ // (only if it was consumed with a known dependency, which has to be read instead, e.g., `f` for `t:=dup(x)&f; forget(f); forget(t);` in a branch)
				if(x in visited) return true;
				visited.insert(x);
				auto lu=x.scope_?x.scope_.lastUses.get(x,true):null;
				while(lu&&lu.forwardTo&&!lu.kind.among(Kind.consumption,Kind.synthesizedForget)) lu=lu.forwardTo; // (e.g., the last use before a conditional, consumed in a branch)
				if(!lu||!lu.isConsumption()||lu.dep.isTop) return false;
				foreach(y;lu.dep.dependencies) if(version_(y,decl)||!ok(y)) return false;
				return true;
			}
			if(x in visited) return true;
			visited.insert(x);
			if(x.splitFrom) return ok(x.splitFrom);
			auto s=x.definitionSources;
			if(!s.known) return false;
			foreach(r;s.reads) if(!ok(r)) return false;
			foreach(c;s.consumes){ // (re-created by undoing the definition)
				if(isClassicalDecl(c[0])) continue;
				if(version_(current(c[0]),decl)) return false;
				if(isOuter(current(c[0]))){ // (its dependency has to be read instead)
					if(c[1].isTop) return false;
					foreach(y;c[1].dependencies) if(version_(y,decl)||!ok(y)) return false;
				}else if(!ok(c[0])) return false;
			}
			return true;
		}
		return ok(d)&&reads;
	}
	private void updateDependenciesOnConsumptionLocal(bool descend=true,bool fromBranch=false,LastUse consumption=null,Scope from=null){ // (`from`: the nested scope that consumes it, whose conditional updates the last uses in its branches with the dependency there)
		//imported!"util.io".writeln("UPDATING DEPENDENCIES FROM: ",this);
		// TODO: perform necessary updates
		auto cdep=dep.dup;
		if(!consumption) consumption=this;
		if(cdep.isTop&&!cdep.lostVar&&consumption.use){
			cdep.lostVar=consumption.decl;
			cdep.lostAt=consumption.use;
		}
		auto start=next;
		if(splitFrom){
			if(fromBranch){ // (all last uses in the branch, including those merged from nested scopes)
				start=scope_.lastUses.lastLastUse;
				while(start&&start.prev) start=start.prev;
				if(!start) start=this;
			}else for(start=this;start&&start.prev&&start.prev.splitFrom;)
				start=start.prev; // TODO: this is a hack, would be better to insert lazy splits in dependency order
		}
		auto branch=cdep.isTop?splitBranch(consumption):null; // (the uncomputations before the consumption keep their dependencies, see `checkBranchOrder`)
		auto fromConditional=from&&splitBranch(consumption)?from:null; // (not in loop bodies, whose next iterations come after the consumption)
		bool before(LastUse lu){ return branch&&lu.time<consumption.consumedAt&&lu.scope_.isNestedIn(branch)&&lu.kind!=Kind.consumption&&!(lu.use&&lu.use.implicitDup); } // (not consumptions of `const` variables and implicit `dup`s, whose variables are forgotten later)
		bool goneBefore(LastUse lu){ // (the variable of an implicit `dup` is consumed or forgotten later, but before the consumption, e.g., `o` in `t:=(measure(o),measure(o)); y:=H(x);` for `o:=dup(x)`, also in another branch)
			if(!(lu.use&&lu.use.implicitDup)) return false;
			auto last=lu.scope_.lastUses.lastUses.get(lu.decl,null);
			return last&&last !is lu&&last.isConsumption()&&last.time<consumption.consumedAt;
		}
		SetX!LastUse visited;
		static void replaceVersions(ref Dependency dep,Declaration d,Dependency by,Identifier consumedAt=null){
			if(dep.isTop) return;
			Declaration[] xs;
			foreach(x;dep.dependencies) if(x is d||x.isSplitFrom(d)||d.isSplitFrom(x)) xs~=x;
			foreach(x;xs) dep.replace(x,by,consumedAt);
		}
		static bool hasVersion(ref Dependency dep,Declaration d){
			if(dep.isTop) return false;
			foreach(x;dep.dependencies) if(x is d||x.isSplitFrom(d)||d.isSplitFrom(x)) return true;
			return false;
		}
		MapX!(Id,Q!(Identifier,Identifier,Identifier,Scope,Scope,Declaration)) outOfScope; // (where a variable goes out of scope, the implicit `dup` before that, the consumption that causes it, the scopes of later uses and of going out of scope, and the version that goes out of scope)
		static bool onOtherPath(Scope a,Scope b){ // (in different branches of the same conditional)
			for(auto x=cast(NestedScope)a;x;x=cast(NestedScope)x.parent)
				for(auto y=cast(NestedScope)b;y;y=cast(NestedScope)y.parent)
					if(x.parent is y.parent) return x !is y&&x.getSiblingScopes().canFind(y);
			return false;
		}
		void walk(LastUse start,Dependency cdep,bool nested,Dependency atSplit,NestedScope level){ // (`atSplit`: the dependency at the split into `level`, for the forgets there)
		auto beforeSplits=cdep.dup; // (before the splits into the next nested scopes)
		for(auto lu=start;lu;lu=lu.next){
			scope(success){
				if(!lu.forwardTo) beforeSplits=cdep.dup; // (not one of the splits, which precede the nested scopes)
				if(descend) foreach(nsc;lu.nestedAfter){
					if(nsc.lastUses.discarded) continue;
					if(fromConditional&&nsc.getSiblingScopes().any!(s=>fromConditional.isNestedIn(s))) continue;
					auto head=nsc.lastUses.lastLastUse;
					if(!head) continue;
					while(head.prev) head=head.prev;
					walk(head,cdep.dup,true,beforeSplits.dup,nsc);
				}
			}
			if(lu is this||lu.discarded||before(lu)||goneBefore(lu)) continue;
			if(splitFrom&&!fromBranch&&lu.kind==Kind.synthesizedForget&&lu.time<consumption.consumedAt) continue; // (forgotten before the consumption, e.g., in a block whose lazy splits come before it: the walk starts at them)
			visited.insert(lu);
			if(lu.decl&&lu.use&&!lu.use.isSemError()){
				auto oos=outOfScope.get(lu.decl.getId,Q!(Identifier,Identifier,Identifier,Scope,Scope,Declaration).init);
				if(oos[2]&&lu.scope_.isNestedIn(oos[3])&&!onOtherPath(lu.scope_,oos[4])&&lu.use !is oos[0]&&lu.use !is oos[1]&&(lu.decl is oos[5]||lu.decl.isDerivedFrom(oos[5]))){ // (used after it went out of scope)
					import ast.semantic_:undefinedIdentifierError;
					lu.use.setSemForceError();
					lu.decl.setSemForceError();
					undefinedIdentifierError(lu.use,[new OutOfScopeDecl(lu.decl,oos[0],oos[2],oos[1])],lu.scope_);
					outOfScope.remove(lu.decl.getId);
				}
			}
			if(lu.forwardTo&&lu.forwardTo.isConsumption()&&lu.forwardTo !is this&&lu.forwardTo !in visited) continue;
			if(lu.kind==Kind.synthesizedForget&&lu.forgottenOutside()) continue; // (checked where it is forgotten)
			if(lu.isConsumption()&&lu.splitFrom&&lu.splitFrom.isConsumption()&&lu.splitFrom !is this&&lu.splitFrom !in visited&&lu.kind!=Kind.synthesizedForget) continue; // (a forget in the branch itself is checked here)
			if(splitFrom&&(fromBranch||!isConsumption())&&lu.decl&&definedInScope(lu.decl)&&(isClassicalDecl(lu.decl)||readSplitAtDefinition(lu.decl,lu.dep))) continue;
			if(!nested&&lu.atSplit){ // (its dependency is the one at the split, which comes before the consumption)
				cdep.replace(lu.decl,lu.dep,lu.use);
				continue;
			}
			auto byAtSplit=nested&&lu.scope_ is level&&isBranch(level)?atSplit:cdep; // (for the forgets at the split: `decl` is consumed before the split)
			if(nested&&lu.kind==Kind.lazySplit) replaceVersions(lu.depAtSplit,decl,byAtSplit);
			//imported!"util.io".writeln("VISITING: ",lu," ",decl," ",cdep," ",use?text(use.loc):"<?>");
			if(nested) replaceVersions(lu.dep,decl,lu.atSplit?byAtSplit:cdep);
			else lu.dep.replace(decl,cdep);
			//imported!"util.io".writeln("REPLACED: ",lu," ",decl," ",cdep);
			if(lu.kind.among(Kind.consumption,Kind.synthesizedForget)||lu.use&&lu.use.implicitDup){
				if(lu.kind==Kind.synthesizedForget) lu.scope_.noteDependencyResolved(lu.dep);
				if(lu.use) foreach(c;lu.cancelable){ // (a last use that would have been cancelled here if the dependency through `decl` had been known)
					auto prev=c[0],id=prev.decl.getId;
					if(id==lu.decl.getId||id in outOfScope||!hasVersion(c[1],decl)) continue;
					auto ndep=c[1].dup;
					replaceVersions(ndep,decl,cdep);
					if(!hasVersion(ndep,lu.decl)) continue;
					replaceVersions(ndep,lu.decl,lu.dep,lu.use);
					if(!ndep.isTop) continue;
					auto at=cancelUse(prev);
					auto dupUse=prev.prevImplicitDup?prev.prevImplicitDup.use:null;
					outOfScope[id]=q(at?at:lu.use,dupUse,lu.use,lu.scope_,prev.scope_,prev.decl);
				}
				if(nested) replaceVersions(cdep,lu.decl,lu.dep,lu.use);
				else cdep.replace(lu.decl,lu.dep,lu.use);
				if(!lu.decl.isSemError()&&lu.isConsumption()){
					//imported!"util.io".writeln("CHECKING: ",lu," ",lu.use?text(lu.use.loc):"<?>"," ",lu.constBlock);
					lu.checkConsumable();
				}
				if(!lu.decl.isSemError()&&lu.dep.isTop){
					if(lu.kind==Kind.synthesizedForget){
						lu.reportUnforgettable();
					}else if(!lu.decl.isSemError()&&lu.use&&lu.use.implicitDup){
						//imported!"util.io".writeln("FOUND CANCELABLE DUP AT: ",lu.use.loc);
						if(auto vd=cast(VarDecl)lu.decl) if(!vd.outOfScopeCause) vd.outOfScopeCause=lu.dep.lostAt;
						if(lu.dep.lostAt&&lu.decl.getId !in outOfScope) outOfScope[lu.decl.getId]=q(lu.use,Identifier.init,lu.dep.lostAt,scope_,lu.scope_,lu.decl); // (the `dup` would not have been implicit if the dependency through `decl` had been known)
						lu.cancelImplicitDup();
					}
				}
			}
		}
		}
		walk(splitFrom?start:this,cdep,false,cdep,null);
	}

	private void reportUnforgettable(){ // (a forget whose dependency is unknown)
		if(use&&use.scope_&&cast(ForgetExp)parent){
			scope_.error(format("cannot synthesize forget expression for `%s`",use),use.loc);
			scope_.explainUnknownDependency(decl,dep);
		}else if(use && use.isSemError()){
			// already reported
		}else if(decl.scope_){
			auto d=decl,sc=decl.scope_;
			if(cast(Parameter)d) sc.error(format("%s `%s` is not consumed (perhaps return it or annotate it `const`)",d.kind,d.getName),d.loc);
			else sc.error(format("%s `%s` is not consumed (perhaps return it)",d.kind,d.getName),d.loc);
			if(cast(ReturnExp)parent) sc.note("at function return",parent.loc);
			else if(use) sc.note("cannot be forgotten after its last use here",use.loc);
			sc.explainUnknownDependency(d,dep);
		}else if(use && use.scope_){
			scope_.error(format("cannot synthesize forget expression for `%s`",use),use.loc);
		}
		decl.setSemForceError();
		if(use) use.setSemForceError();
		if(parent) parent.setSemForceError();
		// TODO: the error has to be propagated out further
	}

	bool checkConsumable(){
		//imported!"util.io".writeln(constBlock.map!(id=>id.loc)," ",use?text(use.loc):"<?>");
		auto nconstBlock=constBlock.length?constBlock[$-1]:null;
		if(!nconstBlock){
			if(auto nsc=cast(NestedScope)scope_){
				nconstBlock=nsc.parent.isConst(decl); // TODO: should not be needed
				//imported!"util.io".writeln("???? ",decl," ",use?text(use.loc):"<?>",nconstBlock is decl," ",scope_ is decl.scope_," ",nsc.parent is decl.scope_," ",this);
			}
		}
		if(nconstBlock) scope_.noteDependencyResolved(dep);
		static if(language==silq)
			if(nconstBlock&&consumedComponent&&scope_.componentConstBlocksAllow(decl,consumedComponent,use.loc))
				nconstBlock=null;
		if(nconstBlock&&dep.isTop){
			if(!use){
				scope_.error(format("variable `%s` is not consumed",decl.getName),decl.loc);
				// TODO: needs a note indicating the end of scope
			}else if(nconstBlock !is use){
				scope_.error(format("cannot consume `const` %s `%s`",decl.kind,use), use.loc);
				scope_.note(format("%s was made `const` here", decl.kind), nconstBlock.loc);
			}else{
				import ast.semantic_:nonLiftedError;
				nonLiftedError(use,scope_); // TODO: would be better to locate this around the enclosing `const` expression
			}
			decl.setSemForceError();
			if(use) use.setSemForceError();
			return false;
		}
		return true;
	}
	bool consume(bool isForget){
		assert(!forwardTo);
		if(kind==Kind.synthesizedForget) return false;
		if(kind==Kind.consumption) return false;
		bool ok=checkConsumable();
		if(kind==Kind.lazySplit){
			auto lu=getSplitFrom();
			assert(!!lu);
		}
		/+imported!"util.io".writeln("CONSUMING: ",this);
		scope(exit) imported!"util.io".writeln("CONSUMED: ",this);+/
		assert(!use||use.meaning is decl);
		auto csc=cast(NestedScope)scope_;
		assert(csc&&csc.isNestedIn(decl.scope_));
		for(;csc;csc=cast(NestedScope)csc.parent){
			auto cdecl=csc.getSplit(decl);
			if(auto d=csc.rnsymtab.get(decl.getId,null)){
				if(d !is cdecl){
					csc.symtabRemove(d);
					csc.reinsert(cdecl);
					if(!cast(DeadDecl)d) // (a marker of a consumption is only in the tables, see `recordConsumption`)
						csc.replaceDecl(d,cdecl,!(d.scope_&&d.scope_ !is csc&&d.scope_.isNestedIn(csc))); // (while merging, the table holds a branch's version, which stays in the branch)
				}
			}else csc.reinsert(cdecl);
			if(csc is decl.scope_) break;
		}
		Declaration result=scope_.getSplit(decl);
		Identifier[] oldConstBlock;
		if(constBlock.length){
			if(auto prop=scope_.updateDeclProps(decl)){
				oldConstBlock=prop.constBlock;
				prop.constBlock=constBlock;
			}
		}
		result=scope_.consume(result,use);
		if(!use&&explanationUse) scope_.recordConsumption(result,explanationUse);
		if(constBlock.length) scope_.updateDeclProps(decl).constBlock=oldConstBlock;
		assert(!!result);
		scope_.unsplit(result);
		assert(scope_.getSplit(decl) is result);
		if(use&&use.meaning is decl) use.meaning=result; // TODO: this is a bit hacky
		assert(!use||use.meaning is result);
		void removeCopies(Scope sc){
			foreach(nested;sc.activeNestedScopes){ // TODO: need to consider nested scopes at correct time
				if(nested.forgottenVarsOnEntry.canFind(result)){
					nested.forgottenVarsOnEntry=nested.forgottenVarsOnEntry.filter!(d=>d!is result).array; // TODO: make more efficient
				}
				auto copy=nested.rnsymtab.get(result.getId,null);
				if(copy&&copy !is result&&!result.splitSequence.canFind(copy)&&!copy.isSplitFrom(result)) copy=null;
				if(copy){
					nested.symtabRemove(copy);
					if(copy is result||nested.dependencyTracked(copy))
						nested.pushDependencies(copy,false);
					if(use&&!use.constLookup&&!use.implicitDup)
						nested.recordConsumption(copy,use);
					if(auto lu=nested.lastUses.get(copy,true))
						lu.markConsumed(use,isForget&&!lu.dep.isTop,false,null,true);
				}
				if(nested.forgottenVars.canFind(result)){
					nested.forgottenVars=nested.forgottenVars.filter!(d=>d!is result).array; // TODO: make more efficient
				}
				nested.checkDeclarationCancel(copy?copy:result,use);
				removeCopies(nested);
			}
		}
		removeCopies(scope_);
		for(auto inner=cast(NestedScope)scope_;inner&&inner !is decl.scope_;inner=cast(NestedScope)inner.parent)
			if(!inner.parent.activeNestedScopes.canFind(inner)) removeCopies(inner.parent); // (nested scopes after `inner` that are still being analyzed)
		markConsumed(use,isForget);
		return ok;
	}

	static enum Forgettability{
		none,
		forgettable,
		consumable,
	}

	bool canForget(bool forceConsumed,ReturnExp earlyReturn=null,bool enclosing=false){
		return getForgettability(forceConsumed,earlyReturn,enclosing)>=(forceConsumed?Forgettability.consumable:Forgettability.forgettable);
	}

	bool canForgetBeforeLoops(bool forceConsumed,ReturnExp earlyReturn){ // (a forget on entry of a loop body has to be moved before the loop)
		for(auto lu=this;lu&&lu.kind==Kind.lazySplit;lu=lu.splitFrom)
			if(auto bs=cast(BlockScope)lu.scope_) if(bs.isLoopBody)
				if(lu.splitFrom.getForgettability(forceConsumed,earlyReturn)==Forgettability.none) return false;
		return true;
	}
	bool atLoopEntry(){
		auto bs=cast(BlockScope)scope_;
		return bs&&bs.isLoopEntry;
	}
	bool forgettableAtSplit(ReturnExp earlyReturn,bool enclosing){ // (a version in a branch, e.g., at an early return after the branch consumed what it depends on, rather than before the split, as it may be used after the conditional; not at an early return in a nested scope (`enclosing`), after which the branch may continue on another path, e.g., `u` for `if c { if d { return x; } forget(u); }`)
		return kind==Kind.lazySplit&&isBranch(scope_)&&!depAtSplit.isTop&&!(earlyReturn&&enclosing);
	}
	bool isLastSplitSibling(){
		auto nsc=cast(NestedScope)scope_;
		assert(!!nsc);
		auto siblings=nsc.getSiblingScopes();
		foreach(ssc;siblings){
			if(ssc is nsc) continue;
			auto ndecl=decl;
			if(decl.scope_ is scope_ && decl.splitFrom && decl.splitFrom.scope_ is nsc.parent)
				ndecl=decl.splitFrom;
			ndecl=ssc.getSplit(ndecl);
			//imported!"util.io".writeln("CHECKING SIBLINGS: ",ssc.forgottenVarsOnEntry," ",decl," ",ndecl," ",ssc.forgottenVarsOnEntry.canFind(ndecl)," ",ssc.forgottenVarsOnEntry.canFind(decl)," ",decl.scope_ is this," ",decl.splitFrom," ",decl.splitFrom&&decl.splitFrom.scope_ is nsc.parent);
			if(ssc.forgottenVarsOnEntry.canFind(ndecl)) continue;
			if(auto bs=cast(BlockScope)ssc) if(bs.isLoopBody&&bs.diverges){ // (a loop body that diverges without using the variable, which `closeUnreachable` only drops)
				auto slu=ssc.lastUses.lastUses.get(ndecl,null);
				if(slu&&slu.kind==Kind.lazySplit&&!slu.forwardTo&&!slu.use) continue;
			}
			return false;
		}
		return true;
	}

	Forgettability getForgettability(bool forceConsumed,ReturnExp earlyReturn=null,bool enclosing=false){
		import ast.semantic_:typeConstBlocked;
		if(typeConstBlocked(decl,scope_)) return Forgettability.none;
		if(forwardTo) return forwardTo.getForgettability(forceConsumed,earlyReturn,enclosing);
		//imported!"util.io".writeln("GETTING FORGETTABILITY: ",this);
		if(kind.among(Kind.consumption,Kind.capture)) return Forgettability.none; // (their uses can be in nested scopes, e.g., the consumption of the version in a loop body)
		if(use&&!scope_.canSplit(use.meaning)) return Forgettability.none;
		final switch(kind)with(Kind){
			case definition:
				goto case constUse;
			case constPinned:
				return Forgettability.none;
			case lazySplitSink:
				return Forgettability.none;
			case lazySplit:
				assert(!!splitFrom);
				auto r=Forgettability.none;
				if(forceConsumed||isLastSplitSibling()||earlyReturn&&dep.isTop&&!forgettableAtSplit(earlyReturn,enclosing)||atLoopEntry())
					r=max(r,splitFrom.getForgettability(forceConsumed,earlyReturn,!!earlyReturn));
				if(r==Forgettability.none&&(!dep.isTop||forgettableAtSplit(earlyReturn,enclosing))&&scope_.canSplit(decl)&&canForgetBeforeLoops(forceConsumed,earlyReturn))
					r=Forgettability.forgettable; // (on entry, also at the split if the branch consumes what it depends on)
				//imported!"util.io".writeln("RESULT: ",r);
				return r;
			case lazyMerge:
				auto r=getMergeForgettability(decl,nestedScopes,true,forceConsumed);
				foreach(nsc;nestedScopes){
					foreach(ssc;nsc.siblingScopes){
						if(auto bs=cast(BlockScope)ssc){
							if(bs.isLoopBody&&bs.diverges){ // (forgets in the scope of the path that skips such a loop are not generated: the variable can only be forgotten before the loop)
								auto nlu=nsc.lastUses.lastUses.get(versionIn(decl,nsc),null);
								if(!nlu||nlu.forwardTo||nlu.kind!=Kind.lazySplit||!nlu.isLastSplitSibling()||!nlu.splitFrom.canForget(false))
									return Forgettability.none;
							}
						}
					}
				}
				return r;
			case synthesizedForget:
				return Forgettability.none; // TODO
			case implicitDup:
				return Forgettability.consumable;
			case constUse:
				if(dep.isTop) return Forgettability.none;
				if(constConsume&&constConsume.canForget(true))
					return Forgettability.consumable;
				if(canAddForget(parent)){
					import ast.semantic_:typeForDecl;
					if(auto ft=cast(ProductTy)typeForDecl(decl)){
						if(ft.captureAnnotation==CaptureAnnotation.spent){
							return Forgettability.consumable;
						}
					}
					return Forgettability.forgettable;
				}
				return Forgettability.none;
			case consumption:
				return Forgettability.none;
			case capture:
				return Forgettability.none; // TODO
		}
	}
	bool canRedefine(){
		if(forwardTo) return forwardTo.canRedefine();
		final switch(kind)with(Kind){
			case definition,constPinned:
				return false;
			case lazySplitSink:
				return false;
			case lazySplit:
				return canForget(true);
			case lazyMerge:
				return canForget(true);
			case implicitDup:
				return canForget(true);
			case constUse:
				return canForget(true);
			case synthesizedForget,consumption:
				return false; // (not handled by `forget`)
			case capture:
				return false; // TODO?
		}
	}

	bool betterUnforgettableError(Scope sc){
		if(forwardTo) return forwardTo.betterUnforgettableError(sc);
		final switch(kind)with(Kind){
			case definition,constPinned:
				return false;
			case lazySplitSink:
				return false;
			case lazySplit:
				return false; // TODO
			case lazyMerge:
				return false; // TODO
			case implicitDup:
				return false; // TODO
			case constUse:
				return false;
			case synthesizedForget,consumption:
				assert(0,text(this," ",sc.getFunction()));
			case capture:
				return false;
		}
	}

	void forget(bool forceConsumed,ReturnExp earlyReturn=null,bool enclosing=false){
		bool isForget=false;
		if(forwardTo){
			forwardTo.forget(forceConsumed,earlyReturn,enclosing);
			while(forwardTo.forwardTo) forwardTo=forwardTo.forwardTo;
			assert(isConsumption(),text(this," ",forwardTo," ",forwardTo.splitFrom," ",isConsumption()));
			if(scope_.lastUses.lastUses.get(decl,null) is this)
				scope_.lastUses.lastUses[decl]=forwardTo;
			return;
		}
		//imported!"util.io".writeln("FORGETTING: ",this," ",canForget(forceConsumed)," ",use?text(use.loc):"?");
		//imported!"util.io".writeln("FORGETTING: ",use);
		final switch(kind)with(Kind){
			case definition:
				goto case constUse;
			case constPinned:
				assert(0);
			case lazySplitSink:
				assert(0); // always forwarded
			case lazySplit:
				assert(!!splitFrom);
				if(forceConsumed||isLastSplitSibling()||earlyReturn&&dep.isTop&&!forgettableAtSplit(earlyReturn,enclosing)||atLoopEntry()){
					if(splitFrom.canForget(forceConsumed,earlyReturn,!!earlyReturn)){
						if(earlyReturn&&dep.isTop) // (forgotten before the split because of the early return)
							splitFrom.decl.forgottenBeforeEarlyReturn=earlyReturn;
						splitFrom.forget(forceConsumed,earlyReturn,!!earlyReturn);
						if(scope_.rnsymtab.get(decl.getId,null) is decl){
							scope_.symtabRemove(decl);
							scope_.pushDependencies(decl,false);
						}
						markConsumed(use,false);
						if(forceConsumed||earlyReturn) removeFromUnusedSiblings(); // (forgotten before the split)
						return;
					}
				}
				if(dep.isTop&&forgettableAtSplit(earlyReturn,enclosing)){ // (forgotten at the split, before the branch consumes what it depends on)
					dep=depAtSplit.dup;
					scope_.lastUses.noteCancelCandidate(decl);
				}
				assert(!dep.isTop);
				assert(!forceConsumed);
				//imported!"util.io".writeln("FORGETTING ON ENTRY: ",decl," ",splitFrom," ",splitFrom.canForget(forceConsumed));
				auto before=decl;
				auto forgotten=scope_.forgetOnEntry(decl);
				if(earlyReturn&&enclosing&&before.forgottenBeforeEarlyReturn is earlyReturn){ // (a nested branch returns where it cannot forget it: forgotten on entry of this branch instead of before its split, so a later use in this branch is explained as for a version forgotten before the conditional)
					before.forgottenBeforeEarlyReturn=null;
					forgotten.forgottenBeforeEarlyReturn=earlyReturn;
					explanationUse=new Identifier(forgotten.getId);
					explanationUse.loc=forgotten.loc;
					explanationUse.meaning=forgotten;
				}
				if(isBranch(scope_)){
					atSplit=true;
					(cast(NestedScope)scope_).forgottenAtSplit~=q(decl,this);
				}
				isForget=true;
				break;
			case lazyMerge:
				useFromMergedScopes();
				consume(false);
				foreach(i,nsc;nestedScopes){
					auto cdecl=versionIn(decl,nestedScopes[i]);
					//imported!"util.io".writeln("MERGED FROM: ",nsc.lastUses.lastUses.get(cdecl,null)," ",decl.mergedFrom," ",nsc.lastUses.lastUses," ",nsc.lastUses.lastUses.get(decl,null));
					assert(nsc.lastUses.canForget(cdecl,false,false));
					auto declBefore=decl;
					if(!use){
						if(auto lu=nsc.lastUses.get(cdecl,true))
							use=lu.use;
					}
					nsc.lastUses.forget(cdecl,false);
					//imported!"util.io".writeln("AFTER FORGET: ",declBefore," ",decl," ",declBefore is decl," ",decl.splitInto);
					if(nsc.mergedVars.any!(d=>d.mergedInto is decl))
						nsc.mergedVars=nsc.mergedVars.filter!(d=>d.mergedInto !is decl).array; // TODO: make more efficient
				}
				//imported!"util.io".writeln("AFTER LMERGE: ",scope_.rnsymtab);
				return;
			case synthesizedForget:
				assert(0);
			case implicitDup:
				assert(use.implicitDup);
				assert(!use.constLookup);
				cancelImplicitDup();
				//assert(!scope_.isConst(decl));
				return;
			case constUse:
				assert(!dep.isTop);
				if(constConsume&&constConsume.canForget(true)){
					constConsume.forget(true);
					markConsumed(use,false);
					return;
				}
				assert(canAddForget(parent));
				use=addForget(parent,decl,scope_);
				assert(!!use);
				scope_.declProps.history(decl).accesses~=use; // TODO: this is out of order, ok?
				isForget=true;
				break;
			case consumption:
				assert(0);
			case capture:
				assert(0); // TODO
				break;
		}
		consume(isForget);
	}
	bool canCancelImplicitDup(){
		if(forwardTo) return forwardTo.canCancelImplicitDup();
		if(splitFrom) return false;
		final switch(kind)with(Kind){
			case definition,lazySplitSink,lazySplit:
				return false;
			case lazyMerge:
				return canCancelImplicitDupMerge(decl,nestedScopes);
			case synthesizedForget:
				return false;
			case implicitDup,constPinned:
				return use&&use.implicitDup;
			case constUse:
				if(constConsume&&constConsume.canCancelImplicitDup())
					return true;
				if(prevImplicitDup||isConstLocal(decl))
					return canForget(false);
				return false;
			case consumption:
				return false;
			case capture:
				return false; // TODO
		}
		return true;
	}
	Identifier explanationUse;
	private void useFromMergedScopes(){
		if(use||explanationUse) return;
		foreach(nsc;nestedScopes){
			if(auto lu=nsc.lastUses.get(versionIn(decl,nsc),true)){
				if(lu.use){
					explanationUse=lu.use;
					return;
				}
			}
		}
	}
	bool cancelImplicitDup(){
		//imported!"util.io".writeln("CANCELING: ",use.loc," ",dep);
		if(forwardTo) return forwardTo.cancelImplicitDup();
		if(splitFrom) return false;
		final switch(kind)with(Kind){
			case definition,lazySplitSink,lazySplit:
				return assert(0);
			case lazyMerge:
				bool ok=true;
				useFromMergedScopes();
				ok&=consume(false);
				foreach(i,nsc;nestedScopes){
					auto cdecl=versionIn(decl,nestedScopes[i]);
					//imported!"util.io".writeln("MERGED FROM: ",nsc.lastUses.lastUses.get(cdecl,null)," ",decl.mergedFrom," ",nsc.lastUses.lastUses," ",nsc.lastUses.lastUses.get(decl,null));
					if(!use){
						if(auto lu=nsc.lastUses.get(cdecl,true))
							use=lu.use;
					}
					if(nsc.lastUses.canCancelImplicitDup(cdecl)){
						nsc.lastUses.cancelImplicitDup(cdecl);
						if(nsc.mergedVars.any!(d=>d.mergedInto is decl))
							nsc.mergedVars=nsc.mergedVars.filter!(d=>d.mergedInto !is decl).array; // TODO: make more efficient
					}else if(nsc.lastUses.canForget(cdecl,false,false)){
						nsc.lastUses.forget(cdecl,false);
						//imported!"util.io".writeln("AFTER FORGET: ",declBefore," ",decl," ",declBefore is decl," ",decl.splitInto);
						if(nsc.mergedVars.any!(d=>d.mergedInto is decl))
							nsc.mergedVars=nsc.mergedVars.filter!(d=>d.mergedInto !is decl).array; // TODO: make more efficient
					}else{
						ok=false;
						nsc.error(format("variable `%s` is not consumed",decl.getName),decl.loc);
						// TODO: needs a note indicating the end of scope
					}
				}
				return ok;
			case synthesizedForget:
				assert(0);
			case implicitDup,constPinned:
				if(!(use&&use.implicitDup)) return false;
				use.implicitDup=false;
				auto ok=scope_.checkImplicitDupCancel(use);
				if(!ok){ // (used afterwards, already reported)
					use.implicitDup=true;
					return false;
				}
				//imported!"util.io".writeln("CONSUMING: ",this," ",use.loc," ",constBlock," ",dep);
				scope_.noteImplicitDupCancelled(use,dep);
				ok&=consume(false);
				if(isBranchSplit()) updateDependenciesOnConsumption(); // (as for a consumption recorded in this branch)
				return ok;
			case constUse:
				if(constConsume&&constConsume.canCancelImplicitDup()){
					constConsume.cancelImplicitDup();
					markConsumed(use,false);
					return true;
				}
				if((prevImplicitDup||isConstLocal(decl))&&canForget(false)){
					forget(false);
					return true;
				}
				return false;
			case consumption:
				assert(0);
			case capture:
				assert(0); // TODO
		}
	}

	void replaceDecl(Declaration splitFrom,Declaration splitInto){
		//imported!"util.io".writeln("REPLACING: ",this," ",splitFrom," ",splitInto);
		if(forwardTo) forwardTo.replaceDecl(splitFrom,splitInto);
		if(decl is splitFrom) decl=splitInto;
		if(splitFrom in dep.dependencies) dep.replace(splitFrom,splitInto);
		if(splitFrom in depAtSplit.dependencies) depAtSplit.replace(splitFrom,splitInto);
	}
}

struct LastUses{
	LastUses* parent;
	MapX!(Declaration,LastUse) lastUses;
	MapX!(Declaration,LastUse[]) retired;
	SetX!Declaration cancelCandidates; // (the declarations whose last uses `LastUse.recordCancelable` considers: those that depend on something known, unless it does not need them, see `pruneCancelCandidates`)
	SetX!Declaration prunedCandidates;
	MapX!(Declaration,Declaration[]) prunedByVersion; // (by the versions they are split from, see `includeCancelCandidate`)
	size_t numCancelCandidates; // (after the last pruning)
	LastUse lastLastUse;
	size_t numAdded=0;
	bool discarded=false;

	LastUse nestingPoint;
	void prepareNesting(Scope parent)do{
		foreach(k,d;parent.rnsymtab){
			if(cast(DeadDecl)d) continue;
			lazySplitSink(d,parent);
		}
		nestingPoint=lastLastUse;
	}
	void nest(NestedScope r)in{
		with(r.lastUses){
			assert(!parent);
			assert(!lastUses.length);
			assert(!lastLastUse);
		}
	}do{
		//imported!"util.io".writeln("NESTING IN: ",lastUses);
		//imported!"util.io".writeln("NESTING IN: ",r.parent.dependencies," ",r.dependencies);
		r.lastUses.parent=&this;
		if(nestingPoint) nestingPoint.nestedAfter~=r;
		foreach(k,d;r.parent.rnsymtab){
			if(cast(DeadDecl)d) continue;
			if(d.sstate!=SemState.completed) continue;
			auto lu=lastUses.get(d,null);
			if(!lu) continue; // TODO: ok?
			while(lu.forwardTo) lu=lu.forwardTo;
			if(lu.kind==LastUse.Kind.consumption) continue;
			//imported!"util.io".writeln("SPLITTING: ",d," ",d.mergedFrom," ",d.splitInto);
			r.lastUses.lazySplit(d,r);
		}
	}
	private void retire(LastUse lastUse){
		if(!LastUse.inBranch(lastUse.scope_)) return; // (only the checks of the branch order read the history, see `checkBranchOrder`)
		retired[lastUse.decl]~=lastUse;
	}
	private void add(LastUse lastUse,Dependency* atSplit=null)in{
		assert(!!lastUse.scope_);
		with(LastUse.Kind){
			assert(lastUse.kind!=constUse||lastUse.parent);
		}
		if(lastUse.use&&lastUse.kind!=LastUse.Kind.capture){
			//assert(lastUse.use.scope_ is lastUse.scope_);
			assert(!lastUse.use.meaning||lastUse.use.meaning is lastUse.decl);
		}else{
			with(LastUse.Kind){
				assert(lastUse.kind.among(definition,lazySplitSink,lazySplit,lazyMerge,capture,constPinned,synthesizedForget));
			}
		}
		assert(!lastUse.prev&&!lastUse.next);
	}do{
		//imported!"util.io".writeln("ADDING LU: ",lastUse);
		lastUse.time=lastUse.consumedAt=tick();
		lastUse.dep=atSplit?atSplit.dup:lastUse.scope_.getDependency(lastUse.scope_.trackingDecl(lastUse.decl)).dup;
		lastUse.atSplit=!!atSplit;
		if(lastUse.dep.isTop){
			// TODO: make sure classical variables have dependency ∅ instead?
			import ast.semantic_:typeForDecl;
			auto type=typeForDecl(lastUse.decl);
			if(type&&type.isClassical) lastUse.dep=Dependency(false);
		}
		assert(lastUse.kind!=LastUse.kind.synthesizedForget||!lastUse.dep.isTop||lastUse.decl.isSemError());
		if(lastUse.kind==LastUse.Kind.synthesizedForget)
			lastUse.scope_.noteDependencyResolved(lastUse.dep);
		if(auto read=lastUse.scope_.isConst(lastUse.decl)){
			//imported!"util.io".writeln("ADDING CONST BLOCK: ",lastUse," ",read," ",read.loc);
			if(auto prop=lastUse.scope_.declProps.tryGet(lastUse.decl)){
				//imported!"util.io".writeln(read," ",prop.constBlock," ",lastUse.dep);
				assert(!lastUse.constBlock,text(lastUse," ",lastUse.constBlock));
				lastUse.constBlock=prop.constBlock;
				if(lastUse.constBlock.length&&lastUse.constBlock.back is lastUse.use)
					lastUse.constBlock.popBack(); // TODO: ok?
			}
		}
		if(auto prevLastUse=lastUses.get(lastUse.decl,null)){
			//imported!"util.io".writeln("PREVIOUS: ",prevLastUse);
			bool keep=lastUse.kind==LastUse.Kind.lazySplitSink;
			auto prev=prevLastUse; // (the last use that a `lazySplitSink` stands for)
			while(prev.forwardTo) prev=prev.forwardTo;
			if(lastUse.kind==LastUse.Kind.constUse&&prev.kind==LastUse.kind.lazyMerge){
				//imported!"util.io".writeln("ATTACHING CONSTCONSUME: ",lastUse);
				lastUse.constConsume=prev;
				keep=true;
			}
			if(prev.prevImplicitDup){
				lastUse.prevImplicitDup=prev.prevImplicitDup;
			}
			if(prev.kind==LastUse.Kind.constPinned){
				if(prev.use&&prev.use.implicitDup){
					lastUse.prevImplicitDup=prev;
					keep=true;
				}
			}
			if(lastUse.kind==LastUse.Kind.synthesizedForget&&prev.splitFrom&&prev.kind==LastUse.Kind.lazySplit&&LastUse.isBranch(lastUse.scope_)){
				lastUse.atSplit=true;
				(cast(NestedScope)lastUse.scope_).forgottenAtSplit~=q(lastUse.decl,lastUse);
			}
			if(prevLastUse.splitFrom){
				//imported!"util.io".writeln("PINNING SPLITS: ",lastUse," ",prevLastUse);
				if(lastUse.kind!=LastUse.Kind.lazySplitSink)
					prevLastUse.pin();
				lastUse.splitSource=prevLastUse;
				keep=true;
			}else if(prevLastUse.splitSource){
				assert(!!prevLastUse.splitSource.splitFrom);
				lastUse.splitSource=prevLastUse.splitSource;
			}
			if(!keep){
				if(prevLastUse.forwardTo){
					assert(prevLastUse.forwardTo !is lastLastUse);
					prevLastUse.forwardTo.remove();
				}
				if(prevLastUse.constConsume){
					assert(prevLastUse.constConsume !is lastLastUse);
					prevLastUse.constConsume.remove();
				}
				if(prevLastUse.splitSource){
					assert(prevLastUse.splitSource !is lastLastUse);
					prevLastUse.splitSource.remove();
				}
				if(lastLastUse is prevLastUse)
					lastLastUse=prevLastUse.prev;
				prevLastUse.remove();
			}
			lastUses.remove(lastUse.decl);
			retire(prevLastUse); // TODO: needed?
		}
		lastUse.index=numAdded++;
		lastUses[lastUse.decl]=lastUse;
		noteCancelCandidate(lastUse.decl);
		if(lastLastUse) lastLastUse.append(lastUse);
		lastLastUse=lastUse;
		if(lastUse.isConsumption()||lastUse.use&&lastUse.use.implicitDup) lastUse.recordCancelable();
		if(lastUse.isConsumption()){
			lastUse.noteBranchEvent();
			if(lastUse.splitSource&&lastUse.splitSource.splitFrom)
				lastUse.splitSource.splitFrom.markConsumed(lastUse.use,false,true,lastUse.consumedComponent,false,lastUse.scope_);
			lastUse.updateDependenciesOnConsumption();
		}
	}
	size_t clock=0;
	size_t tick(){ // (the analysis of a function adds the last uses of its scopes in program order)
		auto root=&this;
		while(root.parent) root=root.parent;
		return root.clock++;
	}
	void definition(Declaration decl,Expression defExp)in{
		assert(!!decl.scope_);
	}do{
		if(decl.isSemError()&&decl.scope_.rnsymtab.get(decl.getId,null) !is decl) return; // (not declared)
		Identifier use=null;
		add(new LastUse(LastUse.Kind.definition,decl.scope_,decl,use,defExp));
	}
	void lazySplitSink(Declaration decl,Scope sc)in{
		assert(decl.scope_&&sc);
	}do{
		auto lu=new LastUse(LastUse.Kind.lazySplitSink,sc,decl,null,null);
		lu.forwardTo=sc.lastUses.lastUses.get(decl,null);
		while(lu.forwardTo&&lu.forwardTo.kind==LastUse.Kind.lazySplitSink&&lu.forwardTo.forwardTo) // (an earlier sink stands for the same last use, e.g., where the variable is not used between two conditionals; a pinned one stays, see `removeFromUnusedSiblings`)
			lu.forwardTo=lu.forwardTo.forwardTo;
		add(lu);
	}
	void lazySplit(Declaration decl,NestedScope sc)in{
		assert(decl.scope_&&sc);
		assert(sc.isNestedIn(decl.scope_));
	}do{
		auto lu=new LastUse(LastUse.Kind.lazySplit,sc,decl,null,null);
		auto splitFrom=lu.getSplitFrom();
		//assert(splitFrom.kind==LastUse.Kind.lazySplitSink,text(splitFrom)); // TODO (fails in nested scopes in lowerings e.g. && and ||)
		add(lu);
		lu.depAtSplit=lu.dep.dup;
		if(splitFrom){
			auto p=splitFrom;
			while(p.forwardTo) p=p.forwardTo;
			if(p.prevImplicitDup) lu.prevImplicitDup=p.prevImplicitDup;
			else if(p.kind.among(LastUse.Kind.implicitDup,LastUse.Kind.constPinned)&&p.use&&p.use.implicitDup) lu.prevImplicitDup=p;
		}
		//imported!"util.io".writeln("SPLITTED: ",lu.getSplitFrom()," ",lu);
	}
	void lazyMerge(Declaration decl,Scope sc,NestedScope[] nestedScopes)in{
		assert(sc&&nestedScopes.length);
	}do{
		auto lu=new LastUse(LastUse.Kind.lazyMerge,sc,decl,null,null,nestedScopes);
		add(lu);
		if(!lu.prevImplicitDup){
			foreach(nsc;nestedScopes){
				if(!LastUse.mergesSameValue(decl,nsc)) continue;
				auto nlu=nsc.lastUses.lastUses.get(LastUse.versionIn(decl,nsc),null);
				while(nlu&&nlu.forwardTo) nlu=nlu.forwardTo;
				if(!nlu) continue;
				if(nlu.prevImplicitDup){
					lu.prevImplicitDup=nlu.prevImplicitDup;
					break;
				}
				if(nlu.kind.among(LastUse.Kind.implicitDup,LastUse.Kind.constPinned)&&nlu.use&&nlu.use.implicitDup){
					lu.prevImplicitDup=nlu;
					break;
				}
			}
		}
	}
	void synthesizedForget(Declaration decl,Identifier use,Scope sc,Expression parent,Dependency* atSplit=null)in{
		if(use){
			assert(use.byRef);
			assert(!use.constLookup);
			assert(use.meaning is decl);
			assert(use.scope_ is sc);
		}
	}do{
		//imported!"util.io".writeln("SYNTHESIZEDFORGET: ",use?text(use.loc):"<?>");
		add(new LastUse(LastUse.Kind.synthesizedForget,sc,decl,use,parent),atSplit);
	}
	bool dependencyAtSplit(Declaration decl,Scope sc,ref Dependency result,ref LastUse split){ // (of a version that is not used after its split: the dependency there, after the forgets since then; `split`: its last use in the branch)
		if(!splitDependency(decl,result,split)) return false;
		Scope.substituteConsumed(result,sc.consumedDepLog);
		return !result.isTop;
	}
	private bool splitDependency(Declaration decl,ref Dependency result,ref LastUse split){ // (in terms of the versions here)
		static bool isLoop(NestedScope nsc){ return nsc.getSiblingScopes().any!(s=>cast(BlockScope)s&&((cast(BlockScope)s).isLoopBody||(cast(BlockScope)s).isLoopEntry)); }
		auto lu=lastUses.get(decl,null);
		if(!lu) return false;
		while(lu.forwardTo) lu=lu.forwardTo;
		if(lu.kind==LastUse.Kind.lazyMerge){ // (continues the version of the only branch that reaches the merge, e.g., after the other one returns)
			if(lu.nestedScopes.length!=1||!LastUse.isBranch(lu.nestedScopes[0])) return false;
			auto nsc=lu.nestedScopes[0];
			if(nsc.getSiblingScopes().any!(s=>s !is nsc&&!(cast(BlockScope)s&&(cast(BlockScope)s).returns))) return false; // (the HQIR merges the versions after a branch that aborts, after the splits)
			auto cdecl=LastUse.versionIn(decl,nsc);
			if(cdecl is decl||!nsc.lastUses.splitDependency(cdecl,result,split)) return false;
			foreach(d;result.dependencies.dup){
				if(d.scope_ !is nsc) continue;
				if(!d.mergedInto) return false; // (consumed in the branch)
				result.replace(d,d.mergedInto);
			}
			return true;
		}
		if(!lu.splitFrom||lu.kind!=LastUse.Kind.lazySplit) return false;
		auto nsc=cast(NestedScope)lu.scope_;
		if(!nsc) return false;
		if(LastUse.isBranch(nsc)){
			if(lu.depAtSplit.isTop) return false;
			split=lu;
			result=lu.depAtSplit.dup;
			return true;
		}
		if(!lu.dep.isTop||nsc.getSiblingScopes().length!=1||isLoop(nsc)) return false; // (a block that does not split the version, e.g., the continuation of a `return` under quantum control)
		if(!nsc.parent.lastUses.splitDependency(lu.splitFrom.decl,result,split)) return false;
		Scope.substituteConsumed(result,nsc.parent.consumedDepLog);
		if(result.isTop) return false;
		foreach(d;result.dependencies.dup){
			auto s=nsc.getSplit(d);
			if(s !is d) result.replace(d,s);
		}
		return true;
	}
	void implicitDup(Identifier use)in{
		assert(!!use);
		assert(use.implicitDup);
		assert(!use.constLookup);
		assert(!!use.meaning);
		assert(!!use.scope_);
	}do{
		add(new LastUse(LastUse.Kind.implicitDup,use.scope_,use.meaning,use,null));
		use.scope_.noteImplicitDup(use);
		//imported!"util.io".writeln("IMPLICIT DUP: ",use," ",use.loc," ",lastUses);
	}
	void constUse(Identifier use,ref Expression parent,bool isStatement,bool inType)in{
		assert(use&&use.meaning);
		assert(use.constLookup||use.implicitDup);
		assert(!!use.scope_,text(use.loc," ",parent));
		assert(!!parent&&(parent.isSemError()||parent.isSemCompleted()),text(parent));
	}do{
		//imported!"util.io".writeln("CONST USE: ",use.loc," ",parent," ",use.meaning);
		void finish(Expression e){
			if(parent.isSemError()) e.setSemError();
			else e.setSemCompleted();
		}
		LetExp getLet(){
			if(auto le=cast(LetExp) parent) if(canAddForget(le)) return le; // (not a `let` with a block, e.g., in a `const` position, see `generalLetExpSemantic`)
			import ast.type:unit;
			import ast.semantic_:freshName;
			auto name=new Identifier(freshName());
			auto var=new VarDecl(name);
			var.loc=parent.loc;
			var.scope_=use.scope_;
			var.vtype=parent.type;
			finish(var);
			auto makeId(){
				auto id=name.copy();
				id.loc=parent.loc;
				id.scope_=use.scope_;
				id.byRef=true;
				id.constLookup=false;
				id.meaning=var;
				id.type=parent.type;
				finish(id);
				return id;
			}
			auto def=new DefineExp(makeId,parent);
			def.loc=parent.loc;
			def.type=unit;
			finish(def);
			auto s=new CompoundExp([def]);
			s.loc=def.loc;
			s.type=unit;
			finish(s);
			auto le=new LetExp(s,makeId);
			le.loc=parent.loc;
			le.type=parent.type;
			le.constLookup=parent.constLookup; // (it takes the place of `parent`, which can be a `const` result, see below)
			finish(le);
			return le;
		}
		auto depOk=!use.scope_.getDependency(use.scope_.trackingDecl(use.meaning)).isTop;
		if(!inType&&depOk){
			if(isStatement){
				auto ce=cast(CompoundExp)parent;
				if(!ce||!canAddForget(ce)){
					import ast.semantic_:definitelyReturns;
					if(!definitelyReturns(parent)){
						auto s=new CompoundExp([parent]);
						s.loc=parent.loc;
						s.type=unit;
						finish(s);
						if(parent.isSemError()) s.setSemError();
						else s.setSemCompleted();
						parent=s;
					}
				}
			}else if((!parent.constLookup||parent.type&&parent.type.isClassical())&&!cast(Identifier)parent) // (a classical value does not borrow from the variable)
				parent=getLet();
		}
		//imported!"util.io".writeln("MADE: ",parent);
		add(new LastUse(LastUse.Kind.constUse,use.scope_,use.meaning,use,parent));
	}
	void consumption(Declaration decl,Identifier use,Scope sc,IndexExp consumedComponent=null)in{
		assert(decl in lastUses||decl.isSemError(),text(decl," ",lastUses," ",cast(void*)decl," ",lastUses.keys.filter!(d=>d.getName is decl.getName).map!(d=>cast(void*)d)));
		assert(!!sc);
		if(use){
			assert(!use.meaning||use.meaning is decl,text(use," ",decl," ",use.meaning));
			assert(!use.constLookup);
			assert(!use.implicitDup);
			//assert(use.scope_ is sc);
		}
	}do{
		//imported!"util.io".writeln("CONSUMPTION: ",decl," ",use);
		auto lu=new LastUse(LastUse.Kind.consumption,sc,decl,use,null);
		lu.consumedComponent=consumedComponent;
		add(lu);
	}
	void capture(Declaration decl,Identifier use,Scope sc,Declaration parent){
		add(new LastUse(LastUse.Kind.capture,sc,decl,use,parent));
	}

	// copy another scope's final state, translating declarations and scopes
	// (used to give independently scoped instantiation twins their own state)
	void remapFrom(ref LastUses src,Declaration delegate(Declaration) mapDecl,Scope delegate(Scope) mapScope){
		MapSX!(LastUse,LastUse) nmap;
		LastUse remap(LastUse lu){
			if(!lu) return null;
			if(auto p = nmap.getPtr(lu)) return *p;
			auto ndecl=lu.decl?mapDecl(lu.decl):null;
			if(lu.decl&&!ndecl) return null;
			auto r=lu.dup;
			nmap[lu]=r;
			r.decl=ndecl;
			r.scope_=lu.scope_?mapScope(lu.scope_):null;
			r.forwardTo=remap(lu.forwardTo);
			r.constConsume=remap(lu.constConsume);
			r.prevImplicitDup=remap(lu.prevImplicitDup);
			r.splitFrom=remap(lu.splitFrom);
			r.splitSource=remap(lu.splitSource);
			r.nestedScopes=null;
			foreach(nsc;lu.nestedScopes)
				if(auto nnsc=cast(NestedScope)mapScope(nsc)) r.nestedScopes~=nnsc;
			r.prev=remap(lu.prev);
			r.next=remap(lu.next);
			return r;
		}
		foreach(d,lu;src.lastUses)
			if(auto nd=mapDecl(d)) if(auto r=remap(lu)) lastUses[nd]=r;
		foreach(d,_;lastUses) noteCancelCandidate(d);
		foreach(d,lus;src.retired)
			if(auto nd=mapDecl(d)) foreach(lu;lus) if(auto r=remap(lu)) retired[nd]~=r;
		lastLastUse=remap(src.lastLastUse);
		numAdded=src.numAdded;
		clock=src.clock;
	}

	LastUse get(Declaration decl,bool forceHere){
		if(auto lu=lastUses.get(decl,null))
			return lu;
		if(forceHere||!parent) return null;
		return parent.get(decl,false);
	}

	bool canForget(Declaration decl,bool forceHere,bool forceConsumed,ReturnExp earlyReturn=null){
		return getForgettability(decl,forceHere,forceConsumed,earlyReturn)>=(forceConsumed?LastUse.Forgettability.consumable:LastUse.Forgettability.forgettable);
	}
	private LastUse.Forgettability getForgettability(Declaration decl,bool forceHere,bool forceConsumed,ReturnExp earlyReturn=null){
		auto lastUse=lastUses.get(decl,null);
		if(!lastUse&&!forceHere&&parent)
			return parent.getForgettability(decl,false,forceConsumed,earlyReturn);
		return lastUse?lastUse.getForgettability(forceConsumed,earlyReturn):LastUse.Forgettability.none;
	}
	bool canRedefine(Declaration decl){
		//imported!"util.io".writeln("CAN REDEFINE: ",decl," ",lastUses," ",lastUses.get(decl,null));
		if(auto lastUse=lastUses.get(decl,null))
			return lastUse.canRedefine();
		return parent&&parent.canRedefine(decl);
	}
	bool betterUnforgettableError(Declaration decl,Scope sc){
		auto lastUse=lastUses.get(decl,null);
		if(!lastUse&&parent)
			return parent.betterUnforgettableError(decl,sc);
		return lastUse&&lastUse.betterUnforgettableError(sc);
	}
	void forget(Declaration decl,bool forceConsumed,ReturnExp earlyReturn=null)in{
		assert(canForget(decl,false,forceConsumed,earlyReturn));
	}do{
		auto lastUse=lastUses.get(decl,null);
		if(!lastUse){
			assert(!!parent);
			return parent.forget(decl,forceConsumed,earlyReturn);
		}
		lastUse.forget(forceConsumed,earlyReturn);
	}
	void pin(Declaration decl,bool forceHere){
		if(!decl.scope_) return;
		if(auto lastUse=lastUses.get(decl,null)) lastUse.pin();
		else if(!forceHere&&parent) parent.pin(decl,false);
		//decl.scope_.lastUses.lastUses.remove(decl);
		foreach(split;decl.splitInto){
			assert(!!split.scope_);
			split.scope_.lastUses.pin(split,true);
		}
	}
	bool canCancelImplicitDup(Declaration decl){
		if(auto lastUse=lastUses.get(decl,null))
			return lastUse.canCancelImplicitDup();
		return false;
	}
	bool cancelImplicitDup(Declaration decl){
		if(auto lastUse=lastUses.get(decl,null))
			return lastUse.cancelImplicitDup();
		return false;
	}

	void replaceDecl(Declaration splitFrom,Declaration splitInto)in{
		// assert(splitInto !in lastUses); // TODO
	}do{
		//imported!"util.io".writeln("REPLACING: ",splitFrom," ",splitInto);
		if(splitFrom in lastUses){
			lastUses[splitInto]=lastUses[splitFrom];
			lastUses.remove(splitFrom);
			cancelCandidates.remove(splitFrom);
			prunedCandidates.remove(splitFrom);
			noteCancelCandidate(splitInto);
		}
		foreach(lu;lastUses) lu.replaceDecl(splitFrom,splitInto);
		if(splitFrom in retired){
			retired[splitInto]=retired[splitFrom];
			retired.remove(splitFrom);
		}
		foreach(lus;retired)
			foreach(lu;lus)
				lu.replaceDecl(splitFrom,splitInto);
	}

	void merge(bool isLoop,Scope parent,scope NestedScope[] nestedScopes){
		//imported!"util.io".writeln("MERGING: ",parent," ",nestedScopes);
		foreach(k,decl;parent.rnsymtab){
			if(cast(DeadDecl)decl) continue;
			//imported!"util.io".writeln("CHECKING MERGE: ",decl," ",decl.mergedFrom," ",decl.splitInto," ",lastUses," ",nestedScopes," ",LastUse.isNontrivialMerge(decl,nestedScopes)," ",LastUse.canForgetMerge(decl,nestedScopes,true,false));
			if(!LastUse.isNontrivialMerge(decl,nestedScopes)) continue;
			if(isLoop) pin(decl,true);
			//if(!LastUse.canForgetMerge(decl,nestedScopes,true,false)) continue;
			lazyMerge(decl,parent,nestedScopes.dup);
			if(isLoop) pin(decl,true);
			//imported!"util.io".writeln("MERGED: ",decl," ",decl.mergedFrom," ",nestedScopes.map!(sc=>cast(void*)sc));
		}
	}

	// TODO: snapshotting is a bit hacky
	void substituteDependency(Declaration decl,Dependency dep){
		foreach(_,lu;lastUses){
			lu.dep.replace(decl,dep);
			lu.depAtSplit.replace(decl,dep);
		}
		foreach(_,lus;retired)
			foreach(lu;lus)
				if(lu){
					lu.dep.replace(decl,dep);
					lu.depAtSplit.replace(decl,dep);
				}
	}
	MapX!(Declaration,LastUse) getSnapshot(Scope sc){
		MapX!(Declaration,LastUse) nlastUses;
		foreach(k,decl;sc.rnsymtab){
			if(auto lu=get(decl,false))
				nlastUses[decl]=lu;
			//if(restoreable) imported!"util.io".writeln("RECORDED: ",nlastUses);
		}
		return nlastUses;
	}
	void restoreSnapshot(MapX!(Declaration,LastUse) snapshot,size_t numAdded,Scope sc){
		for(auto lu=lastLastUse;lu&&lu.index>=numAdded;lu=lu.prev){
			lu.use=null; // (from the discarded analysis, cannot be consumed)
			lu.discarded=true; // (does not constrain later consumptions either)
		}
		foreach(_,d;sc.rnsymtab){
			if(auto nlu=lastUses.get(d,null)){
				if(nlu.isConsumption()||nlu!is snapshot.get(d,null)){
					nlu.kind=LastUse.Kind.constPinned;
				}
			}
			noteCancelCandidate(d); // (e.g., consumed after the snapshot, see `pruneCancelCandidates`)
		}
	}
	private static LastUse target(LastUse lu){
		while(lu&&lu.forwardTo) lu=lu.forwardTo;
		return lu;
	}
	private void noteCancelCandidate(Declaration decl){ // (when its last use changes: a dependency that is unknown or empty stays that way)
		prunedCandidates.remove(decl);
		auto lu=target(lastUses.get(decl,null));
		if(lu&&!lu.dep.isTop&&lu.dep.dependencies.length) includeCancelCandidate(decl);
		else cancelCandidates.remove(decl);
	}
	private void includeCancelCandidate(Declaration decl){ // (and the pruned candidates that one of its dependencies is a version of, see `pruneCancelCandidates`)
		cancelCandidates.insert(decl);
		void include(Declaration d){
			if(d !in prunedCandidates) return;
			prunedCandidates.remove(d);
			if(d in lastUses) includeCancelCandidate(d);
		}
		foreach(x;target(lastUses.get(decl,null)).dep.dependencies){
			foreach(y;x.splitSequence) include(y);
			foreach(d;prunedByVersion.get(x,null)) include(d);
		}
	}
	Declaration[] orderedCancelCandidates(){ // (in the order of `lastUses`)
		if(cancelCandidates.length>2*numCancelCandidates+16){
			pruneCancelCandidates();
			numCancelCandidates=cancelCandidates.length;
		}
		Q!(size_t,Declaration)[] r;
		foreach(d;cancelCandidates){
			size_t pos;
			if(lastUses.tryGetPosition(d,pos)) r~=q(pos,d);
		}
		sort!"a[0]<b[0]"(r);
		return r.map!(x=>x[1]).array;
	}
	private void pruneCancelCandidates(){ // (one that consumes its variable only matters while the dependency of another candidate mentions a version of it: it is included again when one does)
		for(bool changed=true;changed;){
			SetX!Declaration mentioned,versions; // (`versions`: also those that they were split from)
			foreach(d;cancelCandidates){
				auto lu=target(lastUses.get(d,null));
				if(!lu||lu.dep.isTop) continue;
				foreach(x;lu.dep.dependencies){
					mentioned.insert(x);
					foreach(y;x.splitSequence) versions.insert(y);
				}
			}
			Declaration[] stale,gone;
			foreach(d;cancelCandidates){
				auto lu=target(lastUses.get(d,null));
				if(!lu||lu.dep.isTop||!lu.dep.dependencies.length) stale~=d; // (see `noteCancelCandidate`)
				else if((lu.isConsumption()||lastUses.get(d,null).kind.among(LastUse.Kind.consumption,LastUse.Kind.synthesizedForget))&&d !in versions&&!d.splitSequence.any!(y=>y in mentioned)) gone~=d; // (also one whose last use is forwarded to the one before a nested scope consumed it, e.g., a sink of a variable that a branch consumes)
			}
			foreach(d;stale) cancelCandidates.remove(d);
			foreach(d;gone){
				cancelCandidates.remove(d);
				prunedCandidates.insert(d);
				foreach(y;d.splitSequence) prunedByVersion[y]~=d;
			}
			changed=gone.length!=0;
		}
	}
}

void queueBranchOrder(Scope sc,BlockScope[] branches){ // (the forgets in the branches are only known after the analysis of the function)
	if(!branches.all!(b=>LastUse.isBranch(b))) return;
	if(auto fd=sc.getFunction()) if(fd.fscope_){
		fd.fscope_.pendingBranchOrders~=q(sc,branches);
		return;
	}
	checkBranchOrder(sc,branches);
}
void checkBranchOrder(Scope sc,BlockScope[] branches){ // (the code generator splits a variable that a branch consumes after the uncomputations in the branches that recompute values from its version from before the split, and before the consumptions of its versions: without such an order, those cannot be forgotten, see `interleaveBranches` in hqir.d)
	auto fixed=!branches.all!(b=>LastUse.interleavable(b)); // (the code generator does not interleave the branches: it splits the variables before them)
	static struct Event{
		size_t branch,time,var;
		LastUse lu; // (the consumption or the uncomputation)
		bool need,active; // (the uncomputation needs the version from before the split if it is active, e.g., once its definition reads the version of the branch before the split)
		size_t def=size_t.max; // (the event of that definition)
	}
	MapX!(Declaration,size_t) varIndex;
	Event[] events; // (first the splits of the variables)
	foreach(b;branches) foreach(c;b.outerConsumptions){
		if(c[1].discarded||c[1].kind!=LastUse.Kind.consumption||!c[1].dep.isTop||c[0].scope_ !is sc||c[0] in varIndex) continue; // (with a known dependency, the uncomputations recompute it from that one instead, as before)
		varIndex[c[0]]=events.length;
		events~=Event(size_t.max,0,events.length);
	}
	if(!events.length) return;
	auto numVars=events.length;
	static bool reported(Declaration d){ // (an error about a version of the variable, e.g., for the forgets of a version in both branches of a nested conditional)
		while(d.splitFrom) d=d.splitFrom;
		SetX!Declaration visited;
		bool visit(Declaration x){
			if(!x||x in visited) return false;
			visited.insert(x);
			return x.isSemError()||x.splitInto.any!(y=>visit(y))||visit(x.mergedInto);
		}
		return visit(d);
	}
	static size_t definitionTime(Declaration d,Scope b){ // (of the first version in `b` that it is derived or updated from)
		size_t r=size_t.max;
		SetX!Declaration visited;
		void visit(Declaration x){
			if(x in visited||!x.scope_||!x.scope_.isNestedIn(b)) return;
			visited.insert(x);
			auto lus=x.scope_.lastUses.retired.get(x,null);
			if(auto lu=lus.length?lus[0]:x.scope_.lastUses.lastUses.get(x,null)) r=min(r,lu.time);
			foreach(y;x.derivedSequence) visit(y);
			foreach(c;x.definitionSources.consumes) visit(c[0]);
		}
		visit(d);
		return r==size_t.max?0:r;
	}
	foreach(i,b;branches){
		foreach(c;b.outerConsumptions){
			if(c[1].discarded||c[1].kind!=LastUse.Kind.consumption) continue;
			auto p=varIndex.get(c[0],size_t.max);
			if(p!=size_t.max) events~=Event(i,c[1].consumedAt,p,c[1]);
		}
		foreach(lu;b.uncomputations){
			if(lu.discarded||lu.atSplit&&lu.scope_ is b||lu.kind!=LastUse.Kind.synthesizedForget||!lu.decl||lu.decl.isSemError()||lu.dep.isTop) continue;
			foreach(d;lu.dep.dependencies){
				auto outer=LastUse.outerVersion(d,b,true);
				auto p=outer?varIndex.get(outer,size_t.max):size_t.max;
				if(p==size_t.max) continue;
				if(lu.decl.derivedSequence.all!(x=>x.scope_&&x.scope_.isNestedIn(b))&&LastUse.readsSplitAtDefinition(b,outer,lu.decl,lu.dep,true)){ // (it reads the version of the branch)
					events~=Event(i,lu.time,p,lu,true,false,events.length+1);
					events~=Event(i,definitionTime(lu.decl,b),p);
				}else events~=Event(i,lu.time,p,lu,true,true);
			}
		}
	}
	auto edges=new size_t[][](events.length);
	bool ordered(size_t k,size_t l){ // (in program order, unless they are in different branches of a nested conditional, which never both run, also where the code after the nested conditional continues one of them, see `continuedBranches`: the code generator orders them where it interleaves the nested conditional, see `interleaveBranches` in hqir.d and `ItePartialReturn`)
		if(!events[k].lu||!events[l].lu) return true;
		foreach(x;events[k].lu.noted) foreach(y;events[l].lu.noted)
			if(x !is y&&LastUse.interleavable(x)&&LastUse.interleavable(y)&&x.getSiblingScopes().canFind(y)) return false;
		return true;
	}
	foreach(i;0..branches.length){
		auto inBranch=iota(numVars,events.length).filter!(k=>events[k].branch==i).array;
		inBranch.sort!((k,l)=>events[k].time<events[l].time||events[k].time==events[l].time&&k<l);
		foreach(j;0..inBranch.length) foreach(l;j+1..inBranch.length) if(ordered(inBranch[j],inBranch[l])) edges[inBranch[j]]~=inBranch[l];
	}
	foreach(k;numVars..events.length){
		auto e=events[k];
		if(e.lu&&!e.need) edges[e.var]~=k;
		if(e.need&&e.active) edges[k]~=e.var;
	}
	if(fixed) foreach(p;0..numVars) foreach(k;numVars..events.length) edges[p]~=k;
	foreach(b;branches) foreach(f;b.dependenciesAtSplit()){ // (a version without uses in a branch is uncomputed at its split, before the splits of the variables it depends on)
		auto outer=LastUse.outerVersion(f[0],b);
		auto p=outer?varIndex.get(outer,size_t.max):size_t.max;
		if(p==size_t.max||f[1].isTop) continue;
		foreach(d;f[1].dependencies){
			auto od=LastUse.outerVersion(d,b);
			auto q=od?varIndex.get(od,size_t.max):size_t.max;
			if(q!=size_t.max&&q!=p) edges[p]~=q;
		}
	}
	bool reaches(size_t from,size_t to){
		auto visited=new bool[](events.length);
		bool visit(size_t k){
			if(k==to) return true;
			if(visited[k]) return false;
			visited[k]=true;
			foreach(l;edges[k]) if(visit(l)) return true;
			return false;
		}
		return visit(from);
	}
	for(bool changed=true;changed;){ // (a definition before the split reads the version from before it)
		changed=false;
		foreach(k;numVars..events.length){
			if(!events[k].need||events[k].active||!reaches(events[k].def,events[k].var)) continue;
			events[k].active=true;
			edges[k]~=events[k].var;
			changed=true;
		}
	}
	bool interleave=false;
	foreach(k;numVars..events.length){
		auto e=events[k];
		if(!e.need||!e.active||reported(e.lu.decl)) continue;
		if(!reaches(e.var,k)){
			interleave=true;
			continue;
		}
		LastUse at=null; // (a consumption on the cycle, preferably of the same variable, which it cannot precede)
		bool atSame=false;
		foreach(l;numVars..events.length){
			auto c=events[l];
			if(!c.lu||c.need||!reaches(k,l)||!reaches(l,k)) continue;
			bool same=c.var==e.var;
			if(!at||same>atSame||same==atSame&&c.lu.consumedAt<at.consumedAt) at=c.lu, atSame=same;
		}
		e.lu.dep=Dependency(true);
		if(at){
			e.lu.dep.lostVar=at.decl;
			e.lu.dep.lostAt=at.use;
		}
		e.lu.reportUnforgettable();
	}
	if(interleave) foreach(b;branches) b.interleave=true;
}
SetX!Id eagerMergeOrder(Scope sc,NestedScope[] branches,Q!(Id,Declaration[])[] candidates){ // (the candidates for eager merges whose merges can come after the last changes of their versions in the branches and before their first reads, which read the merged versions instead, see `genEagerMerges` in hqir.d, in an order with the splits of `checkBranchOrder` for the events known so far)
	enum none=size_t.max;
	static struct Event{ size_t branch,time,node; }
	Event[] events;
	size_t[][] edges;
	size_t newNode(){ edges~=null; return edges.length-1; }
	void edge(size_t a,size_t b){ if(a!=none&&b!=none&&a!=b) edges[a]~=b; }
	MapX!(Declaration,size_t) varNode;
	foreach(i,b;branches){
		auto bs=cast(BlockScope)b;
		if(!bs) continue;
		foreach(c;bs.outerConsumptions){
			if(c[1].discarded||c[1].kind!=LastUse.Kind.consumption||!c[1].dep.isTop||c[0].scope_ !is sc) continue;
			auto p=varNode.get(c[0],none);
			if(p==none) varNode[c[0]]=p=newNode();
			auto k=newNode();
			events~=Event(i,c[1].consumedAt,k);
			edge(p,k);
		}
	}
	foreach(i,b;branches){
		auto bs=cast(BlockScope)b;
		if(!bs) continue;
		foreach(lu;bs.uncomputations){
			if(lu.discarded||lu.atSplit&&lu.scope_ is b||lu.kind!=LastUse.Kind.synthesizedForget||!lu.decl||lu.decl.isSemError()||lu.dep.isTop) continue;
			foreach(d;lu.dep.dependencies){
				auto outer=LastUse.outerVersion(d,b,true);
				auto p=outer?varNode.get(outer,none):none;
				if(p==none) continue;
				auto k=newNode();
				events~=Event(i,lu.time,k);
				edge(k,p);
			}
		}
		foreach(f;bs.dependenciesAtSplit()){
			auto outer=LastUse.outerVersion(f[0],b);
			auto p=outer?varNode.get(outer,none):none;
			if(p==none||f[1].isTop) continue;
			foreach(d;f[1].dependencies){
				auto od=LastUse.outerVersion(d,b);
				edge(p,od?varNode.get(od,none):none);
			}
		}
	}
	static size_t definitionTime(Declaration d){
		if(!d.scope_) return 0;
		auto lus=d.scope_.lastUses.retired.get(d,null);
		if(auto lu=lus.length?lus[0]:d.scope_.lastUses.lastUses.get(d,null)) return lu.time;
		return 0;
	}
	static size_t firstRead(Declaration d,Scope b,size_t after){ // (in `b` and its nested scopes)
		size_t r=none;
		void visit(Scope s){
			void consider(LastUse lu){
				if(lu&&!lu.discarded&&lu.time>after&&lu.kind.among(LastUse.Kind.constUse,LastUse.Kind.implicitDup,LastUse.Kind.constPinned,LastUse.Kind.capture)) r=min(r,lu.time);
			}
			foreach(lu;s.lastUses.retired.get(d,null)) consider(lu);
			consider(s.lastUses.lastUses.get(d,null));
			foreach(group;s.mergedNestedScopes) foreach(n;group) visit(n);
		}
		visit(b);
		return r;
	}
	size_t[] merges;
	foreach(c;candidates){
		auto m=newNode();
		merges~=m;
		foreach(i,d;c[1]){
			auto def=definitionTime(d),read=firstRead(d,branches[i],def);
			auto k=newNode();
			events~=Event(i,def,k);
			edge(k,m);
			if(read==none) continue;
			auto l=newNode();
			events~=Event(i,read,l);
			edge(m,l);
		}
	}
	foreach(i;0..branches.length){ // (program order)
		auto inBranch=events.filter!(e=>e.branch==i).array;
		inBranch.sort!((a,b)=>a.time<b.time||a.time==b.time&&a.node<b.node);
		foreach(j;1..inBranch.length) edge(inBranch[j-1].node,inBranch[j].node);
	}
	auto active=new bool[](candidates.length);
	active[]=true;
	bool onCycle(size_t m){
		auto visited=new bool[](edges.length);
		bool visit(size_t k){
			foreach(l;edges[k]){
				if(l==m) return true;
				if(visited[l]) continue;
				visited[l]=true;
				auto j=merges.countUntil(l);
				if(j>=0&&!active[j]) continue;
				if(visit(l)) return true;
			}
			return false;
		}
		return visit(m);
	}
	for(bool changed=true;changed;){
		changed=false;
		foreach(j,m;merges){
			if(!active[j]||!onCycle(m)) continue;
			active[j]=false;
			changed=true;
			break;
		}
	}
	SetX!Id r;
	foreach(j,c;candidates) if(active[j]) r.insert(c[0]);
	return r;
}
