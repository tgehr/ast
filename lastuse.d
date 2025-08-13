// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.lastuse;
import astopt;

import std.range, std.algorithm, std.conv, std.format;
import ast.expression,ast.declaration,ast.scope_;


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
	enum Kind{
		definition,
		constPinned,
		lazySplitSource,
		lazySplit,
		lazyMerge,
		synthesizedForget,
		implicitDup,
		constUse,
		consumption,
		capture,
	}
	Kind kind; // TODO: sum type?
	Scope scope_;
	Declaration decl=null;
	Identifier use=null;
	Expression parent=null;
	static if(language==silq)
		auto dep=Dependency(true);
	LastUse forwardTo=null;
	LastUse splitFrom=null;
	LastUse splitSource=null;
	NestedScope[] nestedScopes;
	LastUse prev=null,next=null;

	bool isConsumption(){
		if(forwardTo) return forwardTo.isConsumption();
		return !!kind.among(Kind.consumption,Kind.synthesizedForget);
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

	static bool isNontrivialMerge(Declaration decl,scope NestedScope[] nestedScopes){
		return iota(nestedScopes.length).any!((i){
			auto nsc=nestedScopes[i];
			auto cdecl=decl;
			if(decl.mergedFrom.length==nestedScopes.length&&decl.mergedFrom[i].scope_ is nestedScopes[i])
				cdecl=decl.mergedFrom[i];
			if(decl !is cdecl) return true;
			auto nlu=nsc.lastUses.lastUses.get(cdecl,null);
			if(!nlu) return false;
			while(nlu.forwardTo) nlu=nlu.forwardTo;
			if(nlu.kind!=Kind.lazySplit) return true;
			return false;
		});
	}
	static Forgettability getMergeForgettability(Declaration decl,scope NestedScope[] nestedScopes,bool forceHere){
		//imported!"util.io".writeln("CAN FORGET MERGE: ",decl," ",cast(void*)decl.scope_," ",decl.mergedFrom," ",nestedScopes.map!(sc=>cast(void*)sc));
		return iota(nestedScopes.length).map!((i){
			auto nsc=nestedScopes[i];
			auto cdecl=decl;
			if(decl.mergedFrom.length==nestedScopes.length&&decl.mergedFrom[i].scope_ is nsc)
				cdecl=decl.mergedFrom[i];
			//imported!"util.io".writeln("CHECKING: ",decl," ",nsc.lastUses.getForgettability(cdecl,forceHere,false)," ",nsc.lastUses.getForgettability(decl,forceHere,false)," ",nsc.lastUses.lastUses.get(cdecl,null)," ",cdecl is decl);
			return nsc.lastUses.getForgettability(cdecl,forceHere,false);
		}).fold!((a,b){
			auto r=min(a,b);
			if(r==Forgettability.none) return r;
			if(a==Forgettability.consumable||b==Forgettability.consumable) return Forgettability.consumable;
			return r;
		})(Forgettability.max);
	}
	static bool canForgetMerge(Declaration decl,scope NestedScope[] nestedScopes,bool forceHere,bool forceConsumed){
		return getMergeForgettability(decl,nestedScopes,forceHere)>=(forceConsumed?Forgettability.consumable:Forgettability.forgettable);
	}

	void remove(){
		if(prev) prev.next=next;
		if(next) next.prev=prev;
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
	}

	void pinSplits(){ return pinImpl(true); }
	void pin(){ return pinImpl(false); }
	void pinImpl(bool includingSplits){
		if(forwardTo){
			forwardTo.pin();
			forwardTo=null;
		}
		if(splitFrom) splitFrom.pin();
		if(!includingSplits&&kind==Kind.lazySplit) return;
		if(isConsumption()) return;
		//imported!"util.io".writeln("PINNING: ",this);
		kind=Kind.constPinned;
		if(splitFrom) splitFrom.pinSplits();
	}

	private void markConsumed(bool isForget){
		if(isConsumption()) return;
		if(splitFrom) splitFrom.markConsumed(false);
		if(isForget){
			assert(!dep.isTop);
			kind=Kind.synthesizedForget;
		}else kind=Kind.consumption;
		updateDependenciesOnConsumption();
	}
	private void updateDependenciesOnConsumption(){
		//imported!"util.io".writeln("UPDATING DEPENDENCIES FROM: ",this);
		// TODO: perform necessary updates
		auto cdep=dep.dup;
		auto start=next;
		if(splitFrom){
			for(start=this;start&&start.prev&&start.prev.splitFrom;)
				start=start.prev; // TODO: this is a hack, would be better to insert lazy splits in dependency order
		}
		for(auto lu=start;lu;lu=lu.next){
			if(lu is this) continue;
			//imported!"util.io".writeln("VISITING: ",lu," ",decl," ",cdep);
			lu.dep.replace(decl,cdep);
			//imported!"util.io".writeln("REPLACED: ",lu," ",decl," ",cdep);
			if(lu.kind.among(Kind.consumption,Kind.synthesizedForget)){
				cdep.replace(lu.decl,lu.dep);
				if(lu.kind==Kind.synthesizedForget&&lu.dep.isTop){
					if(lu.use && lu.use.scope_){
						lu.scope_.error(format("cannot synthesize forget expression for '%s'",lu.use),lu.use.loc);
					}else if(lu.decl.scope_){
						auto d=lu.decl,sc=lu.decl.scope_;
						if(cast(Parameter)d) sc.error(format("%s '%s' is not consumed (perhaps return it or annotate it 'const')",d.kind,d.getName),d.loc);
						else sc.error(format("%s '%s' is not consumed (perhaps return it)",d.kind,d.getName),d.loc);
						if(cast(ReturnExp)lu.parent) sc.note("at function return",lu.parent.loc);
					}
					lu.decl.setSemForceError();
					if(lu.use) lu.use.setSemForceError();
					if(lu.parent) lu.parent.setSemForceError();
					// TODO: the error has to be propagated out further
				}
			}
		}
	}

	void consume(bool isForget){
		assert(!forwardTo);
		if(kind==Kind.synthesizedForget) return;
		if(kind==Kind.consumption) return;
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
					csc.replaceDecl(d,cdecl);
				}
			}else csc.reinsert(cdecl);
			if(csc is decl.scope_) break;
		}
		Declaration result=scope_.getSplit(decl);
		result=scope_.consume(result,use);
		assert(!!result);
		scope_.unsplit(result);
		assert(scope_.getSplit(decl) is result);
		assert(!use||use.meaning is result);
		void removeCopies(Scope sc){
			foreach(nested;sc.activeNestedScopes){ // TODO: need to consider nested scopes at correct time
				if(nested.forgottenVarsOnEntry.canFind(result)){
					nested.forgottenVarsOnEntry=nested.forgottenVarsOnEntry.filter!(d=>d!is result).array; // TODO: make more efficient
				}
				if(nested.rnsymtab.get(result.getId,null) is result){
					nested.symtabRemove(result);
					nested.pushDependencies(result,false);
					if(use&&!use.constLookup&&!use.implicitDup)
						nested.recordConsumption(result,use);
					if(auto lu=nested.lastUses.get(result,true))
						lu.markConsumed(isForget);
				}
				if(nested.forgottenVars.canFind(result)){
					nested.forgottenVars=nested.forgottenVars.filter!(d=>d!is result).array; // TODO: make more efficient
				}
				removeCopies(nested);
			}
		}
		removeCopies(scope_);
		markConsumed(isForget);
	}

	static enum Forgettability{
		none,
		forgettable,
		consumable,
	}

	bool canForget(bool forceConsumed){
		return getForgettability(forceConsumed)>=(forceConsumed?Forgettability.consumable:Forgettability.forgettable);
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
			if(!ssc.forgottenVarsOnEntry.canFind(ndecl)) return false;
		}
		return true;
	}

	Forgettability getForgettability(bool forceConsumed){
		if(forwardTo) return forwardTo.getForgettability(forceConsumed);
		//imported!"util.io".writeln("GETTING FORGETTABILITY: ",this);
		if(use&&!scope_.canSplit(use.meaning)) return Forgettability.none;
		final switch(kind)with(Kind){
			case definition,constPinned:
				goto case constUse;
			case lazySplitSource:
				return Forgettability.none;
			case lazySplit:
				assert(!!splitFrom);
				auto r=Forgettability.none;
				if(forceConsumed||isLastSplitSibling())
					r=max(r,splitFrom.getForgettability(forceConsumed));
				if(r==Forgettability.none&&!dep.isTop&&scope_.canSplit(decl))
					r=Forgettability.forgettable;
				//imported!"util.io".writeln("RESULT: ",r);
				return r;
			case lazyMerge:
				return getMergeForgettability(decl,nestedScopes,true);
			case synthesizedForget:
				return Forgettability.none; // TODO
			case implicitDup:
				return Forgettability.consumable;
			case constUse:
				return Forgettability.none; // TODO
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
			case lazySplitSource:
				return false;
			case lazySplit:
				return canForget(true);
			case lazyMerge:
				return canForget(true);
			case implicitDup:
				return canForget(true);
			case constUse:
				return false;
			case synthesizedForget,consumption:
				return true;
			case capture:
				return false; // TODO?
		}
	}

	bool betterUnforgettableError(Scope sc){
		if(forwardTo) return forwardTo.betterUnforgettableError(sc);
		final switch(kind)with(Kind){
			case definition,constPinned:
				return false;
			case lazySplitSource:
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

	void forget(bool forceConsumed){
		bool isForget=false;
		if(forwardTo){
			forwardTo.forget(forceConsumed);
			while(forwardTo.forwardTo) forwardTo=forwardTo.forwardTo;
			assert(isConsumption(),text(this," ",forwardTo," ",forwardTo.splitFrom," ",isConsumption()));
			if(scope_.lastUses.lastUses.get(decl,null) is this)
				scope_.lastUses.lastUses[decl]=forwardTo;
			return;
		}
		//imported!"util.io".writeln("FORGETTING: ",this," ",canForget(forceConsumed)," ",use?text(use.loc):"?");
		//imported!"util.io".writeln("FORGETTING: ",use);
		final switch(kind)with(Kind){
			case definition,constPinned:
				goto case constUse;
			case lazySplitSource:
				assert(0); // always forwarded
			case lazySplit:
				assert(!!splitFrom);
				if(forceConsumed||isLastSplitSibling()){
					if(splitFrom.canForget(forceConsumed)){
						splitFrom.forget(forceConsumed);
						if(scope_.rnsymtab.get(decl.getId,null) is decl){
							scope_.symtabRemove(decl);
							scope_.pushDependencies(decl,false);
						}
						markConsumed(false);
						return;
					}
				}
				assert(!dep.isTop);
				assert(!forceConsumed);
				//imported!"util.io".writeln("FORGETTING ON ENTRY: ",decl," ",splitFrom," ",splitFrom.canForget(forceConsumed));
				scope_.forgetOnEntry(decl);
				isForget=true;
				break;
			case lazyMerge:
				consume(false);
				foreach(i,nsc;nestedScopes){
					auto cdecl=decl;
					if(decl.mergedFrom.length==nestedScopes.length&&decl.mergedFrom[i].scope_ is nestedScopes[i])
						cdecl=decl.mergedFrom[i];
					else if(decl.splitInto.length==nestedScopes.length&&decl.splitInto[i].scope_ is nestedScopes[i])
						cdecl=decl.splitInto[i];
					//imported!"util.io".writeln("MERGED FROM: ",nsc.lastUses.lastUses.get(cdecl,null)," ",decl.mergedFrom," ",nsc.lastUses.lastUses," ",nsc.lastUses.lastUses.get(decl,null));
					assert(nsc.lastUses.canForget(cdecl,false,false));
					auto declBefore=decl;
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
				use.implicitDup=false;
				assert(!use.constLookup);
				//assert(!scope_.isConst(decl));
				break;
			case constUse:
				assert(0); // TODO
				break;
			case consumption:
				assert(0);
			case capture:
				assert(0); // TODO
				break;
		}
		consume(isForget);
	}

	void replaceDecl(Declaration splitFrom,Declaration splitInto){
		//imported!"util.io".writeln("REPLACING: ",this," ",splitFrom," ",splitInto);
		if(forwardTo) forwardTo.replaceDecl(splitFrom,splitInto);
		if(decl is splitFrom) decl=splitInto;
		if(splitFrom in dep.dependencies) dep.replace(splitFrom,splitInto);
	}
}

struct LastUses{
	LastUses* parent;
	LastUse[Declaration] lastUses;
	LastUse[][Declaration] retired;
	LastUse lastLastUse;

	void prepareNesting(Scope parent)do{
		foreach(k,d;parent.rnsymtab){
			if(cast(DeadDecl)d) continue;
			lazySplitSource(d,parent);
		}
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
		retired[lastUse.decl]~=lastUse;
	}
	private void add(LastUse lastUse)in{
		assert(!!lastUse.scope_);
		with(LastUse.Kind){
			assert(lastUse.kind!=constUse||lastUse.parent);
		}
		if(lastUse.use&&lastUse.kind!=LastUse.Kind.capture){
			//assert(lastUse.use.scope_ is lastUse.scope_);
			assert(!lastUse.use.meaning||lastUse.use.meaning is lastUse.decl);
		}else{
			with(LastUse.Kind){
				assert(lastUse.kind.among(definition,lazySplitSource,lazySplit,lazyMerge,capture,constPinned,synthesizedForget));
			}
		}
		assert(!lastUse.prev&&!lastUse.next);
	}do{
		static if(language==silq){
			lastUse.dep=lastUse.scope_.getDependency(lastUse.decl).dup;
			assert(lastUse.kind!=LastUse.kind.synthesizedForget||!lastUse.dep.isTop);
		}
		//imported!"util.io".writeln("ADDING LU: ",lastUse);
		if(auto prevLastUse=lastUses.get(lastUse.decl,null)){
			//imported!"util.io".writeln("PREVIOUS: ",prevLastUse);
			if(prevLastUse.splitFrom){
				//imported!"util.io".writeln("PINNING SPLITS: ",lastUse," ",prevLastUse);
				if(lastUse.kind!=LastUse.Kind.lazySplitSource)
					prevLastUse.pinSplits();
				lastUse.splitSource=prevLastUse;
			}else{
				if(lastUse.kind!=LastUse.Kind.lazySplitSource){
					if(prevLastUse.forwardTo)
						prevLastUse.forwardTo.remove();
					prevLastUse.remove();
				}
				if(prevLastUse.splitSource){
					assert(!!prevLastUse.splitSource.splitFrom);
					lastUse.splitSource=prevLastUse.splitSource;
				}
			}
			lastUses.remove(lastUse.decl);
			retire(prevLastUse); // TODO: needed?
		}
		lastUses[lastUse.decl]=lastUse;
		if(lastLastUse) lastLastUse.append(lastUse);
		lastLastUse=lastUse;
		if(lastUse.isConsumption()&&lastUse.splitSource){
			lastUse.splitSource.updateDependenciesOnConsumption();
		}
	}
	void definition(Declaration decl,Expression defExp)in{
		assert(!!decl.scope_);
	}do{
		Identifier use=null;
		add(new LastUse(LastUse.Kind.definition,decl.scope_,decl,use,defExp));
	}
	void lazySplitSource(Declaration decl,Scope sc)in{
		assert(decl.scope_&&sc);
	}do{
		auto lu=new LastUse(LastUse.Kind.lazySplitSource,sc,decl,null,null);
		lu.forwardTo=sc.lastUses.lastUses.get(decl,null);
		add(lu);
	}
	void lazySplit(Declaration decl,NestedScope sc)in{
		assert(decl.scope_&&sc);
		assert(sc.isNestedIn(decl.scope_));
	}do{
		auto lu=new LastUse(LastUse.Kind.lazySplit,sc,decl,null,null);
		auto splitFrom=lu.getSplitFrom();
		//assert(splitFrom.kind==LastUse.Kind.lazySplitSource,text(splitFrom)); // TODO (fails in nested scopes in lowerings e.g. && and ||)
		add(lu);
		//imported!"util.io".writeln("SPLITTED: ",lu.getSplitFrom()," ",lu);
	}
	void lazyMerge(Declaration decl,Scope sc,NestedScope[] nestedScopes)in{
		assert(sc&&nestedScopes.length);
	}do{
		add(new LastUse(LastUse.Kind.lazyMerge,sc,decl,null,null,nestedScopes));
	}
	void synthesizedForget(Declaration decl,Identifier use,Scope sc,Expression parent)in{
		if(use){
			assert(use.byRef);
			assert(!use.constLookup);
			assert(use.meaning is decl);
			assert(use.scope_ is sc);
		}
	}do{
		add(new LastUse(LastUse.Kind.synthesizedForget,sc,decl,use,parent));
	}
	void implicitDup(Identifier use)in{
		assert(!!use);
		assert(use.implicitDup);
		assert(!use.constLookup);
		assert(!!use.meaning);
		assert(!!use.scope_);
	}do{
		add(new LastUse(LastUse.Kind.implicitDup,use.scope_,use.meaning,use,null));
		//imported!"util.io".writeln("IMPLICIT DUP: ",use," ",use.loc," ",lastUses);
	}
	void constUse(Identifier use,Expression parent)in{
		assert(use&&use.meaning);
		assert(use.constLookup||use.implicitDup);
		assert(!!use.scope_,text(use.loc," ",parent));
	}do{
		//imported!"util.io".writeln("CONST USE: ",use.loc," ",parent);
		add(new LastUse(LastUse.Kind.constUse,use.scope_,use.meaning,use,parent));
	}
	void consumption(Declaration decl,Identifier use,Scope sc)in{
		assert(decl in lastUses||decl.isSemError(),text(decl," ",lastUses," ",cast(void*)decl," ",lastUses.keys.filter!(d=>d.getName is decl.getName).map!(d=>cast(void*)d)));
		assert(!!sc);
		if(use){
			assert(!use.meaning||use.meaning is decl,text(use," ",decl," ",use.meaning));
			assert(!use.constLookup);
			assert(!use.implicitDup);
			//assert(use.scope_ is sc);
		}
	}do{
		add(new LastUse(LastUse.Kind.consumption,sc,decl,use,null));
	}
	void capture(Declaration decl,Identifier use,Scope sc,Declaration parent){
		add(new LastUse(LastUse.Kind.capture,sc,decl,use,parent));
	}

	LastUse get(Declaration decl,bool forceHere){
		if(auto lu=lastUses.get(decl,null))
			return lu;
		if(forceHere||!parent) return null;
		return parent.get(decl,false);
	}

	bool canForget(Declaration decl,bool forceHere,bool forceConsumed){
		return getForgettability(decl,forceHere,forceConsumed)>=(forceConsumed?LastUse.Forgettability.consumable:LastUse.Forgettability.forgettable);
	}
	private LastUse.Forgettability getForgettability(Declaration decl,bool forceHere,bool forceConsumed){
		auto lastUse=lastUses.get(decl,null);
		if(!lastUse&&!forceHere&&parent)
			return parent.getForgettability(decl,false,forceConsumed);
		return lastUse?lastUse.getForgettability(forceConsumed):LastUse.Forgettability.none;
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
	void forget(Declaration decl,bool forceConsumed)in{
		assert(canForget(decl,false,forceConsumed));
	}do{
		auto lastUse=lastUses.get(decl,null);
		if(!lastUse){
			assert(!!parent);
			return parent.forget(decl,forceConsumed);
		}
		lastUse.forget(forceConsumed);
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

	void replaceDecl(Declaration splitFrom,Declaration splitInto)in{
		// assert(splitInto !in lastUses); // TODO
	}do{
		//imported!"util.io".writeln("REPLACING: ",splitFrom," ",splitInto);
		if(splitFrom in lastUses){
			lastUses[splitInto]=lastUses[splitFrom];
			lastUses.remove(splitFrom);
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
	LastUse[Declaration] getSnapshot(Scope sc){
		LastUse[Declaration] nlastUses;
		foreach(k,decl;sc.rnsymtab){
			if(auto lu=get(decl,false))
				nlastUses[decl]=lu;
			//if(restoreable) imported!"util.io".writeln("RECORDED: ",nlastUses);
		}
		return nlastUses;
	}
	void restoreSnapshot(LastUse[Declaration] snapshot,Scope sc){
		foreach(_,d;sc.rnsymtab){
			if(auto nlu=lastUses.get(d,null)){
				if(nlu.isConsumption()||nlu!is snapshot.get(d,null)){
					nlu.kind=LastUse.Kind.constPinned;
				}
			}
		}
	}
}
