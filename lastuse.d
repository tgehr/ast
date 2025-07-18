// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.lastuse;
import astopt;

import std.range, std.algorithm, std.conv;
import ast.expression,ast.declaration,ast.scope_;


final class LastUse{
	private this(LastUse.Kind kind,Scope scope_,Declaration decl,Identifier use,Expression parent){
		this.kind=kind;
		this.scope_=scope_;
		this.decl=decl;
		this.use=use;
		this.parent=parent;
	}
	private this(LastUse.Kind kind,Scope scope_,Declaration decl,Identifier use,Expression parent,Dependency dep){
		this(kind,scope_,decl,use,parent);
		this.dep=dep;
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
		lazySplit,
		lazyMerge,
		implicitForget,
		implicitDup,
		constUse,
		consumption,
	}
	Kind kind; // TODO: sum type?
	Scope scope_;
	Declaration decl=null;
	Identifier use=null;
	Expression parent=null;
	static if(language==silq)
		ast.scope_.Dependency dep;
	LastUse prev=null,next=null;
	int numPendingSplits=0;

	LastUse getSplitFrom()in{
		assert(kind==Kind.lazySplit);
	}do{
		auto nsc=cast(NestedScope)scope_;
		assert(!!nsc);
		auto ndecl=nsc.parent.getSplit(decl);
		while(ndecl.splitFrom&&ndecl.splitFrom.scope_.isNestedIn(nsc.parent))
			ndecl=ndecl.splitFrom;
		auto plu=nsc.parent.lastUses.lastUses.get(ndecl,null);
		assert(!!plu,text(ndecl," ",nsc.parent.lastUses.lastUses));
		return plu;
	}

	bool pin(){
		if(kind==Kind.consumption) return false;
		if(kind==Kind.lazySplit){
			auto plu=getSplitFrom();
			assert(plu&&plu.numPendingSplits>0);
			plu.pin();
			--plu.numPendingSplits;
		}
		kind=Kind.constPinned;
		return true;
	}

	void remove()in{
		assert(kind==Kind.constPinned||kind==Kind.consumption);
	}do{
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

	void consume(){
		if(kind==Kind.implicitForget) return;
		if(kind==Kind.consumption) return;
		if(kind==Kind.lazySplit){
			auto lu=getSplitFrom();
			assert(lu&&lu.numPendingSplits>0);
			--lu.numPendingSplits;
		}
		/+imported!"util.io".writeln("CONSUMING: ",this);
		scope(exit) imported!"util.io".writeln("CONSUMED: ",this);+/
		scope(exit) kind=Kind.consumption;
		assert(!use||use.meaning is decl);
		auto csc=cast(NestedScope)scope_;
		assert(csc&&csc.isNestedIn(decl.scope_));
		for(;csc;csc=cast(NestedScope)csc.parent){
			if(auto d=decl.getId in csc.rnsymtab){
				assert(*d is decl,text(*d," ",decl));
				//imported!"util.io".writeln("FOUND: ",decl," ",csc.getFunction()," ",csc.rnsymtab);
			}else{
				csc.reinsert(decl);
				//imported!"util.io".writeln("INSERTED: ",decl," ",csc.getFunction()," ",csc.rnsymtab);
			}
			if(csc is decl.scope_) break;
		}
		Declaration result=decl;
		result=scope_.consume(result,use);
		assert(scope_.getSplit(decl) is result);
		assert(!use||use.meaning is result);
		result.scope_.unsplit(result);
		void removeCopies(Scope sc){
			foreach(nested;sc.activeNestedScopes){
				if(nested.forgottenVarsOnEntry.canFind(result)){
					nested.forgottenVarsOnEntry=nested.forgottenVarsOnEntry.filter!(d=>d!is result).array; // TODO: make more efficient
				}
				if(nested.rnsymtab.get(result.getId,null) is result){
					nested.symtabRemove(result);
					if(use&&!use.constLookup&&!use.implicitDup)
						nested.recordConsumption(result,use);
				}
				removeCopies(nested);
			}
		}
		removeCopies(scope_);
		// TODO: perform necessary updates
	}

	bool canForget(bool forceConsumed){
		if(use&&!scope_.canSplit(use.meaning)) return false;
		final switch(kind)with(Kind){
			case definition,constPinned:
				goto case constUse;
			case lazySplit:
				auto plu=getSplitFrom();
				assert(!!plu&&plu.numPendingSplits>0);
				return (plu.numPendingSplits==1||forceConsumed)&&plu.canForget(forceConsumed)||!forceConsumed&&!dep.isTop&&scope_.canSplit(decl);
			case lazyMerge:
				return false; // TODO
			case implicitForget:
				return false; // TODO
			case implicitDup:
				return true;
			case constUse:
				return false; // TODO
			case consumption:
				assert(decl.isSemError(),text(this));
				return true;
		}
	}
	bool canRedefine(){
		final switch(kind)with(Kind){
			case definition,constPinned:
				return false;
			case lazySplit:
				return canForget(true);
			case lazyMerge:
				return false; // TODO
			case implicitDup:
				return canForget(true);
			case constUse:
				return false;
			case implicitForget,consumption:
				assert(0);
		}
	}

	bool betterUnforgettableError(Scope sc){
		final switch(kind)with(Kind){
			case definition,constPinned:
				return false;
			case lazySplit:
				return false; // TODO
			case lazyMerge:
				return false; // TODO
			case implicitDup:
				return false; // TODO
			case constUse:
				return false;
			case implicitForget,consumption:
				assert(0);
		}
	}

	void forget(bool forceConsumed){
		final switch(kind)with(Kind){
			case definition,constPinned:
				goto case constUse;
			case lazySplit:
				auto lu=getSplitFrom();
				assert(lu&&lu.numPendingSplits>0);
				if((lu.numPendingSplits==1||forceConsumed)&&lu.canForget(forceConsumed)){
					//imported!"util.io".writeln("FORGETTING NOT ON ENTRY: ",decl," ",lu);
					return lu.forget(forceConsumed);
				}
				assert(!dep.isTop);
				assert(!forceConsumed);
				//imported!"util.io".writeln("FORGETTING ON ENTRY: ",decl," ",lu," ",lu.canForget(forceConsumed));
				scope_.forgetOnEntry(decl);
				break;
			case lazyMerge:
				assert(0); // TODO
				break;
			case implicitForget:
				assert(0); // TODO
				break;
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
		}
		consume();
	}

	void replaceDecl(Declaration splitFrom,Declaration splitInto){
		if(decl is splitFrom) decl=splitInto;
	}

	void pushDependencies(Declaration decl,Scope sc){
		if(kind==Kind.implicitDup){
			//imported!"util.io".writeln("BEFORE PUSH: ",use.loc," ",decl," ",dep);
			if(dep.isTop) return; // might reenter during cancelImplicitDup
			sc.pushUp(dep,decl);
			//imported!"util.io".writeln("AFTER PUSH: ",use.loc," ",decl," ",dep);
			if(dep.isTop){
				assert(use&&use.meaning is this.decl);
				//imported!"util.io".writeln("BEFORE CANCEL: ",sc.rnsymtab," ",sc.lastUses.lastUses);
				if(sc.cancelImplicitDup(use)){
					assert(kind==LastUse.Kind.consumption);
				}else{
					// TODO
				}
			}
		}
	}
}

struct LastUses{
	LastUses* parent;
	LastUse[Declaration] lastUses;
	LastUse lastLastUse;
	void nest(NestedScope r)return in{
		with(r.lastUses){
			assert(!parent);
			assert(!lastUses.length);
			assert(!lastLastUse);
		}
	}do{
		//imported!"util.io".writeln("NESTING IN: ",r.lastUses);
		r.lastUses.parent=&this;
		foreach(d,ref lu;lastUses){
			if(lu.kind==LastUse.Kind.consumption) continue;
			r.lastUses.lazySplit(d,r);
		}
	}
	private void add(LastUse lastUse)in{
		assert(!!lastUse.scope_);
		with(LastUse.Kind){
			assert(!lastUse.kind.among(implicitForget,constUse)||lastUse.parent);
		}
		if(lastUse.use){
			assert(lastUse.use.scope_ is lastUse.scope_);
			assert(!!lastUse.use.meaning);
		}else{
			with(LastUse.Kind){
				assert(lastUse.kind.among(definition,lazySplit,lazyMerge));
			}
		}
		assert(!lastUse.prev&&!lastUse.next);
	}do{
		//imported!"util.io".writeln("ADDING LU: ",lastUse);
		if(auto prevLastUse=lastUses.get(lastUse.decl,null)){
			prevLastUse.remove();
			lastUses.remove(lastUse.decl);
		}
		lastUses[lastUse.decl]=lastUse;
		auto newLastLastUse=lastUses.get(lastUse.decl,null);
		if(lastLastUse) lastLastUse.append(newLastLastUse);
		lastLastUse=newLastLastUse;
	}
	void definition(Declaration decl,Expression defExp)in{
		assert(!!decl.scope_);
	}do{
		Identifier use=null;
		add(new LastUse(LastUse.Kind.definition,decl.scope_,decl,use,defExp));
	}
	void lazySplit(Declaration decl,NestedScope sc)in{
		assert(decl.scope_&&sc);
		assert(sc.isNestedIn(decl.scope_));
	}do{
		auto lu=new LastUse(LastUse.Kind.lazySplit,sc,decl,null,null);
		static if(language==silq) lu.dep=sc.getDependency(decl);
		++lu.getSplitFrom().numPendingSplits;
		add(lu);
	}
	void lazyMerge(Declaration decl,Scope sc)in{
		assert(!!sc);
		assert(decl.mergedFrom.length);
	}do{
		add(new LastUse(LastUse.Kind.lazyMerge,sc,decl,null,null));
	}
	void implicitForget(Identifier use,Expression forgetExp,Dependency forgetDep)in{
		assert(!!use);
		assert(use.byRef);
		assert(!use.constLookup);
		assert(!!use.meaning);
		assert(!!use.scope_);
	}do{
		add(new LastUse(LastUse.Kind.implicitForget,use.scope_,use.meaning,use,forgetExp,forgetDep));
	}
	void implicitDup(Identifier use)in{
		assert(!!use);
		assert(use.implicitDup);
		assert(!use.constLookup);
		assert(!!use.meaning);
		assert(!!use.scope_);
	}do{
		auto lu=new LastUse(LastUse.Kind.implicitDup,use.scope_,use.meaning,use,null);
		static if(language==silq) lu.dep=use.scope_.getDependency(use.meaning);
		add(lu);
	}
	void constUse(Identifier use,Expression parent)in{
		assert(!!use);
		assert(use.constLookup||use.implicitDup);
		assert(!!use.scope_);
	}do{
		add(new LastUse(LastUse.Kind.constUse,use.scope_,use.meaning,use,parent));
	}
	void consume(Declaration decl,Identifier use,Scope sc)in{
		assert(decl in lastUses);
		assert(!!sc);
		if(use){
			assert(use.meaning is decl);
			assert(!use.constLookup);
			assert(!use.implicitDup);
			assert(use.scope_ is sc);
		}
	}do{
		auto lastUse=lastUses.get(decl,null);
		assert(!!lastUse);
		add(new LastUse(LastUse.Kind.consumption,sc,decl,use,null));
	}

	bool canForget(Declaration decl,bool forceHere,bool forceConsumed){
		auto lastUse=lastUses.get(decl,null);
		if(!lastUse&&!forceHere&&parent)
			return parent.canForget(decl,false,forceConsumed);
		return lastUse&&lastUse.canForget(forceConsumed);
	}
	bool canRedefine(Declaration decl){
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
		auto lastUse=lastUses.get(decl,null);
		if(!lastUse&&!forceHere&&parent)
			parent.pin(decl,false);
		if(lastUse&&!lastUse.pin()){
			lastUse.remove();
			lastUses.remove(decl);
			lastUse=null;
		}
		//decl.scope_.lastUses.lastUses.remove(decl);
		foreach(split;decl.splitInto){
			assert(!!split.scope_);
			split.scope_.lastUses.pin(split,true);
		}
	}

	void replaceDecl(Declaration splitFrom,Declaration splitInto)in{
		// assert(splitInto !in lastUses); // TODO
	}do{
		if(splitFrom !in lastUses) return;
		lastUses[splitInto]=lastUses[splitFrom];
		lastUses.remove(splitFrom);
		lastUses[splitInto].replaceDecl(splitFrom,splitInto);
	}

	void pushDependencies(Declaration decl,Scope sc){
		foreach(d,ref lu;lastUses){
			lu.pushDependencies(decl,sc);
		}
	}
}
