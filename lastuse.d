// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.lastuse;
import astopt;

import std.range, std.algorithm, std.conv;
import ast.expression,ast.declaration,ast.scope_;


struct LastUse{
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
	Declaration decl=null;
	Identifier use=null;
	Expression parent=null;
	static if(language==silq)
		ast.scope_.Dependency forgetDep;
	LastUse* prev=null,next=null;

	void commit(){
		switch(kind){
			case LastUse.Kind.lazySplit:
				decl.splitFrom.scope_.consume(decl,null);
				kind=LastUse.Kind.constPinned;
				break;
			case LastUse.Kind.lazyMerge:
				foreach(d;decl.mergedFrom)
					d.scope_.consume(decl,null);
				kind=LastUse.Kind.constPinned;
				break;
			default:
				break;
		}
	}

	void pin(){
		commit();
		if(kind==Kind.implicitDup) kind=Kind.constPinned;
	}

	void remove(){
		commit();
		if(prev) prev.next=next;
		if(next) next.prev=prev;
		prev=next=null;
	}
	void prepend(LastUse* prev)in{
		assert(!this.prev);
		assert(!prev.next);
	}do{
		this.prev=prev;
		prev.next=&this;
		// TODO: perform necessary updates
	}
	void append(LastUse* next)in{
		assert(!this.next);
		assert(!next.prev);
	}do{
		this.next=next;
		next.prev=&this;
		// TODO: perform necessary updates
	}

	void consume(){
		commit();
		if(kind==Kind.implicitForget) return;
		if(kind==Kind.consumption) return;
		kind=Kind.consumption;
		assert(use.meaning is decl);
		auto csc=cast(NestedScope)use.scope_;
		assert(csc&&csc.isNestedIn(decl.scope_));
		for(;csc;csc=cast(NestedScope)csc.parent){
			if(auto d=decl.getId in csc.rnsymtab){
				assert(*d is decl);
				//imported!"util.io".writeln("FOUND: ",decl," ",csc.getFunction()," ",csc.rnsymtab);
			}else{
				csc.symtabInsert(decl); // TODO: use insertCapture?
				//imported!"util.io".writeln("INSERTED: ",decl," ",csc.getFunction()," ",csc.rnsymtab);
			}
			if(csc is decl.scope_) break;
		}
		auto result=use.scope_.consume(decl,use);
		assert(use.scope_.getSplit(decl) is result);
		assert(use.meaning is result);
		void removeSplits(Declaration decl){
			foreach(split;decl.splitInto){
				split.scope_.consume(split,null); // TODO: need to make sure we don't remove anything that has an use
				removeSplits(split);
			}
		}
		removeSplits(result);
		void removeCopies(Scope sc){
			foreach(nested;sc.activeNestedScopes){
				if(nested.rnsymtab.get(result.getId,null) is result)
					nested.symtabRemove(result);
				removeCopies(nested);
			}
		}
		if(result.scope_)
			removeCopies(result.scope_);
		// TODO: perform necessary updates
	}

	bool canForget(bool forceHere){
		if(forceHere){
			if(kind==Kind.consumption) return false; // TODO: can we get rid of this?
			if(kind==Kind.implicitDup) return false; // TODO
		}
		if(!use.scope_.canSplit(use.meaning)) return false;
		final switch(kind)with(Kind){
			case definition,constPinned:
				goto case constUse;
			case lazySplit:
				return false; // TODO
			case lazyMerge:
				return false; // TODO
			case implicitForget:
				return false; // TODO
			case implicitDup:
				if(forceHere) return false;
				return true;
			case constUse:
				return false; // TODO
			case consumption:
				assert(0);
		}
	}
	bool canRedefine(){
		final switch(kind)with(Kind){
			case definition,constPinned:
				return false;
			case lazySplit,lazyMerge:
				return false; // TODO
			case implicitDup:
				return canForget(false);
			case constUse:
				return canForget(true);
			case implicitForget,consumption:
				assert(0);
		}
	}

	bool betterUnforgettableError(Scope sc){
		final switch(kind)with(Kind){
			case definition,constPinned:
				return false;
			case lazySplit,lazyMerge:
				return false; // TODO
			case implicitDup:
				return false; // TODO
			case constUse:
				return false;
			case implicitForget,consumption:
				assert(0);
		}
	}

	void forget(){
		final switch(kind)with(Kind){
			case definition,constPinned:
				goto case constUse;
			case lazySplit:
				assert(0); // TODO
				break;
			case lazyMerge:
				assert(0); // TODO
				break;
			case implicitForget:
				assert(0); // TODO
				break;
			case implicitDup:
				use.implicitDup=false;
				assert(!use.constLookup);
				//assert(!use.scope_.isConst(decl));
				break;
			case constUse:
				assert(0); // TODO
				break;
			case consumption:
				assert(0);
		}
		consume();
	}
}

struct LastUses{
	LastUses* parent;
	LastUse[Declaration] lastUses;
	LastUse* lastLastUse;
	private void add(LastUse lastUse)in{
		assert(lastUse.kind!=LastUse.Kind.constUse||lastUse.parent);
		assert(lastUse.use.scope_);
		assert(lastUse.use.meaning);
		assert(!lastUse.prev&&!lastUse.next);
	}do{
		if(auto prevLastUse=lastUse.decl in lastUses){
			prevLastUse.remove();
			lastUses.remove(lastUse.decl);
		}
		lastUses[lastUse.decl]=lastUse;
		auto newLastLastUse=lastUse.decl in lastUses;
		if(lastLastUse) lastLastUse.append(newLastLastUse);
		lastLastUse=newLastLastUse;
	}
	void definition(Declaration decl,Expression defExp){
		Identifier use=null;
		add(LastUse(LastUse.kind.definition,decl,use,defExp));
	}
	void lazySplit(Declaration decl)in{
		assert(decl.splitFrom&&decl.splitFrom in lastUses);
	}do{
		add(LastUse(LastUse.kind.lazySplit,decl));
	}
	void lazyMerge(Declaration decl)in{
		assert(decl.mergedFrom.length);
	}do{
		add(LastUse(LastUse.kind.lazyMerge,decl));
	}
	void implicitForget(Identifier use,Expression forgetExp,Dependency forgetDep)in{
		assert(!!use);
		assert(use.byRef);
		assert(!use.constLookup);
		assert(!!use.meaning);
	}do{
		add(LastUse(LastUse.Kind.implicitForget,use.meaning,use,forgetExp,forgetDep));
	}
	void implicitDup(Identifier use,Expression parent)in{
		assert(!!use);
		assert(use.implicitDup);
		assert(!use.constLookup);
	}do{
		add(LastUse(LastUse.Kind.implicitDup,use.meaning,use,parent));
	}
	void constUse(Identifier use,Expression parent)in{
		assert(!!use);
		assert(use.constLookup||use.implicitDup);
	}do{
		add(LastUse(LastUse.Kind.constUse,use.meaning,use,parent));
	}
	void consume(Declaration decl,Identifier use)in{
		assert(decl in lastUses);
		if(use){
			assert(use.meaning is decl);
			assert(!use.constLookup);
			assert(!use.implicitDup);
		}
	}do{
		auto lastUse=decl in lastUses;
		assert(!!lastUse);
		add(LastUse(LastUse.Kind.consumption,decl,use));
	}

	bool canForget(Declaration decl,bool forceHere){
		auto lastUse=decl in lastUses;
		if(!lastUse&&!forceHere&&parent)
			return parent.canForget(decl,false);
		return lastUse&&lastUse.canForget(forceHere);
	}
	bool canRedefine(Declaration decl){
		auto lastUse=decl in lastUses;
		if(!lastUse&&parent) return parent.canRedefine(decl);
		return lastUse&&lastUse.canRedefine();
	}
	bool betterUnforgettableError(Declaration decl,Scope sc)in{
		assert(!canForget(decl,false));
	}do{
		auto lastUse=decl in lastUses;
		if(!lastUse&&parent)
			return parent.betterUnforgettableError(decl,sc);
		return lastUse&&lastUse.betterUnforgettableError(sc);
	}
	void forget(Declaration decl)in{
		assert(canForget(decl,false));
	}do{
		auto lastUse=decl in lastUses;
		if(!lastUse){
			assert(!!parent);
			return parent.forget(decl);
		}
		lastUse.forget();
	}
	void pin(Declaration decl,bool forceHere){
		if(!decl.scope_) return;
		auto lastUse=decl in lastUses;
		if(!lastUse&&!forceHere&&parent)
			parent.pin(decl,false);
		if(lastUse) lastUse.pin();
		//decl.scope_.lastUses.lastUses.remove(decl);
		foreach(split;decl.splitInto){
			assert(!!split.scope_);
			split.scope_.lastUses.pin(split,true);
		}
	}
}
