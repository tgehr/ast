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
	Scope scope_;
	Declaration decl=null;
	Identifier use=null;
	Expression parent=null;
	static if(language==silq)
		ast.scope_.Dependency dep;
	LastUse* prev=null,next=null;
	int numPendingSplits=0;

	LastUse* getSplitFrom()in{
		assert(kind==Kind.lazySplit);
	}do{
		auto nsc=cast(NestedScope)scope_;
		assert(!!nsc);
		auto ndecl=nsc.parent.getSplit(decl);
		while(ndecl.splitFrom&&ndecl.splitFrom.scope_.isNestedIn(nsc.parent))
			ndecl=ndecl.splitFrom;
		auto plu=ndecl in nsc.parent.lastUses.lastUses;
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
		if(kind==Kind.implicitForget) return;
		if(kind==Kind.consumption) return;
		if(kind==Kind.lazySplit){
			auto lu=getSplitFrom();
			assert(lu&&lu.numPendingSplits>0);
			--lu.numPendingSplits;
		}
		scope(exit) kind=Kind.consumption;
		assert(!use||use.meaning is decl);
		auto csc=cast(NestedScope)scope_;
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
		Declaration result=decl;
		if(kind==Kind.lazySplit){
			scope_.symtabRemove(result);
		}else result=scope_.consume(result,use);
		assert(scope_.getSplit(decl) is result);
		assert(!use||use.meaning is result);
		result.scope_.unsplit(result);
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

	bool canForget(){
		if(use&&!scope_.canSplit(use.meaning)) return false;
		final switch(kind)with(Kind){
			case definition,constPinned:
				goto case constUse;
			case lazySplit:
				auto plu=getSplitFrom();
				assert(!!plu&&plu.numPendingSplits>0);
				return plu.numPendingSplits==1&&plu.canForget()||!dep.isTop&&scope_.canSplit(decl);
			case lazyMerge:
				return false; // TODO
			case implicitForget:
				return false; // TODO
			case implicitDup:
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
			case lazySplit:
				return getSplitFrom().canRedefine();
			case lazyMerge:
				return false; // TODO
			case implicitDup:
				return canForget();
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

	void forget(){
		final switch(kind)with(Kind){
			case definition,constPinned:
				goto case constUse;
			case lazySplit:
				auto lu=getSplitFrom();
				assert(lu&&lu.numPendingSplits>0);
				if(lu.numPendingSplits==1&&lu.canForget())
					return lu.forget();
				assert(!dep.isTop);
				scope_.forgetOnEntry(decl);
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
}

struct LastUses{
	LastUses* parent;
	LastUse[Declaration] lastUses;
	LastUse* lastLastUse;
	void nest(NestedScope r)return in{
		with(r.lastUses){
			assert(!parent);
			assert(!lastUses.length);
			assert(!lastLastUse);
		}
	}do{
		r.lastUses.parent=&this;
		foreach(d,lu;lastUses){
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
		if(auto prevLastUse=lastUse.decl in lastUses){
			prevLastUse.remove();
			lastUses.remove(lastUse.decl);
		}
		lastUses[lastUse.decl]=lastUse;
		auto newLastLastUse=lastUse.decl in lastUses;
		if(lastLastUse) lastLastUse.append(newLastLastUse);
		lastLastUse=newLastLastUse;
	}
	void definition(Declaration decl,Expression defExp)in{
		assert(!!decl.scope_);
	}do{
		Identifier use=null;
		add(LastUse(LastUse.kind.definition,decl.scope_,decl,use,defExp));
	}
	void lazySplit(Declaration decl,NestedScope sc)in{
		assert(decl.scope_&&sc);
		assert(sc.isNestedIn(decl.scope_));
	}do{
		auto lu=LastUse(LastUse.kind.lazySplit,sc,decl);
		static if(language==silq) lu.dep=sc.getDependency(decl);
		++lu.getSplitFrom().numPendingSplits;
		add(lu);
	}
	void lazyMerge(Declaration decl,Scope sc)in{
		assert(!!sc);
		assert(decl.mergedFrom.length);
	}do{
		add(LastUse(LastUse.kind.lazyMerge,sc,decl));
	}
	void implicitForget(Identifier use,Expression forgetExp,Dependency forgetDep)in{
		assert(!!use);
		assert(use.byRef);
		assert(!use.constLookup);
		assert(!!use.meaning);
		assert(!!use.scope_);
	}do{
		add(LastUse(LastUse.Kind.implicitForget,use.scope_,use.meaning,use,forgetExp,forgetDep));
	}
	void implicitDup(Identifier use)in{
		assert(!!use);
		assert(use.implicitDup);
		assert(!use.constLookup);
		assert(!!use.meaning);
		assert(!!use.scope_);
	}do{
		add(LastUse(LastUse.Kind.implicitDup,use.scope_,use.meaning,use));
	}
	void constUse(Identifier use,Expression parent)in{
		assert(!!use);
		assert(use.constLookup||use.implicitDup);
		assert(!!use.scope_);
	}do{
		add(LastUse(LastUse.Kind.constUse,use.scope_,use.meaning,use,parent));
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
		auto lastUse=decl in lastUses;
		assert(!!lastUse);
		add(LastUse(LastUse.Kind.consumption,sc,decl,use));
	}

	bool canForget(Declaration decl,bool forceHere){
		auto lastUse=decl in lastUses;
		if(!lastUse&&!forceHere&&parent)
			return parent.canForget(decl,false);
		return lastUse&&lastUse.canForget();
	}
	bool canRedefine(Declaration decl){
		if(auto lastUse=decl in lastUses)
			return lastUse.canRedefine();
		return parent&&parent.canRedefine(decl);
	}
	bool betterUnforgettableError(Declaration decl,Scope sc){
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
		assert(splitInto !in lastUses);
	}do{
		if(splitFrom !in lastUses) return;
		lastUses[splitInto]=lastUses[splitFrom];
		lastUses.remove(splitFrom);
		lastUses[splitInto].replaceDecl(splitFrom,splitInto);
	}
}
