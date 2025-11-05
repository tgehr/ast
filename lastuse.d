// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.lastuse;
import astopt;

import std.range, std.algorithm, std.conv, std.format;
import ast.expression,ast.type,ast.declaration,ast.scope_;

bool canAddForget(Expression e){
	if(auto le=cast(LetExp)e)
		return !!le.isForward(true);
	if(auto ce=cast(CompoundExp)e)
		return !ce.blscope_;
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
		assert(!!tpl);
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
	Scope scope_;
	Declaration decl=null;
	Identifier use=null;
	Identifier[] constBlock;
	Expression parent=null;
	static if(language==silq)
		auto dep=Dependency(true);
	LastUse forwardTo=null;
	LastUse constConsume=null;
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
		})(Forgettability.forgettable);
	}
	static bool canForgetMerge(Declaration decl,scope NestedScope[] nestedScopes,bool forceHere,bool forceConsumed){
		return getMergeForgettability(decl,nestedScopes,forceHere)>=(forceConsumed?Forgettability.consumable:Forgettability.forgettable);
	}
	static bool canCancelImplicitDupMerge(Declaration decl,scope NestedScope[] nestedScopes){
		return iota(nestedScopes.length).map!((i){
			auto nsc=nestedScopes[i];
			auto cdecl=decl;
			if(decl.mergedFrom.length==nestedScopes.length&&decl.mergedFrom[i].scope_ is nsc)
				cdecl=decl.mergedFrom[i];
			return nsc.lastUses.canCancelImplicitDup(cdecl);
		}).any;
	}

	void remove(){
		assert(!prev||prev.next is this);
		assert(!next||next.prev is this);
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
		//imported!"util.io".writeln("APPENDING: ",this," ⇒ ",next);
	}

	void pinSplits(){ return pinImpl(true); }
	void pin(){ return pinImpl(false); }
	void pinImpl(bool includingSplits){
		if(forwardTo) forwardTo.pin();
		if(splitFrom) splitFrom.pin();
		if(!includingSplits&&kind==Kind.lazySplit) return;
		if(isConsumption()) return;
		//imported!"util.io".writeln("PINNING: ",this);
		kind=Kind.constPinned;
		if(splitFrom) splitFrom.pinSplits();
	}

	private void markConsumed(Identifier theUse,bool isForget){
		if(!use) use=theUse;
		//imported!"util.io".writeln("MARKING CONSUMED: ",this," ",use?text(use.loc):"<?>");
		if(isConsumption()) return;
		if(splitSource&&splitSource.splitFrom)
			splitSource.splitFrom.markConsumed(theUse,false);
		if(splitFrom) splitFrom.markConsumed(theUse,false);
		if(isForget){
			assert(!dep.isTop);
			kind=Kind.synthesizedForget;
		}else kind=Kind.consumption;
		updateDependenciesOnConsumptionLocal();
	}
	private void updateDependenciesOnConsumption(){
		//imported!"util.io".writeln("UPDATING ALL: ",this);
		if(auto parent=decl.splitFrom){
			assert(parent.splitInto.canFind(decl));
			foreach(split;parent.splitInto){
				if(auto lu=split.scope_.lastUses.get(split,true)){
					if(auto source=lu.splitSource)
						lu=source;
					lu.updateDependenciesOnConsumptionLocal();
				}
			}
		}else updateDependenciesOnConsumptionLocal();
	}
	private void updateDependenciesOnConsumptionLocal(){
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
			//imported!"util.io".writeln("VISITING: ",lu," ",decl," ",cdep," ",use?text(use.loc):"<?>");
			lu.dep.replace(decl,cdep);
			//imported!"util.io".writeln("REPLACED: ",lu," ",decl," ",cdep);
			if(lu.kind.among(Kind.consumption,Kind.synthesizedForget)||lu.use&&lu.use.implicitDup){
				cdep.replace(lu.decl,lu.dep);
				if(!lu.decl.isSemError()&&lu.isConsumption()){
					//imported!"util.io".writeln("CHECKING: ",lu," ",lu.use?text(lu.use.loc):"<?>"," ",lu.constBlock);
					lu.checkConsumable();
				}
				if(!lu.decl.isSemError()&&lu.dep.isTop){
					if(lu.kind==Kind.synthesizedForget){
						if(lu.use && lu.use.scope_){
							lu.scope_.error(format("cannot synthesize forget expression for `%s`",lu.use),lu.use.loc);
						}else if(lu.decl.scope_){
							auto d=lu.decl,sc=lu.decl.scope_;
							if(cast(Parameter)d) sc.error(format("%s `%s` is not consumed (perhaps return it or annotate it `const`)",d.kind,d.getName),d.loc);
							else sc.error(format("%s `%s` is not consumed (perhaps return it)",d.kind,d.getName),d.loc);
							if(cast(ReturnExp)lu.parent) sc.note("at function return",lu.parent.loc);
						}
						lu.decl.setSemForceError();
						if(lu.use) lu.use.setSemForceError();
						if(lu.parent) lu.parent.setSemForceError();
						// TODO: the error has to be propagated out further
					}else if(!lu.decl.isSemError()&&lu.use&&lu.use.implicitDup){
						//imported!"util.io".writeln("FOUND CANCELABLE DUP AT: ",lu.use.loc);
						lu.cancelImplicitDup();
					}
				}
			}
		}
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
					csc.replaceDecl(d,cdecl);
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
		if(constBlock.length) scope_.updateDeclProps(decl).constBlock=oldConstBlock;
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
						lu.markConsumed(use,isForget);
				}
				if(nested.forgottenVars.canFind(result)){
					nested.forgottenVars=nested.forgottenVars.filter!(d=>d!is result).array; // TODO: make more efficient
				}
				nested.checkDeclarationCancel(result,use);
				removeCopies(nested);
			}
		}
		removeCopies(scope_);
		markConsumed(use,isForget);
		return ok;
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
			case definition:
				goto case constUse;
			case constPinned:
				return Forgettability.none;
			case lazySplitSink:
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
			case definition:
				goto case constUse;
			case constPinned:
				assert(0);
			case lazySplitSink:
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
						markConsumed(use,false);
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
				scope_.updateDeclProps(decl).accesses~=use; // TODO: this is out of order, ok?
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
				return false;
			case consumption:
				return false;
			case capture:
				return false; // TODO
		}
		return true;
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
				ok&=consume(false);
				foreach(i,nsc;nestedScopes){
					auto cdecl=decl;
					if(decl.mergedFrom.length==nestedScopes.length&&decl.mergedFrom[i].scope_ is nestedScopes[i])
						cdecl=decl.mergedFrom[i];
					else if(decl.splitInto.length==nestedScopes.length&&decl.splitInto[i].scope_ is nestedScopes[i])
						cdecl=decl.splitInto[i];
					//imported!"util.io".writeln("MERGED FROM: ",nsc.lastUses.lastUses.get(cdecl,null)," ",decl.mergedFrom," ",nsc.lastUses.lastUses," ",nsc.lastUses.lastUses.get(decl,null));
					if(!use){
						if(auto lu=nsc.lastUses.get(cdecl,true))
							use=lu.use;
					}
					if(nsc.lastUses.canCancelImplicitDup(cdecl)){
						nsc.lastUses.cancelImplicitDup(cdecl);
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
				//imported!"util.io".writeln("CONSUMING: ",this," ",use.loc," ",constBlock," ",dep);
				ok&=consume(false);
				return ok;
			case constUse:
				if(constConsume&&constConsume.canCancelImplicitDup()){
					constConsume.cancelImplicitDup();
					markConsumed(use,false);
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
			lazySplitSink(d,parent);
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
				assert(lastUse.kind.among(definition,lazySplitSink,lazySplit,lazyMerge,capture,constPinned,synthesizedForget));
			}
		}
		assert(!lastUse.prev&&!lastUse.next);
	}do{
		//imported!"util.io".writeln("ADDING LU: ",lastUse);
		static if(language==silq){
			lastUse.dep=lastUse.scope_.getDependency(lastUse.decl).dup;
			assert(lastUse.kind!=LastUse.kind.synthesizedForget||!lastUse.dep.isTop);
		}
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
			if(lastUse.kind==LastUse.Kind.constUse){
				//imported!"util.io".writeln("ATTACHING CONSTCONSUME: ",prevLastUse);
				lastUse.constConsume=prevLastUse;
				keep=true;
			}
			if(prevLastUse.kind==LastUse.Kind.constPinned){
				if(prevLastUse.use&&prevLastUse.use.implicitDup)
					keep=true;
			}
			if(prevLastUse.splitFrom){
				//imported!"util.io".writeln("PINNING SPLITS: ",lastUse," ",prevLastUse);
				if(lastUse.kind!=LastUse.Kind.lazySplitSink)
					prevLastUse.pinSplits();
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
		lastUses[lastUse.decl]=lastUse;
		if(lastLastUse) lastLastUse.append(lastUse);
		lastLastUse=lastUse;
		if(lastUse.isConsumption()){
			if(lastUse.splitSource&&lastUse.splitSource.splitFrom)
				lastUse.splitSource.splitFrom.markConsumed(lastUse.use,false);
			lastUse.updateDependenciesOnConsumption();
		}
	}
	void definition(Declaration decl,Expression defExp)in{
		assert(!!decl.scope_);
	}do{
		Identifier use=null;
		add(new LastUse(LastUse.Kind.definition,decl.scope_,decl,use,defExp));
	}
	void lazySplitSink(Declaration decl,Scope sc)in{
		assert(decl.scope_&&sc);
	}do{
		auto lu=new LastUse(LastUse.Kind.lazySplitSink,sc,decl,null,null);
		lu.forwardTo=sc.lastUses.lastUses.get(decl,null);
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
		//imported!"util.io".writeln("SYNTHESIZEDFORGET: ",use?text(use.loc):"<?>");
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
			if(auto le=cast(LetExp) parent) return le;
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
			le.constLookup=false;
			finish(le);
			return le;
		}
		static if(language==silq) auto depOk=!use.scope_.getDependency(use.meaning).isTop;
		else enum depOk=true;
		if(!inType&&depOk){
			if(isStatement){
				auto ce=cast(CompoundExp)parent;
				if(!ce||ce.blscope_){
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
			}else if(!parent.constLookup&&!cast(Identifier)parent)
				parent=getLet();
		}
		//imported!"util.io".writeln("MADE: ",parent);
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
		//imported!"util.io".writeln("CONSUMPTION: ",decl," ",use);
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
