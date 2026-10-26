// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.scope_;
import astopt;

import std.format, std.conv, std.range, std.algorithm;
import util.tuple:Q=Tuple,q=tuple;
import ast.lexer, ast.expression, ast.declaration, ast.type, ast.error;
import util, util.hashtable: HashMap;

struct Dependency{
	bool isTop;
	SetX!Declaration dependencies;
	Declaration lostVar; // (if `isTop`: a consumed value it depended on, if known)
	Identifier lostAt; // (where `lostVar` was consumed)
	void joinWith(Dependency rhs){
		if(isTop) return;
		if(rhs.isTop){
			this=rhs;
			return;
		}
		foreach(x;rhs.dependencies)
			dependencies.insert(x);
	}
	void remove(Declaration decl){
		dependencies.remove(decl);
	}
	void replace(Declaration decl, Dependency rhs, Identifier consumedAt=null){
		if(decl !in dependencies) return;
		dependencies.remove(decl);
		if(rhs.isTop&&!rhs.lostVar&&consumedAt){
			rhs.lostVar=decl;
			rhs.lostAt=consumedAt;
		}
		joinWith(rhs);
	}
	void replace(Declaration decl,Declaration ndecl){
		if(decl in dependencies){
			dependencies.remove(decl);
			dependencies.insert(ndecl);
		}
	}
	Dependency dup(){
		return Dependency(isTop, dependencies.dup, lostVar, lostAt);
	}
	private Q!(bool,SetX!Id) getIds(){
		SetX!Id result;
		foreach(decl;dependencies){
			auto id=decl.getId;
			if(id==Id()) continue;
			assert(id !in result);
			result.insert(id);
		}
		return q(isTop,result);
	}
	bool matches(Dependency rhs){ // TODO: make faster?
		auto ids=getIds,rids=rhs.getIds;
		return ids==rids;
	}
}

struct Dependencies{
	HashMap!(Declaration,Dependency,(a,b)=>a is b,(a)=>a.toHash()) dependencies;
	void joinWith(Dependencies rhs){
		foreach(k,ref v;dependencies){
			if(k in rhs.dependencies){
				v.joinWith(rhs.dependencies[k]);
				if(k in v.dependencies)
					v=Dependency(true); // TODO: get rid of this
			}
		}
	}
	void pushUp(Declaration removed, bool keep, Identifier consumedAt=null)in{
		assert(removed in dependencies,text(removed," ",removed.loc," ",dependencies));
	}do{
		Dependency x=dependencies[removed];
		if(!keep) dependencies.remove(removed);
		foreach(k,ref v;dependencies){
			v.replace(removed, x, consumedAt);
			if(k in v.dependencies)
				v=Dependency(true); // TODO: get rid of this
		}
	}
	void replace(Declaration decl,Declaration ndecl)in{
		assert(decl in dependencies,text(decl.loc," ",dependencies));
		assert(ndecl !in dependencies,text(ndecl.loc," ",dependencies));
	}do{
		foreach(k,ref v;dependencies) v.replace(decl,ndecl);
		dependencies[ndecl]=dependencies[decl];
		dependencies.remove(decl);
	}
	void merge(Declaration decl,Declaration ndecl)in{ // (`ndecl` is another version of the variable of `decl`)
		assert(decl in dependencies&&ndecl in dependencies);
	}do{
		auto dep=dependencies[decl];
		dependencies.remove(decl);
		foreach(k,ref v;dependencies) v.replace(decl,ndecl);
		dependencies[ndecl].joinWith(dep);
		foreach(k,ref v;dependencies)
			if(k in v.dependencies)
				v=Dependency(true); // TODO: get rid of this
	}
	void substitute(Declaration decl,Dependency dep){ // substitute `decl` by `dep` inside all tracked sets (`decl` itself has no entry)
		foreach(k,ref v;dependencies){
			v.replace(decl,dep);
			if(k in v.dependencies)
				v=Dependency(true); // TODO: get rid of this
		}
	}
	Dependencies dup(){
		typeof(Dependencies.dependencies) result;
		foreach(k,ref v;dependencies)
			result[k]=v.dup;
		return Dependencies(result);
	}
	bool canForget(Declaration decl)in{
		assert(decl in dependencies||decl.isSemError(),text(decl," ",dependencies));
	}do{
		if(decl !in dependencies) return true;
		return !dependencies[decl].isTop;
	}
	void clear(){
		dependencies.clear();
	}
	private HashMap!(Id,typeof(Dependency.getIds()),(a,b)=>a is b,(a)=>a.toHash) getIds(){
		typeof(return) result;
		foreach(decl,ref dependency;dependencies){
			auto id=decl.getId;
			if(id==Id()) continue;
			assert(id !in result,text(decl," ",dependencies," ",result));
			result[id]=dependency.getIds();
		}
		return result;
	}
	bool matches(Dependencies rhs){ // TODO: make faster?
		auto ids=getIds,rids=rhs.getIds;
		return ids==rids;
	}
}

struct DummyWitnessContext{
	MapX!(Declaration,Declaration) dummies; // candidate -> dummy placeholder
	MapX!(Declaration,Declaration) results; // candidates witnessed so far
	MapSX!(Declaration,Dependency) consumedDeps; // dependency each decl had when it was consumed while this context was active
	SetX!Id[] nestedLoopCarried; // the loop-carried candidates of each nested quantum loop analyzed while this context was active
	Dependency[] reconstructed; // dependencies of quantum guards whose inputs change while borrowed
}

import ast.lastuse;
enum Lookup{
	consuming,
	constant,
	probing,
	probingWithCapture,
}

abstract class Scope{
	final TopScope getTopScope(){
		for(Scope sc=this;sc;){
			if(auto ts=cast(TopScope)sc) return ts;
			auto nsc=cast(NestedScope)sc;
			if(!nsc) return null;
			sc=nsc.parent;
		}
		return null;
	}
	abstract @property ErrorHandler handler();
	import ast.looplowering:LoopContinuation;
	LoopContinuation loopContinuation; // loop lowering: code after a loop that the lowering may absorb
	bool allowsLinear(){
		return true;
	}
	Scope parentScope(){
		return null;
	}
	@property bool inferenceMode(){
		return false;
	}
	final bool canInsert(Id id){
		auto decl=symtabLookup(id,false,null);
		return !decl||cast(DeadDecl)decl;
	}

	static if(language==silq) final bool checkCaptureRedefinition(Declaration decl){
		auto fd=getFunction();
		if(!fd||!decl.name||!fd.fscope_||cast(Parameter)decl) return true;
		if(Id.s!"silq-loop" in fd.attributes||Id.s!"silq-join" in fd.attributes) return true;
		bool inBody(Identifier id){
			return fd.body_&&fd.body_.blscope_&&id.scope_&&id.scope_.isNestedIn(fd.body_.blscope_);
		}
		foreach(capture,allIds;fd.captures){
			if(!capture.name||capture.name.id!=decl.name.id) continue;
			auto ids=allIds.filter!inBody.array;
			if(!ids.length) continue;
			if(fd.isConsumedCapture(capture)) continue;
			import ast.semantic_:typeForDecl;
			auto type=typeForDecl(capture);
			if(type&&type.isClassical()&&ids.any!(id=>!id.constLookup)&&!capture.isConst()){ // (a `const` variable is not consumed by a capture)
				fd.consumingCaptures.insert(decl.name.id);
				fd.captureReanalysis=true;
				for(auto efd=fd.scope_.getFunction();efd&&capture.scope_&&!capture.scope_.isNestedIn(efd.fscope_);efd=efd.scope_.getFunction()){
					efd.consumingCaptures.insert(decl.name.id);
					efd.captureReanalysis=true;
				}
				return true;
			}
			if(!decl.isSemError()){
				error(format("redefinition of captured variable \"%s\"",decl.name),decl.name.loc);
				note("captured here",ids[0].loc);
				decl.setSemError();
			}
			return false;
		}
		return true;
	}
	final bool tryPrepareRedefine(Declaration newDecl,Declaration oldDecl){
		static if(language==silq) if(blockedRedefinitionError(newDecl,oldDecl)) return false;
		if(oldDecl.scope_&&lastUses.canRedefine(oldDecl)){
			static if(language==silq) if(consumesOutsideType(oldDecl,letTypeBoundary())){ // (the previous version is forgotten)
				if(!oldDecl.isSemError()&&!newDecl.isSemError()) error(format("cannot consume `%s` in a type",oldDecl.name),newDecl.name.loc);
				newDecl.setSemError();
				return false;
			}
			lastUses.forget(oldDecl,true);
			return true;
		}
		if(!oldDecl.isSemError()&&!newDecl.isSemError()) redefinitionError(newDecl, oldDecl);
		newDecl.setSemError();
		return false;
	}
	final void redefinitionError(Declaration decl, Declaration prev) in{
		assert(decl&&prev);
		assert(!cast(DeadDecl)decl&&!cast(DeadDecl)prev);
	}do{
		error(format("redefinition of \"%s\"",decl.name), decl.name.loc);
		note("previous definition was here",prev.name.loc);
		decl.setSemError();
	}

	bool insert(Declaration decl,bool force=false)in{assert(!decl.scope_);}do{
		if(auto d=symtabLookup(decl.name,false,null)){
			static if(language==silq) if(isConstLocal(d)&&!d.isSemError()){
				if(!decl.isSemError()){
					error(format("redefinition of `const` variable \"%s\"",decl.name),decl.name.loc);
					note("previous definition was here",d.name.loc);
				}
				decl.setSemError();
				return false;
			}
			if(!tryPrepareRedefine(decl,d))
				return false;
			//assert(!symtabLookup(decl.name,false,null));
		}else static if(language==silq){
			for(Scope sc=this;sc;sc=cast(FunctionScope)sc?null:sc.parentScope()){
				auto d=sc.peekSymtab(decl.name.id,false);
				if(!d) continue;
				if(auto dd=cast(DeadDecl)d)
					if(dd.reportRedefinition(decl,this))
						return false;
				break;
			}
			if(!checkCaptureRedefinition(decl)) return false;
		}
		rename(decl);
		symtabInsert(decl);
		decl.scope_=this;
		return true;
	}

	void symtabInsert(Declaration decl)in{
		assert(!toRemove.canFind(decl));
		assert(!!decl);
		assert(decl.getId !in rnsymtab||cast(DeadDecl)rnsymtab[decl.getId]);
	}do{
		if(decl.name.id !in symtab||cast(DeadDecl)symtab[decl.name.id])
			symtab[decl.name.id]=decl;
		rnsymtab[decl.getId]=decl;
	}
	void symtabRemove(Declaration decl)in{
		assert(!!decl);
		assert(rnsymtab.get(decl.getId,null) is decl);
	}do{
		if(symtab.get(decl.name.id,null) is decl)
			symtab.remove(decl.name.id);
		rnsymtab.remove(decl.getId);
	}

	static struct DeclProp{
		Identifier[] constBlock;
		static struct ComponentReplacement{
			IndexExp write; // null for temporary conversion
			Id name;
			IndexExp read;
			IndexExp constRead;
			IndexExp convertedWrite;
			IndexExp location(){ return write?write:convertedWrite; }
			bool blocksAggregate(){ return !write&&convertedWrite; }
		}
		ComponentReplacement[] componentReplacements;
		void nameIndex(IndexExp index,Id name){
			auto r=ComponentReplacement(index,name,IndexExp.init);
			if(index.isSemError()) swap(r.write,r.read);
			componentReplacements~=r;
		}
		/+private+/ Identifier[] accesses;
		/+private+/ Declaration[] capturers;
		static DeclProp default_(){
			return DeclProp.init;
		}
		DeclProp dup(){
			return DeclProp(constBlock,componentReplacements.dup,accesses.dup,capturers.dup);
		}
		DeclProp move(){
			auto r=DeclProp(constBlock,componentReplacements,accesses,capturers);
			this=typeof(this).init;
			return r;
		}
		DeclProp inherit(){ return default_(); }
		enum inheritIsDefault=true; // set to false if inherit becomes nontrivial
		DeclProp merged()in{
			//assert(!constBlock);
			assert(!componentReplacements.length);
		}do{
			constBlock=[]; // TODO: ok?
			return this;
		}
		void merge(DeclProp nested)in{
			//assert(!nested.constBlock);
			assert(!nested.componentReplacements.length);
		}do{
			accesses~=nested.accesses;
			capturers~=nested.capturers;
		}
		void replaceDecl(Declaration splitFrom,Declaration splitInto){
			foreach(id;accesses){ // TODO: avoid considering the same access multiple times in different scopes
				// foreach(id,decl;declProps.accesses.map!(x=>x)) hangs the compiler
				//imported!"util.io".writeln("ADJUSTING: ",id.loc," ",id.meaning is splitFrom," ",id.meaning is splitInto);
				id.meaning=splitInto;
				//if(id.scope_) id.scope_.lastUses.replaceDecl(splitFrom,splitInto);
			}
			foreach(capturer;capturers){
				void doIt(T)(T capturer){
					if(splitFrom !in capturer.captures) return;
					capturer.captures[splitInto]=capturer.captures[splitFrom];
					capturer.captures.remove(splitFrom);
					foreach(ref oldDecl;capturer.capturedDecls){
						if(oldDecl is splitFrom){
							oldDecl=splitInto;
							break;
						}
					}
					foreach(id;capturer.captures[splitInto])
						id.meaning=splitInto;
				}
				if(auto fd=cast(FunctionDef)capturer) doIt(fd);
				else if(auto dat=cast(DatDecl)capturer) doIt(dat);
				else assert(0,text(typeid(capturer)));
			}
		}
	}
	static struct DeclProps{
		private MapSX!(Declaration,DeclProp) props;
		DeclProps dup(){ return DeclProps(props.dup); }
		void clear(){ props.clear(); }
		DeclProp* tryGet(Declaration decl){ return props.getPtr(decl); }
		ref DeclProp set(Declaration decl,DeclProp prop){
			return props[decl]=prop;
		}
		void remove(Declaration decl){
			props.remove(decl);
		}
		void merge(ref DeclProps nested){
			foreach(decl,ref prop;nested.props){
				if(decl !in props) props[decl]=prop.merged();
				else props[decl].merge(prop);
			}
		}
		void replaceDecl(Declaration splitFrom,Declaration splitInto){
			if(auto declProp=tryGet(splitFrom)){
				declProp.replaceDecl(splitFrom,splitInto);
				props[splitInto]=declProp.move();
				props.remove(splitFrom);
			}
		}
		void moveComponentReplacements(Declaration prev,Declaration new_){
			if(auto prevProp=tryGet(prev)){
				if(new_ !in props) set(new_,DeclProp.default_());
				auto newProp=tryGet(new_);
				assert(newProp&&!newProp.componentReplacements.length);
				newProp.componentReplacements=prevProp.componentReplacements;
				prevProp.componentReplacements=[];
			}
		}
	}
	final DeclProps saveDeclProps(){ return declProps.dup; }
	final void resetDeclProps(DeclProps previous){ declProps=previous; }
	final void mergeDeclProps(ref DeclProps nested,ComponentConstBlock[] nestedComponentConstBlocks){
		foreach(decl,ref prop;nested.props){
			if(!prop.constBlock.length) continue;
			if(!decl.scope_||!this.isNestedIn(decl.scope_)) continue;
			foreach(read;prop.constBlock){
				Expression.CopyArgs cargs={preserveSemantic: true};
				auto nread=read.copy(cargs);
				nread.scope_=this;
				blockConst(decl,nread);
				recordAccess(nread,decl);
				foreach(ccb;nestedComponentConstBlocks)
					if(ccb.read is read)
						componentConstBlocks~=ComponentConstBlock(decl,ccb.component,nread);
			}
			prop.constBlock=[];
		}
		declProps.merge(nested);
	}
	final int nestedDeclProps(scope int delegate(ref DeclProps) dg){
		if(auto r=dg(declProps)) return r;
		return outerDeclProps(dg);
	}
	int outerDeclProps(scope int delegate(ref DeclProps) dg){
		return 0;
	}
	final nestedDeclProp(Declaration decl){
		static struct NestedDeclProps{
			Scope sc;
			Declaration decl;
			int opApply(scope int delegate(ref DeclProp) dg){
				foreach(ref props;&sc.nestedDeclProps){
					if(auto prop=props.tryGet(decl)){
						if(auto r=dg(*prop))
							return r;
					}
				}
				return 0;
			}
		}
		return NestedDeclProps(this,decl);
	}
	// DMD/LDC bug: if this function returns ref DeclProp,
	// memory corruption occurs
	final DeclProp* updateDeclProps(Declaration decl){
		if(auto r=declProps.tryGet(decl)) return r;
		static if(!DeclProp.inheritIsDefault){
			foreach(ref prop;nestedDeclProp(decl)){
				return &declProps.set(decl,prop.inherit);
			}
		}
		return &declProps.set(decl,DeclProp.default_());
	}
	final void recordAccess(Identifier id,Declaration meaning){
		if(id.typeofSuppressedCapture) return;
		if(!meaning.isToplevelDeclaration()&&!meaning.isAggregateMember()){
			lastUses.pin(meaning,false); // previous last use cannot be used to forget anymore
			static if(language==silq) pinTypeMentions(meaning); // (as are the variables that its type mentions)
			if(!id.constLookup&&!id.implicitDup)
				lastUses.consumption(meaning,id,this); // TODO: ok?
			updateDeclProps(meaning).accesses~=id;
		}
	}
	static if(language==silq)
	final void pinTypeMentions(Declaration meaning){ // (the variables that the type of `meaning` mentions are live where it is used)
		import ast.semantic_: typeForDeclNoAnalyze;
		if(auto type=typeForDeclNoAnalyze(meaning)) pinMentions(type);
	}
	static if(language==silq)
	final void pinMentions(Expression type){ // (the variables that `type` mentions are live here)
		foreach(fid;type.freeIdentifiers)
			if(fid.meaning&&!fid.meaning.isToplevelDeclaration()&&!fid.meaning.isAggregateMember()) lastUses.pin(getSplit(fid.meaning),false);
	}
	final void recordCapturer(Declaration capturer,Declaration meaning){
		if(!meaning.isToplevelDeclaration){
			updateDeclProps(meaning).capturers~=capturer;
		}
	}
	private final Identifier isConstHere(Declaration decl){
		if(auto r=declProps.tryGet(decl))
			if(r.constBlock.length)
				return r.constBlock[$-1];
		return null;
	}
	final void registerConstCapture(Declaration decl,Location loc,Expression type){
		if(decl.isToplevelDeclaration()||decl.isPinned()) return;
		if(!type||type.isClassical()) return; // TODO: why needed?
		if(auto prev=isConstHere(decl)) if(prev.meaning is decl&&prev.loc==loc) return;
		auto cid=new Identifier(decl.getId);
		cid.loc=loc;
		cid.scope_=this;
		cid.meaning=decl;
		cid.type=type;
		cid.constLookup=true;
		cid.setSemCompleted();
		blockConst(decl,cid);
	}
	final void blockConst(Declaration decl,Identifier constBlock){
		if(!decl.isToplevelDeclaration){
			if(auto props=updateDeclProps(decl))
				props.constBlock~=constBlock;
		}
	}
	static struct ComponentConstBlock{
		Declaration decl;
		IndexExp component;
		Identifier read;
	}
	private ComponentConstBlock[] componentConstBlocks;
	final void recordComponentConstBlock(Declaration decl,Identifier read,IndexExp component)in{
		assert(decl&&!decl.isToplevelDeclaration);
		assert(!!read);
		assert(!!component);
	}do{
		if(auto props=declProps.tryGet(decl))
			if(props.constBlock.length&&props.constBlock[$-1] is read)
				componentConstBlocks~=ComponentConstBlock(decl,component,read);
	}
	int outerComponentConstBlocks(scope int delegate(ComponentConstBlock) dg){
		return 0;
	}
	final int nestedComponentConstBlocks(scope int delegate(ComponentConstBlock) dg){
		foreach(ccb;componentConstBlocks)
			if(auto r=dg(ccb)) return r;
		return outerComponentConstBlocks(dg);
	}
	final bool isComponentConstBlock(Identifier read){
		bool result=false;
		nestedComponentConstBlocks((ComponentConstBlock ccb){
			if(ccb.read is read) result=true;
			return result;
		});
		return result;
	}
	final bool hasNonComponentConstBlock(Declaration decl){
		for(auto d=decl;d;d=d.splitFrom)
			foreach(ref prop;nestedDeclProp(d))
				foreach(read;prop.constBlock)
					if(!isComponentConstBlock(read)) return true;
		return false;
	}
	final bool componentConstBlocksAllow(Declaration decl,IndexExp write,Location loc){
		import ast.semantic_:guaranteedDisjointComponents,InType;
		bool any=false,result=true;
		for(auto d=decl;d;d=d.splitFrom)
			foreach(ref prop;nestedDeclProp(d)){
				foreach(read;prop.constBlock){
					any=true;
					bool component=false;
					nestedComponentConstBlocks((ComponentConstBlock ccb){
						if(ccb.read !is read) return 0;
						component=true;
						if(!guaranteedDisjointComponents(ccb.component,write,loc,this,InType.no))
							result=false;
						return 1;
					});
					if(!component||!result) return false;
				}
			}
		return any&&result;
	}
	final bool componentConstBlockRedefined(ConstBlockContext context){
		foreach(ccb;componentConstBlocks[context.numComponentConstBlocks..$])
			if(peekSymtab(ccb.decl.getId,true) !is ccb.decl)
				return true;
		return false;
	}
	final bool componentConstBlockConsumedDuringBorrow(ConstBlockContext context){
		foreach(ccb;componentConstBlocks[context.numComponentConstBlocks..$])
			if(peekSymtab(ccb.decl.getId,true) !is ccb.decl&&ccb.read.consumedDuringBorrow)
				return true;
		return false;
	}
	static struct TrackedTemporary{
		Expression expr;
		Dependency dep;
		Identifier read; // for recordConstBlockedConsumption
		TrackedTemporary dup(){
			return TrackedTemporary(expr,dep.dup);
		}
	}
	final bool trackTemporary(Expression expr){
		//imported!"util.io".writeln("TRACKING: ",expr," ",expr.loc);
		import ast.semantic_:getDependency;
		auto implicitDup=expr.implicitDup;
		expr.implicitDup=false;
		auto dep=getDependency(expr,this);
		expr.implicitDup=implicitDup;
		if(dep.isTop) return false;
		trackedTemporaries~=TrackedTemporary(expr,dep);
		if(auto id=cast(Identifier)expr){
			if(id.implicitDup&&id.meaning) {
				recordImplicitDup(id);
			}
		}
		return true;
	}
	void pinLastUse(Declaration decl){
		lastUses.pin(decl,true);
	}
	private struct TypeConstBlockEntry{
		Declaration decl;
	}
	private TypeConstBlockEntry[] typeConstBlockLog;
	private static void releaseTypeConstBlockEntry(TypeConstBlockEntry entry){
		auto decl=entry.decl;
		assert(decl.typeConstBlockDepth>0);
		if(--decl.typeConstBlockDepth==0) decl.typeConstBlocker=null;
	}
	final void recordTypeConstBlock(Declaration decl)in{
		assert(!!decl);
	}do{
		typeConstBlockLog~=TypeConstBlockEntry(decl);
		decl.typeConstBlockDepth++;
	}
	final size_t saveTypeConstBlocks(){
		return typeConstBlockLog.length;
	}
	final void releaseTypeConstBlocks(size_t save,bool doRelease)in{
		assert(save<=typeConstBlockLog.length);
	}do{
		foreach_reverse(i;save..typeConstBlockLog.length){
			auto entry=typeConstBlockLog[i];
			if(doRelease) releaseTypeConstBlockEntry(entry);
		}
		typeConstBlockLog.length=save;
	}
	final void filterTypeConstBlocks(size_t save,Expression type)in{
		assert(save<=typeConstBlockLog.length);
	}do{
		filterTypeConstBlocks(save,(Declaration decl){
			if(!type) return false;
			foreach(id;type.freeIdentifiers){
				if(id.meaning&&id.meaning.canonicalSource is decl.canonicalSource)
					return true;
			}
			return false;
		});
	}
	final void filterTypeConstBlocks(size_t save,bool delegate(Declaration) keep)in{
		assert(save<=typeConstBlockLog.length);
	}do{
		size_t j=save;
		foreach(i;save..typeConstBlockLog.length){
			auto entry=typeConstBlockLog[i];
			if(keep(entry.decl)) typeConstBlockLog[j++]=entry;
			else releaseTypeConstBlockEntry(entry);
		}
		typeConstBlockLog.length=j;
	}
	final void recordConstBlockedConsumption(Identifier read,Identifier use)in{
		assert(read.meaning&&read is isConst(read.meaning));
		assert(read.scope_);
	}do{
		if(read.meaning.isSemError()) return;
		import ast.semantic_:getDependency;
		auto dep=getDependency(read,read.scope_); // can already be top, will cause an error later
		read.scope_.trackedTemporaries~=TrackedTemporary(use,dep,read);
	}
	final void recordImplicitDup(Identifier id)in{
		assert(!!id);
		assert(id.implicitDup);
		assert(!id.constLookup);
		assert(!!id.meaning);
		assert(id.scope_ is this);
	}do{
		if(!id.meaning.isToplevelDeclaration()&&!id.typeofSuppressedCapture){
			if(isConsumable(id)) lastUses.implicitDup(id);
		}
	}

	final bool checkImplicitDupCancel(Identifier id)in{
		assert(id&&id.meaning);
	}do{
		return checkDeclarationCancel(id.meaning,id);
	}
	final bool checkDeclarationCancel(Declaration decl,Identifier use)in{
		assert(!!decl);
	}do{
		if(use&&use.isSemError()) return false;
		bool ok=true;
		Identifier[] accesses; // TODO: use ranges?
		if(auto declProp=declProps.tryGet(decl)) accesses=declProp.accesses;
		if(use&&use.scope_ !is this) // (all accesses here are after `use`, also those of versions split from `decl` in nested scopes)
			foreach(d,ref prop;declProps.props) if(d !is decl&&d.isDerivedFrom(decl)) accesses~=prop.accesses;
		if(accesses.length){
			bool seen=false;
			DeadDecl[] failures;
			foreach(access;accesses){
				if((!use||use.scope_!is this||seen)&&access !is use){
					if(ok&&use){
						if(auto cd=recordConsumption(decl,use))
							failures~=cd;
					}
					ok=false;
					if(use) use.setSemForceError();
					decl.setSemForceError();
					access.setSemForceError();
					import ast.semantic_:undefinedIdentifierError;
					undefinedIdentifierError(access,failures,this);
				}
				if(use&&access is use) seen=true;
			}
			// TODO: can we have `use.sstate != SemState.error` here?
		}
		static if(language==silq) if(ok&&use&&use.scope_ is this) ok=checkDeclarationCancelOuter(decl,use);
		return ok;
	}
	static if(language==silq)
	private bool checkDeclarationCancelOuter(Declaration decl,Identifier use){ // (accesses after the enclosing branches were analyzed before the cancellation)
		bool ok=true;
		DeadDecl[] failures;
		void reportLater(Identifier access,Scope sc){
			if(ok) if(auto cd=recordConsumption(decl,use)) failures~=cd;
			ok=false;
			use.setSemForceError();
			decl.setSemForceError();
			access.setSemForceError();
			import ast.semantic_:undefinedIdentifierError;
			undefinedIdentifierError(access,failures,sc);
		}
		static Declaration origin(Declaration d){ while(d.splitFrom) d=d.splitFrom; return d; }
		void visitActive(Scope sc){ // (accesses in nested scopes after the use that are still being analyzed)
			foreach(nsc;sc.activeNestedScopes){
				foreach(d,ref nprop;nsc.declProps.props){
					if(origin(d) !is origin(decl)) continue;
					foreach(access;nprop.accesses) if(!access.isSemError()) reportLater(access,nsc);
				}
				visitActive(nsc);
			}
		}
		for(auto inner=cast(NestedScope)this;inner;inner=cast(NestedScope)inner.parent){
			auto outer=inner.parent;
			if(!outer||outer.getFunction() !is getFunction()) break;
			if(!outer.activeNestedScopes.canFind(inner)) visitActive(outer);
			DeclProp* prop=null;
			for(auto d=decl;d&&!prop;d=d.splitFrom) prop=outer.declProps.tryGet(d);
			if(!prop) continue;
			auto siblings=inner.getSiblingScopes();
			bool seen=false;
			foreach(access;prop.accesses){
				if(access is use){
					seen=true;
					continue;
				}
				if(!seen||!access.scope_||access.scope_.isNestedIn(inner)) continue;
				if(siblings.any!(sib=>sib !is inner&&access.scope_.isNestedIn(sib))) continue; // (on another path)
				reportLater(access,outer);
			}
		}
		return ok;
	}

	final bool cancelImplicitDup(Identifier id)in{
		assert(!!id.implicitDup);
		assert(!!id.meaning);
		assert(!id.constLookup);
	}do{
		if(id.typeofSuppressedCapture) return true;
		bool ok=true;
		if(!checkConsumable(id)){
			ok=false;
			id.setSemForceError();
			id.meaning.setSemForceError();
		}
		lastUses.cancelImplicitDup(id.meaning); // TOOD: what if this fails?
		return ok;
	}
	final void pushTrackedTemporaryDependencies(Declaration decl){
		foreach(ref tt;trackedTemporaries){
			if(tt.dep.isTop) continue;
			this.pushUp(tt.dep,decl);
			if(!tt.dep.isTop) continue;
			if(auto id=cast(Identifier)tt.expr){
				if(!tt.read){
					if(id.implicitDup&&id.meaning){ // implicit dup no longer recomputable
						if(!cancelImplicitDup(id)){
							decl.setSemForceError();
						}
					}
				}
			}
		}
	}
	final bool checkTrackedTemporaries(TrackedTemporary[] trackedTemporaries,Expression parent){
		//imported!"util.io".writeln("CHECKING TEMPORARIES: ",trackedTemporaries," ",parent);
		bool success=true;
		foreach(ref tt;trackedTemporaries){
			if(!tt.dep.isTop) continue; // nothing to do for recomputable temporaries
			if(auto id=cast(Identifier)tt.expr){
				if(tt.read){ // non-recomputable const-blocked consumption
					if(id.meaning&&(!id.constLookup&&!id.implicitDup)){
						success=false;
						assert(tt.read.meaning);
						blockConst(tt.read.meaning,tt.read); // TODO: why needed?
						if(tt.read.scope_.checkConsumable(id,tt.read.meaning))
							assert(tt.read.meaning.isSemError);
						id.setSemForceError();
						id.meaning.setSemForceError();
						parent.setSemForceError();
					}
				}
			}
		}
		foreach(ref tt;trackedTemporaries){
			//imported!"util.io".writeln("CHECKING TRACKED TEMPORARY: ",tt);
			if(!tt.dep.isTop) continue;
			if(auto id=cast(Identifier)tt.expr){
				if(id.isSemError()) parent.setSemForceError();
				continue;
			}
			success=false;
			import ast.semantic_:nonLiftedError;
			nonLiftedError(tt.expr,this);
			tt.expr.setSemError();
			parent.setSemForceError();
		}
		return success;
	}
	final Identifier isConst(Declaration decl){
		foreach(ref prop;nestedDeclProp(decl)){
			auto r=prop.constBlock;
			if(r.length) return r[$-1];
		}
		return null;
	}
	final void inheritConstBlocks(Declaration prev,Declaration new_){ // new_ replaces prev, so it inherits prev's active const blocks
		foreach(ref props;&nestedDeclProps){
			bool done=false;
			for(auto d=prev;d&&!done;d=d.splitFrom)
				if(auto prop=props.tryGet(d))
					if(prop.constBlock.length){
						if(!props.tryGet(new_)) props.set(new_,DeclProp.default_());
						props.tryGet(new_).constBlock~=prop.constBlock;
						done=true;
					}
		}
	}
	static struct ConstBlockContext{
		private MapX!(Declaration,Identifier[]) constBlock;
		private size_t numTrackedTemporaries;
		private size_t numComponentConstBlocks;
	}
	final ConstBlockContext saveConst(){
		MapX!(Declaration,Identifier[]) constBlock;
		foreach(decl,ref prop;declProps.props){
			auto r=prop.constBlock;
			if(r.length) constBlock[decl]=r;
		}
		return ConstBlockContext(constBlock,trackedTemporaries.length,componentConstBlocks.length);
	}
	private void recordResetConst(Declaration decl,Identifier constBlock,ref Expression parent,bool isStatement,bool inType)in{
		assert(decl&&constBlock);
	}do{
		if(constBlock is parent&&!(!constBlock.type||constBlock.type.isClassical())) return; // TODO: would be nice if we would not need this, can happen e.g. in consumeArray
		if(auto lu=lastUses.get(decl,true)){
			if(lu.isConsumption()){
				if(constBlock.meaning){
					if(dependencyTracked(constBlock.meaning)&&!getDependency(constBlock.meaning).isTop){ // TODO: make this condition unnecessary?
						if(lu.kind==LastUse.Kind.consumption){
							lastUses.synthesizedForget(constBlock.meaning,null,this,parent);
						}
					}
				}
				return;
			}
			if(lu.kind==LastUse.Kind.implicitDup) return;
		}
		if(constBlock.scope_&&constBlock.meaning&&!constBlock.meaning.isToplevelDeclaration()){
			if(constBlock.meaning.isSemError()&&!constBlock.scope_.dependencyTracked(constBlock.meaning)) return; // (replaced after an error)
			lastUses.constUse(constBlock,parent,isStatement,inType);
		}
	}
	final bool resetConst(ConstBlockContext context,ref Expression parent,bool isStatement,bool inType){
		Identifier[] lookupSnapshot(Declaration decl){
			for(auto d=decl; d; d=d.splitFrom){
				if(auto r=context.constBlock.get(d,null)) return r;
			}
			return null;
		}
		Declaration lookupCurrent(Declaration decl){
			if(declProps.tryGet(decl)) return decl;
			foreach(d,ref prop;declProps.props){
				for(auto s=d.splitFrom; s; s=s.splitFrom){
					if(s is decl) return d;
				}
			}
			return null;
		}
		foreach(decl,ref prop;declProps.props){
			auto nconstBlock=lookupSnapshot(decl);
			if(prop.constBlock.length&&prop.constBlock!=nconstBlock){
				recordOuterConstReads(decl,prop.constBlock.filter!(read=>!nconstBlock.canFind(read)));
				recordResetConst(decl,prop.constBlock[$-1],parent,isStatement,inType);
			}
			prop.constBlock=nconstBlock;
		}
		foreach(decl,constBlock;context.constBlock){
			auto current=lookupCurrent(decl);
			if(!current) continue; // declaration was consumed/removed entirely
			auto prop=declProps.tryGet(current);
			assert(prop&&prop.constBlock==constBlock,text(prop is null," ",prop?prop.constBlock:null," ",constBlock));
		}
		auto success=checkTrackedTemporaries(trackedTemporaries[context.numTrackedTemporaries..$],parent);
		trackedTemporaries=trackedTemporaries[0..context.numTrackedTemporaries];
		componentConstBlocks=componentConstBlocks[0..context.numComponentConstBlocks];
		return success;
	}
	static struct OuterConstRead{
		Declaration decl;
		Identifier read;
		IndexExp component;
	}
	OuterConstRead[]* outerConstReads=null; // (const reads of outer variables that are reset, e.g., within a `let` expression in a `const` position)
	private void recordOuterConstReads(R)(Declaration decl,R reads){
		if(!outerConstReads||decl.scope_&&decl.scope_.isNestedIn(this)&&!decl.splitFrom) return;
		foreach(read;reads){
			IndexExp component=null;
			foreach(ccb;componentConstBlocks) if(ccb.read is read) component=ccb.component;
			*outerConstReads~=OuterConstRead(decl,read,component);
		}
	}
	final bool resetConst(ref Expression parent,bool isStatement,bool inType){
		foreach(decl,ref prop;declProps.props){
			if(prop.constBlock.length){
				recordOuterConstReads(decl,prop.constBlock);
				recordResetConst(decl,prop.constBlock[$-1],parent,isStatement,inType);
				prop.constBlock=[];
			}
		}
		auto success=checkTrackedTemporaries(trackedTemporaries,parent);
		trackedTemporaries=[];
		componentConstBlocks=[];
		return success;
	}
	final void resetLocalComponentReplacements(){
		foreach(decl,ref prop;declProps.props)
			prop.componentReplacements=[];
	}
	final DeclProp.ComponentReplacement[] localComponentReplacements(){
		typeof(return) r;
		foreach(decl,ref prop;declProps.props)
			r~=prop.componentReplacements;
		return r;
	}
	final DeclProp.ComponentReplacement[][] localComponentReplacementsByDecl(){
		Declaration[] decls;
		typeof(return) r;
		foreach(decl,ref prop;declProps.props){
			if(!prop.componentReplacements.length) continue;
			decls~=decl;
			r~=prop.componentReplacements;
		}
		sort!"a[0].getName<b[0].getName"(zip(decls,r));
		return r;
	}
	DeclProp.ComponentReplacement*[] allComponentReplacements(){ // TODO: get rid of this?
		typeof(return) r=[];
		foreach(ref props;&nestedDeclProps)
			foreach(decl,ref prop;props.props)
				r~=iota(prop.componentReplacements.length).map!(i=>&prop.componentReplacements[i]).array;
		return r;
	}
	final DeclProp.ComponentReplacement*[] componentReplacements(Declaration decl){ // TODO: get rid of this?
		typeof(return) r=[];
		foreach(ref prop;nestedDeclProp(decl))
			r~=iota(prop.componentReplacements.length).map!(i=>&prop.componentReplacements[i]).array;
		return r;
	}
	final DeclProp.ComponentReplacement* blockingComponentReplacement(Declaration decl){
		for(auto d=decl;d;d=d.splitFrom){
			auto blocking=componentReplacements(d).find!(crepl=>crepl.blocksAggregate);
			if(!blocking.empty) return blocking.front;
		}
		return null;
	}
	final bool blockedRedefinitionError(Declaration newDecl,Declaration oldDecl){
		auto blocking=blockingComponentReplacement(oldDecl);
		if(!blocking) return false;
		if(!oldDecl.isSemError()&&!newDecl.isSemError()){
			redefinitionError(newDecl,oldDecl);
			note("replaced component is here",blocking.location.loc);
		}
		newDecl.setSemError();
		return true;
	}
	static struct ComponentReplacementContext{
		private MapX!(Declaration,DeclProp.ComponentReplacement[]) componentReplacements;
		bool empty(){ return !componentReplacements.length; }
	}
	final ComponentReplacementContext moveLocalComponentReplacements(){ // TODO: get rid of this
		MapX!(Declaration,DeclProp.ComponentReplacement[]) r;
		foreach(decl,ref prop;declProps.props){
			r[decl]=prop.componentReplacements;
			prop.componentReplacements=[];
		}
		return typeof(return)(r);
	}
	final void isolateComponentReplacements(){ // TODO: this is a bit hacky
		foreach(decl,ref prop;declProps.props)
			prop.componentReplacements=prop.componentReplacements.dup;
	}
	final void restoreLocalComponentReplacements(ComponentReplacementContext previous){ // TODO: get rid of this
		foreach(decl,crepls;previous.componentReplacements)
			updateDeclProps(decl).componentReplacements=crepls;
	}
	Q!(Declaration,Identifier)[] pendingConsumptions;
	final ConsumedDecl recordConsumption(Declaration decl,Identifier use){
		if(allowMerge){
			if(use) pendingConsumptions~=q(decl,use);
			return null;
		}
		if(!use) return null;
		static if(language==silq){
			auto earlyForgotten=decl.earlyForgotten;
			decl.earlyForgotten=null;
			ConsumedDecl cd;
			auto earlyReturn=decl.forgottenBeforeEarlyReturn;
			if(earlyForgotten){
				cd=new IllegalConsumedDecl(decl,use,earlyForgotten);
			}else if(earlyReturn){
				cd=new EarlyReturnForgottenDecl(decl,use,earlyReturn);
			}else if(auto vd=cast(VarDecl)decl){
				if(vd.outOfScopeCause) cd=new OutOfScopeDecl(decl,use,vd.outOfScopeCause,vd.outOfScopeDup);
			}
			if(!cd) cd=new ConsumedDecl(decl,use);
		}else auto cd=new ConsumedDecl(decl,use);
		if(decl.rename){
			cd.rename=new Identifier(decl.rename.id);
			cd.rename.loc=decl.rename.loc;
		}
		cd.scope_=decl.scope_;
		cd.setSemCompleted();
		if(canInsert(cd.name.id))
			symtabInsert(cd);
		return cd;
	}
	final Identifier isConstThroughSplits(Declaration decl){
		for(auto d=decl;d;d=d.splitFrom)
			if(auto read=isConst(d))
				return read;
		return null;
	}
	final Declaration consume(Declaration decl,Identifier use,IndexExp consumedComponent=null,bool splitting=false){
		if(use&&!decl.isSemError&&!use.isSemError){
			if(auto read=isConstThroughSplits(decl)){
				if(!(consumedComponent&&componentConstBlocksAllow(decl,consumedComponent,use.loc))){
					if(!splitting){
						for(auto d=decl;d;d=d.splitFrom){
							foreach(prop;nestedDeclProp(d)){
								foreach(block;prop.constBlock)
									block.consumedDuringBorrow=true;
							}
						}
					}
					recordConstBlockedConsumption(read,use);
				}
			}
		}
		if(rnsymtab.get(decl.getId,null) !is decl) return null;
		if(cast(DeadDecl)decl) return null;
		Expression type;
		return consumeImpl(decl,decl,type,true,use,consumedComponent,splitting); // TODO: separate splitting and consuming
	}
	final bool canSplit(Declaration decl)in{
		if(!decl.isToplevelDeclaration()&&!decl.isSemError)
			assert(decl.scope_&&this.isNestedIn(decl.scope_));
	}do{
		if(decl.scope_ is this) return true;
		if(decl.isToplevelDeclaration()) return false;
		import ast.semantic_:typeConstBlocked;
		if(decl.isPinned||typeConstBlocked(decl,this)) return false;
		if(isConst(decl)){
			if(!canRecompute(decl)) return false;
			noteDependencyResolved(getDependency(decl));
		}
		return true;
	}
	final Declaration split(Declaration decl,Identifier use)in{
		if(!decl.isToplevelDeclaration()&&!decl.isSemError)
			assert(decl.scope_&&this.isNestedIn(decl.scope_),text(decl));
	}do{
		if(decl.scope_ is this) return decl;
		if(!canSplit(decl)) return decl;
		Expression type;
		auto result=consume(decl,use,null,true);
		if(!result) return decl;
		unconsume(result);
		return result;
	}
	final Declaration forkSplit(Declaration decl)in{ // (into sibling scopes that do not rejoin, e.g., the exit of a `do`-`while` loop: declarations whose types depend on `decl` are split as well)
		assert(decl.scope_&&this.isNestedIn(decl.scope_));
	}do{
		if(decl.scope_ is this) return decl;
		auto blocker=decl.typeConstBlocker;
		auto result=consume(decl,null,null,true);
		if(!result) return decl;
		unconsume(result);
		if(blocker) foreach(d;decl.splitInto) d.typeConstBlocker=blocker;
		return result;
	}
	final void unsplit(Declaration decl)in{
		assert(this is decl.scope_);
	}do{
		foreach(split;decl.splitInto){
			// assert(split !in split.scope_.lastUses.lastUses,text(split," ",split.scope_.lastUses.lastUses[split]));
			split.scope_.unsplit(split);
			if(split.scope_.consumedOuter.canFind(decl)){
				split.scope_.consumedOuter=split.scope_.consumedOuter.filter!(d=>d!is decl).array; // TODO: make more efficient
			}
			if(split.scope_.splitVars.canFind(split)){
				split.scope_.splitVars=split.scope_.splitVars.filter!(d=>d!is split).array; // TODO: make more efficient
			}
			if(split.scope_.forgottenVarsOnEntry.canFind(split)){
				split.scope_.forgottenVarsOnEntry=split.scope_.forgottenVarsOnEntry.filter!(d=>d!is split).array; // TODO: make more efficient
			}
			if(split.scope_.forgottenVars.canFind(split)){
				split.scope_.forgottenVars=split.scope_.forgottenVars.filter!(d=>d!is split).array; // TODO: make more efficient
			}
			if(split.scope_.mergedVars.canFind(split)){
				split.scope_.mergedVars=split.scope_.mergedVars.filter!(d=>d!is split).array; // TODO: make more efficient
				if(split.mergedInto&&split.mergedInto.scope_){
					split.mergedInto.scope_.unsplit(split.mergedInto);
					split.mergedInto.scope_.consume(split.mergedInto,null);
				}
			}
			split.scope_.consume(split,null);
		}
		decl.splitInto=[];
	}
	final void reinsert(Declaration decl){
		if(toRemove.canFind(decl))
			toRemove=toRemove.filter!(pdecl=>pdecl!is decl).array; // TODO: make more efficient
		symtabInsert(decl);
	}
	final void unconsume(Declaration decl)in{
		assert(decl.scope_ is null||decl.scope_ is this||decl.isSemError(),text(decl," ",decl.loc));
	}do{
		reinsert(decl);
		decl.scope_=this;
	}
	Declaration[] consumedOuter;
	Declaration[] splitVars;
	final void splitVar(Declaration splitFrom,Declaration splitInto){
		if(splitFrom.isSemError())
			splitInto.setSemForceError();
		assert(splitFrom.scope_ !is splitInto.scope_);
		splitFrom.splitInto~=splitInto;
		splitInto.splitFrom=splitFrom;
		splitVars~=splitInto;
	}
	final void resetSplits(Declaration decl){
		void rec(Declaration cdecl){
			foreach(split;cdecl.splitInto){
				replaceDecl(split,decl);
				rec(split);
			}
			cdecl.splitInto=[];
		}
		rec(decl);
	}
	final void replaceDecl(Declaration splitFrom,Declaration splitInto,bool nested=true)in{
		assert(splitFrom !is splitInto);
	}do{
		if(splitFrom.isSemError())
			splitInto.setSemForceError();
		if(nested) foreach(scopes;mergedNestedScopes){
			foreach(sc;scopes)
				sc.replaceDecl(splitFrom,splitInto);
		}
		if(dependencyTracked(splitFrom)){
			static if(language==silq) bool merge=dependencyTracked(splitInto); // (another version of the same variable, e.g., a capture that is also tracked through its declaration outside of the function)
			else enum merge=false;
			if(merge) dependencies.merge(splitFrom,splitInto);
			else replaceDependencies(splitFrom,splitInto);
		}
		declProps.replaceDecl(splitFrom,splitInto);
		foreach(ref oldDecl;forgottenVarsOnEntry){
			if(oldDecl is splitFrom)
				oldDecl=splitInto;
		}
		lastUses.replaceDecl(splitFrom,splitInto);
		void retype(Declaration d){
			if(d.scope_ !is this) return;
			retypeDeclaration(d,(Declaration m)=>m is splitFrom?splitInto:m);
		}
		foreach(_,d;rnsymtab) retype(d);
		foreach(d,ref prop;declProps.props) retype(d);
	}
	// (the types of the declarations of a scope mention the versions of the variables in that scope)
	private void retypeDeclaration(Declaration decl,scope Declaration delegate(Declaration) current){
		auto vd=cast(VarDecl)decl;
		if(!vd||!vd.vtype) return;
		MapSX!(Id,Declaration) meanings;
		MapSX!(Id,Expression) subst;
		foreach(id;vd.vtype.freeIdentifiers){
			if(!id.meaning) continue;
			if(auto m=meanings.get(id.id,null)){
				if(m !is id.meaning) subst.remove(id.id); // (different versions of the same name are not distinguished by substitution)
				continue;
			}
			meanings[id.id]=id.meaning;
			auto cur=current(id.meaning);
			if(cur is id.meaning) continue;
			import ast.semantic_: typeForDecl;
			auto nid=new Identifier(cur.getId);
			nid.meaning=cur;
			nid.scope_=this;
			nid.loc=id.loc;
			nid.type=typeForDecl(cur);
			nid.constLookup=true;
			nid.setSemCompleted();
			subst[id.id]=nid;
		}
		if(!subst.length) return;
		vd.vtype=vd.vtype.substitute(subst);
		updateType(vd);
	}

	final void updateType(Declaration decl){
		if(auto prop=declProps.tryGet(decl)){
			foreach(id;prop.accesses){
				if(auto ty=id.typeFromMeaning)
					id.type=ty;
			}
		}
	}

	protected Declaration consumeImpl(Declaration odecl,Declaration ndecl,ref Expression type,bool remove,Identifier use,IndexExp consumedComponent=null,bool splitting=false)in{
		assert(odecl is ndecl||!remove);
	}do{
		assert(odecl.scope_ is this&&ndecl.scope_ is this);
		if(rnsymtab.get(odecl.getId,null) !is odecl) return null;
		if(remove){
			symtabRemove(odecl);
			if(odecl !is ndecl)
				replaceDecl(odecl,ndecl);
			static if(language==silq) if(!splitting&&!dependencyTracked(ndecl)) addDefaultDependency(ndecl); // (consumed like a tracked declaration, such that its dependency is not tracked again afterwards)
			if(dependencyTracked(ndecl)){
				auto prevConsumingUse=consumingUse;
				consumingUse=use;
				scope(exit) consumingUse=prevConsumingUse;
				pushDependencies(ndecl,true,splitting?null:use);
			}
			recordConsumption(odecl,use);
		}else if(odecl !is ndecl){
			assert(odecl.name.id == ndecl.name.id);
			symtabRemove(odecl);
			symtabInsert(ndecl);
			replaceDecl(odecl,ndecl);
		}
		return ndecl;
	}
	private Declaration[] toRemove;
	private TrackedTemporary[] trackedTemporaries;
	final void pushUp(ref Dependency dependency,Declaration removed){
		static if(language==psi) return; // (in PSI, all data is classical: dependencies are not tracked)
		if(!dependencyTracked(removed)) return; // TODO: ideally can be removed
		dependency.replace(removed,dependencies.dependencies[removed]);
	}
	final void clearConsumed(){
		foreach(removed;toRemove)
			removeDependency(removed);
		toRemove=[];
	}

	final Declaration symtabLookup(Identifier ident,bool rnsym,DeadDecl[]* failures){
		return symtabLookup(ident.id,rnsym,failures);
	}
	protected final Declaration symtabLookup(Id id,bool rnsym,DeadDecl[]* failures){
		if(allowMerge) return null;
		auto r=rnsym?rnsymtab.get(id,null):symtab.get(id,null);
		if(auto dd=cast(DeadDecl)r){
			if(failures) *failures~=dd;
			r=null;
		}
		return r;
	}
	final Declaration peekSymtab(Id name,bool rnsym){
		return rnsym?rnsymtab.get(name,null):symtab.get(name,null);
	}

	final bool isConsumable(Identifier id,Declaration meaning=null,IndexExp consumedComponent=null)in{
		assert(id.isSemError||id.meaning||meaning);
	}do{
		if(!meaning) meaning=id.meaning;
		if(!meaning) return true;
		import ast.semantic_:typeConstBlocked;
		if(typeConstBlocked(meaning,this)) return false;
		if(canRecompute(meaning)) return true;
		static if(language==silq)
			if(consumedComponent&&componentConstBlocksAllow(meaning,consumedComponent,id.loc))
				return true; // consumption only affects components that are not borrowed
		if(isConst(meaning)) return false;
		if(meaning.isPinned) return false;
		return true;
	}
	static if(language==silq) final Scope letTypeBoundary(){ // (of the innermost `let` expression within a type that contains this scope in the same function)
		for(auto bs=cast(BlockScope)this;bs;bs=cast(BlockScope)bs.parent)
			if(bs.typeBoundary) return bs.typeBoundary;
		return null;
	}
	final bool checkConsumable(Identifier id,Declaration meaning=null,IndexExp consumedComponent=null)in{
		assert(id.isSemError||id.meaning||meaning);
	}do{
		if(!meaning) meaning=id.meaning;
		if(!meaning) return true;
		assert(!!meaning);
		if(meaning.isToplevelDeclaration()){
			if(!meaning.isSemError()){
				error(format("cannot consume top-level %s `%s`",meaning.kind,id), id.loc);
				note("declared here",meaning.loc);
				id.setSemForceError();
			}
			return false;
		}
		static if(language==silq) if(consumesOutsideType(meaning,letTypeBoundary())){ // (e.g., `forget(x)` in a `let` expression within a type)
			if(!id.isSemError()) error(format("cannot consume `%s` in a type",meaning.name),id.loc);
			id.setSemForceError();
			return false;
		}
		import ast.semantic_:typeConstBlocked,typeConstBlockNote;
		if(!meaning.isConst&&typeConstBlocked(meaning,this)){ // (`const` declarations cannot be consumed even if their type dependents can be uncomputed, see below)
			static if(language==silq){
				if(!meaning.typeConstBlocker&&tryUncomputeTypeDependents(meaning,id))
					return true;
			}
			if(!meaning.isSemError()){
				error(format("cannot consume `const` %s `%s`",meaning.kind,id), id.loc);
				meaning.setSemForceError();
			}
			typeConstBlockNote(meaning,this);
			id.setSemForceError();
			return false;
		}
		if(meaning.isConst){
			if(!meaning.isSemError()){
				error(format("cannot consume `const` %s `%s`",meaning.kind,id), id.loc);
				note("declared `const` here", meaning.loc);
				meaning.setSemForceError();
			}
			id.setSemForceError();
			return false;
		}
		if(auto read=isConst(meaning)){
			if(canRecompute(meaning))
				return true;
			static if(language==silq)
				if(consumedComponent&&componentConstBlocksAllow(meaning,consumedComponent,id.loc))
					return true; // consumption only affects components that are not borrowed
			if(!meaning.isSemError()){
				if(read !is id){
					error(format("cannot consume `const` %s `%s`",meaning.kind,id), id.loc);
					note(format("%s was made `const` here", meaning.kind), read.loc);
				}else{
					import ast.semantic_:nonLiftedError;
					nonLiftedError(id,this); // TODO: would be better to locate this around the enclosing `const` expression
				}
				meaning.setSemForceError();
			}
			id.setSemForceError();
			return false;
		}
		return true;
	}

	private Declaration postprocessLookup(Identifier id,Declaration meaning,Lookup kind){
		//imported!"util.io".writeln("POSTPROCESSING: ",id.loc," ",meaning," ",kind);
		static if(language==silq) enum performConsume=true;
		else auto performConsume=id.byRef&&!(meaning&&meaning.isAggregateMember()); // (fields are accessed through `this`)
		auto typeofSuppressedCapture=id.typeofSuppressedCapture;
		if(performConsume){
			if(!meaning) return meaning;
			if(kind==Lookup.consuming&&!typeofSuppressedCapture){
				bool doConsume=true;
				if(doConsume){
					if(!checkConsumable(id,meaning))
						doConsume=false;
					if(doConsume&&meaning.scope_){
						assert(!meaning.isPinned);
						if(auto nmeaning=consume(meaning,id))
							meaning=nmeaning;
					}
				}
			}
		}
		static if(language==silq) enum blocksConst=true;
		else auto blocksConst=!(meaning&&meaning.isAggregateMember()); // (fields are accessed through `this`)
		if(blocksConst&&kind==Lookup.constant&&meaning&&!meaning.isPinned&&!meaning.isToplevelDeclaration()&&!typeofSuppressedCapture)
			blockConst(meaning,id);
		if(kind!=Lookup.probing&&meaning&&!typeofSuppressedCapture){
			recordAccess(id,meaning);
		}
		return meaning;
	}

	final Declaration lookup(Identifier ident,bool rnsym,bool lookupImports,Lookup kind,DeadDecl[]* failures){
		auto meaning=lookupImpl(ident,rnsym,lookupImports,kind,this,failures);
		if(typeofOperand&&meaning&&kind!=Lookup.probing) meaning=typeofOperandUse(ident,meaning,kind,failures);
		return postprocessLookup(ident,meaning,kind);
	}
	private Declaration typeofOperandUse(Identifier ident,Declaration meaning,Lookup kind,DeadDecl[]* failures){ // (uses of values from outside the operand have no effect)
		if(ident.typeofSuppressedCapture||meaning.isToplevelDeclaration()||!meaning.scope_) return meaning;
		auto fsc=typeofFrame();
		if(!fsc||!fsc.isNestedIn(meaning.scope_)) return meaning; // (declared within the operand)
		ident.typeofSuppressedCapture=true;
		static if(language==silq) if(kind==Lookup.consuming&&consumesOutsideType(meaning,letTypeBoundary())){ // (as outside of the operand)
			error(format("cannot consume `%s` in a type",meaning.name),ident.loc);
			ident.setSemError();
			return meaning;
		}
		static if(language==silq) if(!fsc.simulateTypeofConsumption(ident,meaning,kind,this,failures)) return null;
		return meaning;
	}
	final Scope typeofFrame(){
		for(auto sc=this;sc;sc=sc.parentScope())
			if(sc.typeofConsumed.length) return sc;
		return null;
	}
	static if(language==silq)
	final bool simulateTypeofConsumption(Identifier ident,Declaration meaning,Lookup kind,Scope origin,DeadDecl[]* failures){
		auto uses=typeofConsumed[$-1].get(meaning,null);
		foreach(use;uses){
			if(origin.isNestedIn(use[1])){ // (consumed earlier in this `typeof` operand)
				if(failures) *failures~=new ConsumedDecl(meaning,use[0]);
				return false;
			}
		}
		if(kind==Lookup.consuming) typeofConsumed[$-1][meaning]=uses~q(ident,origin);
		return true;
	}
	Declaration lookupImpl(Identifier ident,bool rnsym,bool lookupImports,Lookup kind,Scope origin,DeadDecl[]* failures){
		return lookupHereImpl(ident,rnsym,failures);
	}
	Identifier getRenamed(Identifier cname){
		auto name=cname.id;
		bool takenByConsumed(){ // (by a consumed variable with a different name that was renamed to `cname`)
			for(Scope sc=this;sc;sc=sc.parentScope())
				if(auto dd=cast(DeadDecl)sc.peekSymtab(cname.id,true))
					if(dd.name.id!=name) return true;
			return false;
		}
		for(;;){ // TODO: quite hacky
			auto d=lookup(cname,true,true,Lookup.probing,null);
			import ast.semantic_: isBuiltIn;
			if(!d&&!isBuiltIn(cname)&&!takenByConsumed()) break;
			auto loc=cname.loc;
			cname=new Identifier(cname.id.apos);
			cname.loc=loc;
		}
		return cname;
	}
	protected final void rename(Declaration decl){
		auto cname=decl.rename?decl.rename:decl.name;
		decl.rename=getRenamed(cname);
	}
	final Declaration lookupHere(Identifier ident,bool rnsym,Lookup kind,DeadDecl[]* failures){
		auto meaning=lookupHereImpl(ident,rnsym,failures);
		return postprocessLookup(ident,meaning,kind);
	}
	final Declaration lookupHereImpl(Identifier ident,bool rnsym,DeadDecl[]* failures){
		auto r=symtabLookup(ident,rnsym,failures);
		if(auto fd=cast(FunctionDef)r){
			import ast.semantic_:isInDataScope;
			if(auto asc=isInDataScope(fd.scope_))
				if(fd.name.id==asc.decl.name.id)
					r=asc.decl;
		}
		return r;
	}

	bool isNestedIn(Scope rhs){ return rhs is this; }

	void error(lazy string err, Location loc){handler.error(err,loc);}
	void note(lazy string err, Location loc){handler.note(err,loc);}
	void message(lazy string msg, Location loc){handler.message(msg,loc);}

	final bool close(T)(T loc)if(is(T==Scope)||is(T==ReturnExp)){
		import ast.semantic_: unrealizable,typeConstBlocked;
		bool errors=false;
		Declaration[] pending,hidden; // (`hidden`: splits forgotten here, which do not block the variables that their types mention; still visible to the code after a return)
		foreach(_,d;rnsymtab) pending~=d;
		for(bool deferBlocked=true;pending.length;){
			Declaration[] blocked; // (forgotten after the live variables whose types mention them, e.g., `n` after `y:=vector(n,0:!𝔹)`)
			bool forgot=false;
			foreach(d;pending){
				if(cast(DeadDecl)d) continue;
				if(d.isSemError()) continue;
				if(rnsymtab.get(d.getId,null) !is d) continue;
				//if(d.scope_ !is this && !d.isLinear()) continue;
				//imported!"util.io".writeln("REMOVING: ",d," ",getDependency(d)," ",canSplit(d)," ",canForget(d)," ",lastUses.canForget(d,true,false)," ",rnsymtab," ",isConst(d)," ",lastUses.lastUses);
				if(d.scope_.getFunction() !is getFunction()) continue;
				//d=split(d,null);
				//assert(d.scope_ is this);
				if(auto vd=cast(VarDecl)d) if(!vd.vtype||unrealizable(vd.vtype)) {
					d.setSemForceError();
					continue;
				}
				if(!canForgetAppend(loc,d)){
					if(deferBlocked&&typeConstBlocked(d,this)){
						blocked~=d;
						continue;
					}
					if(!d.isSemError()){
						bool done=false;
						if(!canSplit(d)){
							if(auto read=isConst(d)){
								error(format("cannot forget `const` variable `%s`",d), d.loc);
								note("variable was made `const` here", read.loc);
								errors=true;
								done=true;
							}else continue; // TODO: catch this early
						}
						if(!done) done=lastUses.betterUnforgettableError(d,this);
						if(!done){
							if(cast(Parameter)d) error(format("%s `%s` is not consumed (perhaps return it or annotate it `const`)",d.kind,d.getName),d.loc);
							else error(format("%s `%s` is not consumed (perhaps return it)",d.kind,d.getName),d.loc);
							explainUnforgettable(d);
							errors=true;
							done=true;
						}
						d.setSemForceError();
					}else symtabRemove(d);
					static if(is(typeof(loc):Expression)) loc.setSemForceError();
				}else{
					forgot=true;
					if(auto split=rnsymtab.get(d.getId,null)) for(auto s=split.splitFrom;s;s=s.splitFrom) if(s is d){ symtabRemove(split); hidden~=split; break; }
					Identifier use=null;
					if(isConst(d)){
						use=new Identifier(d.getName);
						use.constLookup=false;
						static if(is(T==Scope)) use.loc=d.loc;
						else use.loc=loc.loc;
						use.sstate=SemState.completed;
					}
					consume(d,use);
					clearConsumed();
				}
			}
			pending=blocked;
			deferBlocked=forgot;
		}
		foreach(split;hidden) symtabInsert(split);
		return errors;
	}

	final bool close(){
		return Scope.close(this);
	}

	bool diverges=false;
	final bool closeUnreachable(Scope mergeScope,Scope consumptionScope=null){
		clearConsumed();
		activeNestedScopes=[];
		allowMerge=false;
		diverges=true;
		if(!consumptionScope) consumptionScope=mergeScope;
		foreach(_,d;rnsymtab.dup){
			if(cast(DeadDecl)d) continue;
			if(d.isLinear()&&(!consumptionScope||!d.scope_||d.scope_.isNestedIn(consumptionScope))||d.scope_ is this){ // (variables of scopes that enclose the merge are not split into the branch, e.g., through the scope of a `let` expression)
				if(auto p=cast(Parameter)d) if(p.isConst) continue;
				consume(d,null);
				clearConsumed();
			}else symtabRemove(d);
		}
		if(mergeScope)
			mergeScope.mergeDeclProps(this.declProps,this.componentConstBlocks);
		return false;
	}

	// TODO: clean up
	private DummyWitnessContext[] dummyWitnessContexts_; // populated on the root scope only
	final ref DummyWitnessContext[] dummyWitnessContexts(){
		if(auto p=parentScope()) return p.dummyWitnessContexts;
		return dummyWitnessContexts_;
	}
	final void pushDummyWitnessContext(MapX!(Declaration,Declaration) dummies){
		dummyWitnessContexts~=DummyWitnessContext(dummies);
	}
	final DummyWitnessContext popDummyWitnessContext()in{
		assert(dummyWitnessContexts.length);
	}do{
		auto result=dummyWitnessContexts[$-1];
		dummyWitnessContexts=dummyWitnessContexts[0..$-1];
		return result;
	}
	final bool dummyWitnessActive(){ return dummyWitnessContexts.length!=0; }
	final void noteDependencyResolved(Dependency dep){
		if(dep.isTop||!dummyWitnessActive) return;
		foreach(ref context;dummyWitnessContexts){
			foreach(v,vprime;context.dummies)
				if(vprime in dep.dependencies)
					context.results[v]=v;
		}
	}
	final void noteDependencyConsumed(Declaration decl,Dependency dep){
		if(!dummyWitnessActive) return;
		foreach(ref context;dummyWitnessContexts)
			if(decl !in context.consumedDeps)
				context.consumedDeps[decl]=dep.dup;
	}
	final Dependency expandDependency(Dependency dep){
		if(dep.isTop) return dep;
		SetX!Declaration seen;
		Declaration[] worklist;
		foreach(x;dep.dependencies) worklist~=x;
		while(worklist.length){
			auto decl=worklist[$-1];
			worklist=worklist[0..$-1];
			if(decl in seen) continue;
			seen.insert(decl);
			if(!dependencyTracked(decl)) continue;
			auto d=dependencies.dependencies[decl];
			if(!d.isTop) foreach(x;d.dependencies) worklist~=x;
		}
		auto all=Dependency(false);
		foreach(x;seen) all.dependencies.insert(x);
		return all;
	}
	final void noteReconstructed(Dependency dep){
		if(dep.isTop||!dummyWitnessActive) return;
		foreach(ref context;dummyWitnessContexts)
			context.reconstructed~=dep.dup;
	}
	final void noteNestedLoopCarried(SetX!Id ids){
		if(!dummyWitnessActive||!ids.length) return;
		foreach(ref context;dummyWitnessContexts)
			context.nestedLoopCarried~=ids;
	}

	auto controlDependency=Dependency(false,SetX!Declaration.init);
	bool quantumControlled=false;
	void addControlDependency(Dependency dep){
		controlDependency.joinWith(dep);
		quantumControlled=true;
	}

	static Dependency getDefaultDependency(Declaration decl){
		return Dependency(!decl.isSemError()&&decl.isLinear);
	}
	void addDefaultDependency(Declaration decl)in{
		static if(language==silq) assert(!dependencyTracked(decl));
	}do{
		addDependency(decl,getDefaultDependency(decl));
		//foreach(ddecl,ref dep;dependencies.dependencies) imported!"util.io".writeln(ddecl," ",cast(void*)ddecl);
		//imported!"util.io".writeln("ADDED DEFAULT: ",decl," ",dependencies," ",cast(void*)decl);
		//imported!"util.io".writeln(dependencies.getIds());
		//assert(decl.getName!="rrr");
	}

	void addDependency(Declaration decl, Dependency dep){
		addDependencies([q(decl,dep)]);
	}
	void removeDependency(Declaration decl){
		//imported!"util.io".writeln("REMOVING: ",decl," ",cast(void*)decl);
		static int counter=0;
		dependencies.dependencies.remove(decl);
	}
	void addDependencies(scope Q!(Declaration,Dependency)[] deps,bool sourcesTracked=false){
		static if(language==psi) return; // (in PSI, all data is classical: dependencies are not tracked)
		//imported!"util.io".writeln("ADDING: ",deps);
		foreach(i,ref dep;deps){
			assert(!!dep[0]);
			substituteConsumed(dep[1],consumedDepLog);
			if(dep[0] in dependencies.dependencies){
				//writeln(dep[0]," ",toRemove," ",dependencies)
				dep[1].remove(dep[0]); // (its previous value is joined, e.g., a replaced component computed from other components)
				dep[1].joinWith(dependencies.dependencies[dep[0]]);
				if(!sourcesTracked) dep[0].definitionSources=DefinitionSources.init;
			}
		}
		foreach(decl,dep;deps.map!(x=>x)){
			assert(decl&&!cast(DeadDecl)decl);
			dependencies.dependencies[decl]=dep;
		}
	}
	final bool dependencyTracked(Declaration decl){
		static if(language==psi) return true; // (in PSI, all data is classical: dependencies are not tracked)
		return !!(decl in dependencies.dependencies);
	}
	final Scope dependencyScope(Declaration decl){ // (the dependencies of a merged scope are those of the scope it was merged into, e.g., for its last uses)
		for(Scope sc=this;sc&&sc.dependenciesMerged;sc=sc.parentScope())
			if(sc.parentScope()&&sc.parentScope().dependencyTracked(decl)) return sc.parentScope();
		return this;
	}
	final Declaration trackingDecl(Declaration decl){ // (a variable of an enclosing function is tracked through its declaration outside of the function, as in `dependencyDecl`)
		while(decl.splitFrom&&decl.scope_&&decl.scope_.getFunction()!is getFunction())
			decl=decl.splitFrom;
		return decl;
	}
	final Dependency getDependency(Identifier id)in{
		assert(id.isSemCompleted()||id.isSemError());
		assert(!!id.meaning);
	}do{
		return getDependency(id.meaning);
	}
	final Dependency getDependency(Declaration decl,bool pushed=false)in{
		assert(decl.isSemCompleted()||decl.isSemError()||cast(FunctionDef)decl||cast(Parameter)decl,text(decl," ",decl.sstate));
	}do{
		static if(language==psi) return Dependency(false); // (in PSI, all data is classical: dependencies are not tracked)
		if(!dependencyTracked(decl)){
			if(auto dsc=dependencyScope(decl)) if(dsc !is this) return dsc.dependencies.dependencies[decl];
			auto cur=rnsymtab.get(decl.getId,null);
			if(cur&&cur !is decl&&!cast(DeadDecl)cur) return getDefaultDependency(decl);
			static if(language==silq) if(cast(DeadDecl)cur){ // (the variable was consumed here: its dependency is not tracked again)
				if(auto pd=consumedDepLog.getPtr(decl)) return pd.dup;
				return getDefaultDependency(decl);
			}
			addDefaultDependency(decl); // TODO: ideally can be removed
		}
		return dependencies.dependencies[decl];
	}
	final void replaceDependencies(Declaration decl,Declaration rhs){
		static if(language==psi) return; // (in PSI, all data is classical: dependencies are not tracked)
		dependencies.replace(decl,rhs);
	}
	final void substituteDependency(Declaration decl,Dependency dep){
		static if(language==psi) return; // (in PSI, all data is classical: dependencies are not tracked)
		dependencies.substitute(decl,dep);
		lastUses.substituteDependency(decl,dep);
	}
	MapSX!(Declaration,Dependency) consumedDepLog; // dependency each declaration consumed in this scope had at its consumption
	static void substituteConsumed(ref Dependency dep,ref MapSX!(Declaration,Dependency) consumedDepLog){
		if(dep.isTop) return;
		SetX!Declaration substituted; // stale sets can mention consumed declarations in cycles
		for(bool changed=true;changed;){
			changed=false;
			foreach(m;dep.dependencies){
				if(m in substituted) continue;
				if(auto pd = consumedDepLog.getPtr(m)){
					substituted[m]=[];
					dep.replace(m,*pd);
					changed=true;
					break;
				}
			}
			if(dep.isTop) break;
		}
	}
	Identifier consumingUse;
	final void pushDependencies(Declaration decl,bool keep,Identifier consumedAt=null){
		static if(language==psi) return; // (in PSI, all data is classical: dependencies are not tracked)
		consumedDepLog[decl]=getDependency(decl).dup;
		noteDependencyConsumed(decl,getDependency(decl));
		if(getDependency(decl).isTop){
			bool done=false;
			do{ // TODO: improve
				done=true;
				foreach(ndecl;dependencies.dependencies.keys.array){
					auto v=getDependency(ndecl);
					//imported!"util.io".writeln("CHECKING: ",decl," ",ndecl," ",v.dependencies," ",decl in v.dependencies);
					if(decl in v.dependencies){
						if(auto lu=lastUses.get(ndecl,true)){
							while(lu.forwardTo) lu=lu.forwardTo;
							//imported!"util.io".writeln("CHECKING PUSH: ",lu," ",lu.use?lu.use.implicitDup:false);
							if(lu.canCancelImplicitDup()){
								if(consumingUse) if(auto vd=cast(VarDecl)ndecl) if(!vd.outOfScopeCause){
									vd.outOfScopeCause=consumingUse;
									if(!isConstLocal(vd)&&lu.kind==LastUse.Kind.constUse&&lu.prevImplicitDup)
										vd.outOfScopeDup=lu.prevImplicitDup.use;
								}
								if(lu.cancelImplicitDup()){
									assert(lu.isConsumption(),text(lu));
									done=false;
								}else{
									// TODO
								}
							}
						}
					}
				}
			}while(!done);
		}
		dependencies.pushUp(decl,keep,consumedAt);
		if(keep) toRemove~=decl;
		this.pushUp(controlDependency,decl);
		pushTrackedTemporaryDependencies(decl);
	}

	bool canForget(Declaration decl,bool forceHere=false){
		if(decl.isSemError()) return true;
		import ast.semantic_:typeForDecl;
		auto type=typeForDecl(decl);
		if(type&&type.isClassical) return true; // TODO: ensure classical variables have dependency `{}` instead?
		if(decl.isToplevelDeclaration()) return true;
		assert(decl.isSemCompleted()||cast(FunctionDef)decl&&type,text(decl," ",decl.sstate," ",type));
		auto dsc=dependencyScope(decl);
		if(!dsc.dependencyTracked(decl)){
			if(decl.scope_&&decl.scope_.getFunction() !is getFunction()) // (a declaration of an enclosing function is tracked through its capture)
				return !forceHere&&lastUses.canForget(decl,true,false)||!getDefaultDependency(decl).isTop;
			addDefaultDependency(decl); // TODO: ideally can be removed
		}
		return !forceHere&&lastUses.canForget(decl,true,false)||dsc.dependencies.canForget(decl);
	}
	final bool canRecompute(Declaration decl){
		if(decl.isSemError()) return false;
		return canForget(decl,true);
	}

	Declaration[] forgottenVarsOnEntry;
	final Declaration forgetOnEntry(Declaration decl)in{
		assert(canSplit(decl));
	}do{
		decl=split(decl,null);
		forgottenVarsOnEntry~=decl;
		return decl;
	}
	Declaration[] forgottenVars;
	final bool canForgetAppend(T)(T cause,Declaration decl)if(is(T==Scope)||is(T==ReturnExp))in{
		//assert(decl.scope_ is this,text(decl," ",decl.scope_," ",typeid(decl)));
	}do{
		if(cast(DeadDecl)decl) return true;
		static if(is(T==ReturnExp)) auto earlyReturn=cause;
		else ReturnExp earlyReturn=null;
		bool atLoopGuard(){ // (a classical variable stays available on the path that exits the loop)
			import ast.semantic_:typeForDecl;
			auto type=typeForDecl(decl);
			if(!type||!type.isClassical()) return false;
			for(auto lu=lastUses.get(decl,true);lu;lu=lu.forwardTo?lu.forwardTo:lu.splitFrom)
				if(lu.loopGuard) return true;
			return false;
		}
		if(lastUses.canForget(decl,true,false,earlyReturn)&&!(earlyReturn&&atLoopGuard())){
			lastUses.forget(decl,false,earlyReturn);
			return true;
		}
		if(!canSplit(decl)) return false;
		if(canForget(decl)){
			decl=split(decl,null);
			assert(decl.scope_ is this);
			if(cause.forgottenVars.canFind(decl)) return true; // (e.g., `const` locals are forgotten before merging)
			cause.forgottenVars~=decl;
			static if(is(T:Expression)) lastUses.synthesizedForget(decl,null,this,cause);
			else lastUses.synthesizedForget(decl,null,this,null);
			return true;
		}
		return false;
	}
	final bool canForgetAppend(Declaration decl){
		return canForgetAppend(this,decl);
	}
	final void explainUnknownDependency(Declaration decl,Dependency dep){
		if(!dep.isTop||!dep.lostVar||!dep.lostAt||dep.lostVar.getId==decl.getId) return;
		note(format("`%s` depends on `%s`, which is consumed here",decl.getName,dep.lostVar.getName),dep.lostAt.loc);
		if(dep.lostAt.sstate==SemState.started) dep.lostAt.setSemError(); // (being looked up: no additional note that the lookup caused the error)
	}
	final void explainUnforgettable(Declaration decl){
		if(auto lu=lastUses.get(decl,true)){
			while(lu.forwardTo) lu=lu.forwardTo;
			if(lu.dep.isTop&&lu.dep.lostVar) return explainUnknownDependency(decl,lu.dep);
		}
		if(dependencyTracked(decl)) explainUnknownDependency(decl,getDependency(decl));
	}
	static if(language==silq)
	final bool tryUncomputeTypeDependents(Declaration decl,Identifier use,string action="consume"){
		import ast.semantic_:liveTypeDependents,typeConstBlocked;
		if(allowMerge) return false;
		auto dependents=liveTypeDependents(decl,rnsymtab);
		if(!dependents.length) return false;
		foreach(d;dependents)
			if(!lastUses.canForget(d,true,false))
				return false;
		foreach(d;dependents)
			for(auto s=cast(NestedScope)this;s&&!cast(FunctionScope)s;s=cast(NestedScope)s.parent)
				if(auto bs=cast(BlockScope)s) if(bs.isLoopReset){
					if(!d.scope_||!d.scope_.isNestedIn(bs.parent)) return false; // (the exit of a `do`-`while` loop follows the resets of the earlier iterations: a variable from outside the loop would have to be forgotten before it)
					break;
				}
		EarlyForgottenDecl firstEFD=null;
		foreach(d;dependents){
			lastUses.forget(d,false);
			auto ed=new EarlyForgottenDecl(d,decl,use);
			ed.action=action;
			if(!firstEFD) firstEFD=ed;
			else ed.reportVia=firstEFD;
			if(d.rename){
				ed.rename=new Identifier(d.rename.id);
				ed.rename.loc=d.rename.loc;
			}
			ed.setSemCompleted();
			if(auto dsc=d.scope_)
				dsc.consume(d,null); // remove from the home scope, if still there
			if(rnsymtab.get(d.getId,null) is d){
				symtabRemove(d);
				if(dependencyTracked(d))
					pushDependencies(d,false);
			}
			ed.scope_=this;
			if(canInsert(ed.name.id))
				symtabInsert(ed);
		}
		auto result=!typeConstBlocked(decl,this);
		if(result) decl.earlyForgotten=firstEFD;
		return result;
	}
	Declaration[] mergedVars;
	Declaration[] producedOuter;
	final void mergeVar(Declaration mergedFrom,Declaration mergedInto){
		if(mergedFrom.isSemError())
			mergedInto.setSemForceError();
		mergedInto.mergedFrom~=mergedFrom;
		mergedFrom.mergedInto=mergedInto;
		mergedInto.resetCanonicalSource();
		mergedVars~=mergedFrom;
	}

	bool allowMerge=false;
	NestedScope[] activeNestedScopes;
	void nest(NestedScope r)in{
		static if(language==silq) assert(allowsLinear());
		assert(r.parent is this);
	}do{
		r.controlDependency.joinWith(controlDependency); // TODO: replace
		r.quantumControlled|=quantumControlled;
		r.dependencies=dependencies.dup;
		r.symtab=symtab.dup;
		r.rnsymtab=rnsymtab.dup;
		if(!allowMerge) lastUses.prepareNesting(this);
		allowMerge=true;
		activeNestedScopes~=r;
		lastUses.nest(r);
	}

	NestedScope[][] mergedNestedScopes;

	final bool merge(bool quantumControl,NestedScope[] scopes...)in{
		assert(scopes.length);
	}do{
		return merge(quantumControl,false,scopes);
	}
	final bool mergeLoop(bool returns,NestedScope forgetScope,NestedScope loopScope)in{
		assert(equal(activeNestedScopes,only(forgetScope,loopScope)));
	}do{
		if(returns) loopScope.closeUnreachable(this);
		return merge(false,!returns,forgetScope,loopScope);
	}
	final bool mergeLoopExit(BlockScope exitScope)in{ // (the exit scope is nested in the loop scope of the last iteration)
		assert(activeNestedScopes.empty);
		assert(exitScope.isNestedIn(this)&&exitScope !is this);
	}do{
		activeNestedScopes=[exitScope];
		return merge(false,exitScope);
	}

	bool merge(bool quantumControl,bool isLoop,NestedScope[] scopes...)in{
		assert(scopes.length);
		//debug assert(allowMerge);
	}do{
		// scope(exit) writeln("MERGING\n",this,"\n",scopes.map!(sc=>text("nested: ",sc,"\nconsumed: ",sc.consumedOuter,"\nsplit: ",sc.splitVars,"\nmergedVars: ",sc.mergedVars,"\nproducedOuter: ",producedOuter)).join("\n"),"\nEND MERGE\n");
		// imported!"util.io".writeln("MERGING: ",scopes.map!(sc=>sc.rnsymtab));
		// imported!"util.io".writeln("MERGING: ",scopes.map!(sc=>sc.dependencies));
		if(!allowsLinear()){
			assert(activeNestedScopes.empty);
			return false; // (no nesting, so no merge)
		}
		clearConsumed(); // TODO: why needed?
		foreach(sc;scopes) sc.clearConsumed();
		assert(scopes==activeNestedScopes,text(scopes," ",activeNestedScopes));
		foreach(sc;scopes){
			sc.siblingScopes=activeNestedScopes;
			sc.siblingsFinal=true;
		}
		mergedNestedScopes~=activeNestedScopes;
		activeNestedScopes=[];
		allowMerge=false;
		static if(language==silq) foreach(sc;scopes){ // (released after the enclosing statement, e.g., for branches of an `if` expression whose types mention variables)
			typeConstBlockLog~=sc.typeConstBlockLog;
			sc.typeConstBlockLog=[];
		}
		scope(exit){
			auto pending=pendingConsumptions;
			pendingConsumptions=[];
			foreach(p;pending)
				if(!symtabLookup(p[0].getId,false,null)&&!rnsymtab.get(p[0].getId,null))
					recordConsumption(p[0],p[1]);
		}
		if(scopes.any!(sc=>sc.diverges))
			scopes=scopes.filter!(sc=>!sc.diverges).array;
		if(!scopes.length) return false;
		SetX!Declaration goneConstLocals; // (the types of the merged variables do not mention them)
		static if(language==silq){
			foreach(sc;scopes){
				if(auto bsc=cast(BlockScope)sc) if(bsc.keepConstLocals) continue;
				foreach(_,d;sc.rnsymtab.dup){
					if(cast(DeadDecl)d||d.isSemError()||!isConstLocal(d)) continue;
					if(sc.rnsymtab.get(d.getId,null) !is d) continue;
					auto origin=d;
					while(origin.splitFrom) origin=origin.splitFrom;
					if(!origin.scope_||!origin.scope_.isNestedIn(sc)) continue;
					if(!sc.canForgetAppend(d)){
						if(!sc.lastUses.betterUnforgettableError(d,sc))
							sc.error(format("`const` variable `%s` cannot be forgotten at the end of its scope",d.getName),d.loc);
						d.setSemForceError();
					}else{
						sc.consume(d,null); // (not merged, e.g., with a variable of the same name in another branch)
						sc.clearConsumed();
						for(auto x=d;x;x=x.splitFrom) goneConstLocals.insert(x);
					}
				}
			}
		}
		symtab=scopes[0].symtab.dup;
		rnsymtab=scopes[0].rnsymtab.dup;
		//imported!"util.io".writeln("TO REMOVE: ",toRemove," DEPS: ",dependencies," ",toRemove.map!(t=>!!(t in dependencies.dependencies)));
		MapX!(Declaration,Dependency) carryOverDependencies;
		static if(language==silq) foreach(decl;toRemove) if(dependencyTracked(decl)) carryOverDependencies[decl]=getDependency(decl); // TODO: this is a bit hacky
		dependencies=scopes[0].dependencies.dup;
		auto nestedControlDependency=scopes[0].controlDependency.dup;
		bool errors=false;
		bool consumedByError(Id id){ // (by an erroneous expression in a branch: not reported again)
			foreach(sc;scopes) if(auto cd=cast(ConsumedDecl)sc.rnsymtab.get(id,null)) if(cd.use.erroneousUse) return true;
			return false;
		}
		MapSX!(Id,DeadMerge) deadMerges;
		DeadMerge addDeadMerge(Declaration sym){
			if(auto dm = deadMerges.getPtr(sym.name.id))
				return *dm;
			auto dm=new DeadMerge(sym.name);
			if(sym.rename){
				dm.rename=new Identifier(sym.rename.id);
				dm.rename.loc=sym.rename.loc;
			}
			dm.scope_=this;
			dm.quantumControl=quantumControl;
			dm.numBranches=scopes.length;
			dm.loc=sym.loc;
			dm.setSemCompleted();
			deadMerges[sym.name.id]=dm;
			return dm;
		}
		MapSX!(Id,Expression) mergeTypeSubst;
		auto numProducedOuter=producedOuter.length;
		Declaration goneMention(Expression type){ // (a `const` local of a branch that `type` mentions)
			if(type&&goneConstLocals.length)
				foreach(id;type.freeIdentifiers) if(id.meaning&&id.meaning in goneConstLocals) return id.meaning;
			return null;
		}
		Expression visibleType(Expression type){ // (a supertype of `type` that does not mention the `const` locals of the branches, as the join with a type in another branch, or `null`)
			return goneConstLocals.length?eliminateVariables(type,(Declaration d)=>!!(d in goneConstLocals)):type;
		}
		foreach(psym;rnsymtab.dup){
			auto sym=psym;
			import ast.semantic_: typeForDecl;
			bool symExists=true,needMerge=sym.scope_ is scopes[0];
			void removeOSym(Scope sc,Declaration osym){
				if(sc !is this)
					if(auto dm = deadMerges.getPtr(osym.name.id))
						dm.mergedFrom~=osym;
				if(sc.rnsymtab.get(osym.getId,null) is osym)
					sc.symtabRemove(osym);
				if(sc.dependencyTracked(osym))
					sc.pushDependencies(osym,false);
			}
			void splitSym(){
				auto nsym=scopes[0].split(sym,null);
				if(nsym is sym) return;
				pushUp(nestedControlDependency,sym); // TODO: needed?
				if(rnsymtab.get(sym.getId,null) is sym) symtabRemove(sym); // (otherwise already consumed by the split, after an error in another branch)
				symtabInsert(nsym);
				sym=nsym;
			}
			void removeSym(){
				addDeadMerge(sym);
				removeOSym(this,sym);
				removeOSym(scopes[0],psym);
				pushUp(nestedControlDependency,psym); // TODO: needed?
				symExists=false;
			}
			void promoteSym(Expression ntype){
				symtabRemove(sym);
				auto var=addVariable(sym,ntype,true);
				if(!dependencyTracked(sym))
					addDefaultDependency(sym); // TODO: ideally can be removed
				//dependencies.replace(sym,var); // reverse-inherit dependencies
				pushUp(nestedControlDependency,sym); // TODO: needed?
				auto dep=getDependency(sym);
				dep.joinWith(nestedControlDependency);
				addDependency(var,dep);
				pushDependencies(sym,false);
				if(sym.isSemError())
					var.setSemForceError();
				sym=var;
				needMerge=true;
			}
			if(cast(DeadDecl)sym){
				removeOSym(this,sym);
				continue;
			}
			auto cur=scopes[0].rnsymtab.get(sym.getId,null);
			if(!cur||cast(DeadDecl)cur){ // (consumed when merging the dependencies of another variable)
				removeOSym(this,sym);
				continue;
			}
			foreach(sc;scopes[1..$]){
				auto osym=sc.rnsymtab.get(sym.getId,null);
				if(!osym||cast(DeadDecl)osym){
					splitSym();
					if(!scopes[0].canForgetAppend(sym)&&!consumedByError(sym.getId)){
						error(format("variable `%s` is not consumed", sym.getName), sym.loc);
						scopes[0].explainUnforgettable(sym);
						errors=true;
					}
					removeSym();
				}else{
					if(sym!=osym){
						auto ot=typeForDecl(osym),st=typeForDecl(sym);
						if(!ot) ot=st;
						if(!st) st=ot;
						if(mergeTypeSubst.length){ // compare types after, not before, merging the variables they mention
							if(ot) ot=ot.substitute(mergeTypeSubst);
							if(st) st=st.substitute(mergeTypeSubst);
						}
						bool trivialSplit=sym.canonicalSource is osym.canonicalSource;
						if(ot&&st){
							if(quantumControl&&!trivialSplit){ // automatically promote to quantum if possible
								if(auto qt=ot.getQuantum)
									ot=qt;
							}
							auto nt=ot&&st?joinTypes(ot,st):null;
							if(!nt||quantumControl&&!trivialSplit&&nt.hasClassicalComponent()){
								splitSym(), sc.split(osym,null);
								if(sym.isSemCompleted()&&osym.isSemCompleted()){
									auto symOk=scopes[0].canForgetAppend(sym),osymOk=sc.canForgetAppend(osym);
									if(!symOk||!osymOk){
										error(format("variable `%s` is not consumed", sym.getName), sym.loc);
										if(!nt) note(format("declared with incompatible types `%s` and `%s` in different branches",ot,st), osym.loc);
										else if(!symOk) scopes[0].explainUnforgettable(sym);
										else sc.explainUnforgettable(osym);
										errors=true;
									}
								}
								removeSym();
								removeOSym(sc,osym);
							}else{
								auto vt=visibleType(nt);
								promoteSym(vt?vt:nt);
							}
						}
					}
				}
			}
			if(symExists&&needMerge&&sym.scope_ is scopes[0]){
				auto type=typeForDecl(sym);
				if(auto gone=goneMention(type)) if(!visibleType(type)){ // (not merged, as for incompatible types on different paths)
					splitSym();
					if(!scopes[0].canForgetAppend(sym)&&!consumedByError(sym.getId)){
						error(format("variable `%s` is not consumed", sym.getName), sym.loc);
						scopes[0].explainUnforgettable(sym);
						note(format("its type `%s` mentions `const` variable `%s`, which is not visible after its block",type,gone.getName),gone.loc);
						errors=true;
					}
					removeSym();
					deadMerges[sym.name.id].goneMention=gone;
				}
			}
			if(symExists&&needMerge){
				if(auto ntype=typeForDecl(sym)){
					if(sym.scope_ is scopes[0]) promoteSym(visibleType(ntype));
					auto sources=DefinitionSources.empty;
					if(nestedControlDependency.isTop) sources=DefinitionSources.init;
					else foreach(d;nestedControlDependency.dependencies) sources.reads.insert(d);
					scope(success) sym.definitionSources=sources;
					foreach(sc;scopes){
						assert(sym.getId in sc.rnsymtab);
						auto osym=sc.rnsymtab[sym.getId];
						if(cast(DeadDecl)osym){ // TODO: why needed?
							removeSym();
							break;
						}
						sc.mergeVar(osym,sym);
						if(sources.known) sources.consume(osym,sc.dependencyTracked(osym)?sc.getDependency(osym):Dependency(true));
						if(osym.loc.rep.ptr>sym.loc.rep.ptr) sym.loc=osym.loc; // TODO: this is a bit hacky
						//imported!"util.io".writeln("MAKING MERGE: ",osym," ",sym," ",cast(void*)osym," ",cast(void*)sym);
						if(!sc.dependencyTracked(osym))
							sc.addDefaultDependency(osym); // TODO: ideally can be removed
						//sc.dependencies.replace(osym,sym); // reverse-inherit dependencies
						auto dep=sc.getDependency(osym);
						// dep.joinWith(sc.controlDependency); // TODO
						dep.joinWith(nestedControlDependency);
						sc.addDependency(sym,dep);
						sc.pushDependencies(osym,false);
					}
					if(!cast(DeadDecl)sym){
						if(auto mtype=typeForDecl(sym)){
							auto nid=new Identifier(sym.getId);
							nid.meaning=sym;
							nid.scope_=this;
							nid.loc=sym.loc;
							nid.type=mtype;
							nid.constLookup=true;
							nid.setSemCompleted();
							mergeTypeSubst[sym.getId]=nid;
						}
					}
				}else{
					//auto dep=sym.scope_.getDependency(sym);
					sym.scope_=this;
					//addDependency(sym,dep);
				}
				if(symExists) producedOuter~=sym;
			}
		}
		if(mergeTypeSubst.length) foreach(sym;producedOuter[numProducedOuter..$]){ // (the types of the merged variables mention the merged versions, independently of the order of merging)
			auto vd=cast(VarDecl)sym;
			if(vd&&vd.vtype&&vd.scope_ is this) vd.vtype=vd.vtype.substitute(mergeTypeSubst);
		}
		for(bool changed=true;changed;){ // (consumed in a branch when merging the dependencies of another variable, after it was merged)
			changed=false;
			foreach(sym;rnsymtab.dup){
				if(cast(DeadDecl)sym||!scopes.any!(sc=>!!cast(DeadDecl)sc.rnsymtab.get(sym.getId,null))) continue;
				addDeadMerge(sym);
				symtabRemove(sym);
				if(dependencyTracked(sym)) pushDependencies(sym,false);
				changed=true;
			}
		}
		foreach(sc;scopes){
			foreach(sym;sc.rnsymtab.dup){
				if(sc.rnsymtab.get(sym.getId,null) !is sym) continue; // (consumed when pushing the dependencies of another variable)
				if(sym.isSemError()&&(!sym.scope_||!isNestedIn(sym.scope_))){
					// TODO: why needed?
					sym.scope_=this;
					continue;
				}
				if(auto dd=cast(DeadDecl)sym){
					auto dm=addDeadMerge(sym);
					static if(language==silq) bool force=!!cast(EarlyForgottenDecl)dd||!!cast(IllegalConsumedDecl)dd;
					else bool force=false;
					if(force||dm.mergedFrom.all!(d=>cast(DeadDecl)d))
					   dm.mergedFrom~=dd;
					assert(sym.getId !in rnsymtab||cast(DeadDecl)rnsymtab[sym.getId]);
					continue;
				}
				if(sym.getId !in rnsymtab){
					if(sym.scope_ !is sc&&sym.isSemError()){ // (not split into `sc` after an error in another branch)
						sc.symtabRemove(sym);
						continue;
					}
					sym=sc.split(sym,null);
					if(!sc.canForgetAppend(sym)&&!consumedByError(sym.getId)){
						error(format("variable `%s` is not consumed", sym.getName), sym.loc);
						sc.explainUnforgettable(sym);
						errors=true;
					}
					if(sc.dependencyTracked(sym))
						sc.pushDependencies(sym,false);
				}
			}
		}
		foreach(sc;scopes[1..$])
			dependencies.joinWith(sc.dependencies);
		foreach(sc;scopes){ // TODO: needed?
			foreach(decl,ref dep;sc.consumedDepLog)
				if(decl !in consumedDepLog)
					consumedDepLog[decl]=dep;
		}
		foreach(k,ref v;dependencies.dependencies)
			substituteConsumed(v,consumedDepLog);
		foreach(k,v;dependencies.dependencies.dup){
			if(k.getId !in rnsymtab)
				if(dependencyTracked(k))
					removeDependency(k);
		}
		foreach(sc;scopes){
			mergeDeclProps(sc.declProps,sc.componentConstBlocks);
		}
		foreach(_,dm;deadMerges){
			if(dm.mergedFrom.empty) continue;
			if(cast(DeadDecl)dm.mergedFrom[0]&&this.isNestedIn(dm.mergedFrom[0].scope_)&&dm.mergedFrom.all!(d=>d is dm.mergedFrom[0])){ // TODO: avoid making dm in the first place?
				symtabInsert(dm.mergedFrom[0]);
			}else symtabInsert(dm);
		}
		foreach(sc;scopes){
			sc.dependencies.clear();
			sc.dependenciesMerged=true;
		}
		foreach(k,v;symtab) assert(this.isNestedIn(v.scope_),text(v));
		foreach(k,v;rnsymtab) assert(this.isNestedIn(v.scope_),text(v));
		foreach(decl,ref dep;carryOverDependencies){
			if(decl !in dependencies.dependencies)
				dependencies.dependencies[decl]=dep;
		}
		lastUses.merge(isLoop,this,scopes);
		// TODO: needed?
		foreach(k,ref v;dependencies.dependencies)
			substituteConsumed(v,consumedDepLog);
		return errors;
	}

	final Declaration addVariable(Declaration decl,Expression type,bool isFirstDef=false)in{
		assert(decl&&!cast(DeadDecl)decl);
	}do{
		auto id=new Identifier(decl.name.id);
		id.loc=decl.name.loc;
		auto var=new VarDecl(id);
		var.loc=decl.loc;
		if(decl.rename){
			var.rename=new Identifier(decl.rename.id);
			var.rename.loc=decl.rename.loc;
		}
		if(auto d=symtabLookup(var.rename,true,null)){
			bool ok;
			if(isFirstDef) ok=tryPrepareRedefine(d,var);
			else ok=tryPrepareRedefine(var,d);
			if(!ok) return null;
		}
		symtabInsert(var);
		var.vtype=type;
		var.scope_=this;
		var.isConst_=isConstLocal(decl); // (splits and merges of `const` local variables; not of `const` parameters)
		if(auto vd=cast(VarDecl)decl) var.setTemporary(vd.isTemporary);
		import ast.semantic_:varDeclSemantic;
		varDeclSemantic(var,this);
		return var;
	}

	Annotation restriction(ref FunctionDef reason){
		return Annotation.none;
	}
	/// innermost construct that imposes a restriction of at least `annotation` (for diagnostics)
	RestrictionCause restrictionCause(Annotation annotation){
		return RestrictionCause.init;
	}

	private bool insertCapture(Identifier id,Declaration meaning,Scope outermost,bool consumedClassical=false){
		if(!meaning) return false;
		if(!meaning.isLinear()&&!id.byRef&&!consumedClassical) return true;
		auto type=id.typeFromMeaning(meaning);
		if(!type) return false;
		return insertCaptureImpl(id,meaning,type,outermost);
	}

	protected bool insertCaptureImpl(Identifier id,Declaration meaning,Expression type,Scope outermost){ return true; }

	protected void captureTypeDependencyImpl(Identifier id,Declaration meaning,Scope origin){}
	final void captureTypeDependencies(Expression type){ // (e.g., the type of a `typeof` operand, whose uses of outer variables do not capture)
		foreach(free;type.freeVars){
			auto meaning=free.meaning;
			if(!meaning||!meaning.scope_||meaning.isToplevelDeclaration()||!isNestedIn(meaning.scope_)) continue;
			Scope[] chain;
			for(Scope s=this;s&&s !is meaning.scope_;s=s.parentScope()) chain~=s;
			foreach_reverse(s;chain) s.captureTypeDependencyImpl(free,meaning,this);
		}
	}

	abstract FunctionDef getFunction();
	abstract DatDecl getDatDecl();
	final int all(T)(int delegate(T) dg){
		foreach(_,v;rnsymtab){
			auto t=cast(T)v;
			if(!t) continue;
			if(auto r=dg(t)) return r;
		}
		return 0;
	}

	static if(language==silq)
	void nameIndex(IndexExp index,Id name){ // semantic checks that those do not alias
		import ast.semantic_:getIdFromIndex;
		auto id=getIdFromIndex(index);
		assert(id&&id.meaning);
		updateDeclProps(id.meaning).nameIndex(index,name);
	}
	static if(language==silq)
	void reregisterComponentReplacement(IndexExp write,Id name,IndexExp read){
		import ast.semantic_:getIdFromIndex;
		auto id=getIdFromIndex(write);
		assert(id&&id.meaning);
		updateDeclProps(id.meaning).componentReplacements~=DeclProp.ComponentReplacement(write,name,read);
	}
	static if(language==silq)
	void blockConvertedAggregate(Declaration decl,IndexExp convertedWrite,Id name){
		updateDeclProps(decl).componentReplacements~=DeclProp.ComponentReplacement(null,name,null,null,convertedWrite);
	}

	struct ScopeState{
		bool loopEntryCanForget(Id id){ // whether the variable was forgettable at loop entry
			auto decl=rnsymtab.get(id,null);
			if(!decl) return false;
			return dependencies.canForget(decl);
		}
		bool opEquals(ref ScopeState rhs){
			if(!dependencies.matches(rhs.dependencies))
				return false;
			import ast.semantic_: typeForDecl;
			bool checkDecl(Declaration decl,Declaration rdecl){
				if(!rdecl) return false;
				import ast.semantic_: typeForDecl;
				if(typeForDecl(decl)==typeForDecl(rdecl))
					return true;
				return false;
			}
			bool compareTables(MapX!(Id,Declaration) symtab,MapX!(Id,Declaration) rsymtab){
				foreach(name,decl;rsymtab){
					if(cast(DeadDecl)decl) continue;
					if(name !in symtab)
						return false;
				}
				foreach(name,decl;symtab){
					if(cast(DeadDecl)decl) continue;
					if(!checkDecl(decl,rsymtab.get(name,null)))
						return false;
				}
				return true;
			}
			if(!compareTables(symtab,rhs.symtab))
				return false;
			if(!compareTables(rnsymtab,rhs.rnsymtab))
				return false;
			return true;
		}
		string toString(){
			string r;
			r~=text("dependencies: ",dependencies,"\n");
			import ast.semantic_: typeForDecl;
			import std.array: join;
			r~=text("{",symtab.values.map!text.join(", "),"}");
			return r;
		}
		private Identifier isConst(Declaration decl)in{
			assert(restoreable);
		}do{
			if(auto dprop=declProps.tryGet(decl))
				if(dprop.constBlock.length)
					return dprop.constBlock[$-1];
			return null;
		}
		private bool isNonConstDecl(Declaration decl){ // TODO: get rid of code duplication?
			if(!decl) return false;
			import ast.semantic_:typeConstBlocked,typeConstBlockedInState;
			if(!decl||decl.isConst||(rnsymtab.get(decl.getId,null) is decl?typeConstBlockedInState(decl,rnsymtab):typeConstBlocked(decl,rnsymtab))||isConst(decl))
				return false;
			return true;
		}
		Q!(Id,Declaration,Expression,bool)[][2] loopParams(NestedScope loopScope, scope MapX!(Declaration,Declaration)* mustBeConstFromDummies=null, bool separateConstParams=true, scope SetX!Declaration* accessedDecls=null, scope SetX!Id* namesInLoop=null, scope SetX!Id* unchangedConst=null, scope SetX!Id* consumedAfter=null, scope SetX!Id* freed=null, scope Declaration[]* forgetBefore=null)in{
			assert(!!loopScope);
		}do{ // (name,decl,type,mayChange)
			typeof(return) r;
			SetX!Id mustBeConst;
			if(mustBeConstFromDummies)
				foreach(v;(*mustBeConstFromDummies).byValue)
					mustBeConst.insert(v.getId);
			import ast.semantic_: typeForDecl;
			Scope letScope=null; // (variables declared outside of a `let` expression are captured, such that its lowering does not depend on where it is analyzed)
			for(Scope s=loopScope;s&&!cast(FunctionScope)s;s=cast(NestedScope)s?(cast(NestedScope)s).parent:null)
				if(auto bs=cast(BlockScope)s) if(bs.isLetBody){ letScope=bs; break; }
			SetX!Declaration inTypes; // (types of parameters cannot depend on other parameters)
			if(separateConstParams) foreach(id,decl;rnsymtab)
				if(auto type=typeForDecl(decl))
					foreach(tid;type.freeIdentifiers) if(tid.meaning) inTypes.insert(tid.meaning.canonicalSource);
			foreach(id,decl;rnsymtab){
				auto type=typeForDecl(decl);
				if(!type) continue;
				// variables whose names do not occur in the loop cannot change in it (they may still be split into the
				// loop scope, e.g. by an early `return` that has to forget them); they are not loop parameters
				if(namesInLoop&&id !in *namesInLoop&&(!decl.name||decl.name.id !in *namesInLoop)) continue;
				bool mayChange=isNonConstDecl(decl)||decl.isLinear();
				if(!mayChange&&forgetBefore&&namesInLoop&&type.isClassical()&&!decl.isConst&&!isConst(decl)&&decl.typeConstBlocker is null&&rnsymtab.get(decl.getId,null) is decl&&decl.splitInto.any!(d=>d.scope_ is loopScope)&&!unchangedOnContinuingPaths(decl,loopScope)){
					// (changed on paths that continue the loop, blocked by live variables that the loop and its continuation do not
					// mention, e.g., `x` in `x:=vector(n,…); for i in 0..2 { forget(n); n:=i; }`: they are forgotten before the loop,
					// as by the first change, which makes them unavailable after it)
					import ast.semantic_:liveTypeDependentsInState;
					auto deps=liveTypeDependentsInState(decl,rnsymtab);
					if(deps.length&&deps.all!((d){
						auto dtype=typeForDecl(d);
						return d.name&&d.name.id !in *namesInLoop&&dtype&&(dtype.isClassical()||dependencies.canForget(d));
					})){
						foreach(d;deps) if(!(*forgetBefore).canFind(d)) *forgetBefore~=d;
						mayChange=true;
					}
				}
				if(mayChange) mayChange=decl.splitInto.any!(d=>d.scope_ is loopScope);
				if(!mayChange){
					if(consumedAfter&&decl.name&&decl.name.id in *consumedAfter&&type.isClassical()&&!decl.isConst&&(cast(VarDecl)decl||cast(Parameter)decl)&&!decl.isToplevelDeclaration()&&!isTypeTy(type)&&!cast(FunTy)type){
						// (consumed by the code after the loop, which becomes part of the function, e.g., `n` in `forget(x); forget(n);` with
						// `x:𝔹^n`: the types of the parameters that mention it are weakened, see `lowerLoop`)
						Expression.CopyArgs cargsMoved;
						r[1]~=q(id,decl,type.copy(cargsMoved),true);
						if(freed) freed.insert(decl.name.id);
						continue;
					}
					if(!separateConstParams) continue;
					if(!accessedDecls||decl.canonicalSource !in *accessedDecls) continue; // not captured
					// (classical variables are passed as well: a function without captures is analyzed only once)
					if(type.isClassical()&&(!cast(VarDecl)decl&&!cast(Parameter)decl||decl.isToplevelDeclaration()||isTypeTy(type)||cast(FunTy)type||decl.canonicalSource in inTypes)) continue; // (const capture)
					if(type.isClassical()&&letScope&&!(decl.canonicalSource.scope_&&decl.canonicalSource.scope_.isNestedIn(letScope))) continue; // (const capture)
					Expression.CopyArgs cargsConst;
					r[0]~=q(id,decl,type.copy(cargsConst),false); // separate const parameter
					continue;
				}
				bool canForget=type.isClassical()||dependencies.canForget(decl);
				bool isConstParamDecl=false;
				if(canForget&&!type.isClassical()){
					isConstParamDecl=mustBeConstFromDummies?decl.getId in mustBeConst:true;
					if(mayChange&&unchangedConst&&unchangedOnContinuingPaths(decl,loopScope)){
						isConstParamDecl=true;
						unchangedConst.insert(id);
					}
				}
				Expression.CopyArgs cargs;
				r[isConstParamDecl?0:1]~=q(id,decl,type.copy(cargs),mayChange);
			}
			foreach(i;0..2) sort!"a[0].str<b[0].str"(r[i]);
			return r;
		}
		Expression typeOf(Id id){
			import ast.semantic_: typeForDecl;
			if(auto decl=rnsymtab.get(id,null)) return typeForDecl(decl);
			return null;
		}
		Expression typeOfName(Id name){
			import ast.semantic_: typeForDecl;
			foreach(_,decl;rnsymtab) if(!cast(DeadDecl)decl&&decl.name&&decl.name.id==name) return typeForDecl(decl);
			return null;
		}
		// (a variable comes after the variables whose types mention it in this state)
		Q!(Id,Declaration,Expression,bool)[] orderedByTypeMentions(Q!(Id,Declaration,Expression,bool)[] params){
			import ast.semantic_: typeForDecl;
			bool mentions(Q!(Id,Declaration,Expression,bool) p,Q!(Id,Declaration,Expression,bool) q){
				auto decl=rnsymtab.get(p[0],null);
				auto type=decl?typeForDecl(decl):null;
				return type&&type.freeIdentifiers.any!(id=>id.meaning&&id.meaning.getId==q[0]);
			}
			typeof(params) ordered,rest=params;
			while(rest.length){
				auto i=rest.countUntil!(p=>!rest.any!(q=>q[0]!=p[0]&&mentions(q,p)));
				if(i<0) i=0;
				ordered~=rest[i];
				rest=rest[0..i]~rest[i+1..$];
			}
			return ordered;
		}
		static bool unchangedOnContinuingPaths(Declaration decl,NestedScope loopScope){
			Declaration split=null;
			foreach(d;decl.splitInto) if(d.scope_ is loopScope) split=d;
			if(!split) return false;
			auto current=loopScope.rnsymtab.get(split.getId,null);
			return current&&current.isDerivedFrom(split);
		}
		Dependency dependencyOf(Declaration decl){
			if(decl !in dependencies.dependencies) return Dependency(true);
			return dependencies.dependencies[decl].dup;
		}
	private:
		Dependencies dependencies;
		DeclProps declProps;
		Declaration[] toRemove;
		TrackedTemporary[] trackedTemporaries;
		MapX!(Id,Declaration) symtab;
		MapX!(Id,Declaration) rnsymtab;
		MapX!(Declaration,LastUse) lastUses;
		Declaration[] prevCapturedDecls; // TODO: only store how many there are?
		bool restoreable=false;
		size_t numMergedNestedScopes;
		size_t numLastUses;
		size_t numMovedCaptures;
	}
	ScopeState getStateSnapshot(bool restoreable=false){
		MapX!(Id,Declaration) nsymtab=symtab.dup;
		MapX!(Id,Declaration) nrnsymtab=rnsymtab.dup;
		MapX!(Declaration,LastUse) nlastUses;
		DeclProps declProps;
		TrackedTemporary[] trackedTemporaries;
		Declaration[] prevCapturedDecls;
		size_t numMovedCaptures;
		if(restoreable){
			declProps=saveDeclProps();
			trackedTemporaries=trackedTemporaries.map!(x=>x.dup).array;
			nlastUses=lastUses.getSnapshot(this);
			if(auto fd=getFunction()){
				prevCapturedDecls=fd.capturedDecls;
				numMovedCaptures=fd.movedCaptures.length;
			}
		}
		auto r=ScopeState(dependencies.dup,declProps,toRemove,trackedTemporaries,nsymtab,nrnsymtab,nlastUses,prevCapturedDecls,restoreable);
		r.numMergedNestedScopes=mergedNestedScopes.length;
		r.numLastUses=lastUses.numAdded;
		r.numMovedCaptures=numMovedCaptures;
		return r;
	}
	Declaration getSplit(Declaration decl,bool clearSplitInto=false){
		if(decl.scope_ is this){
			if(clearSplitInto)
				resetSplits(decl);
			return decl;
		}
		if(decl.splitInto.length==0)
			return decl;
		foreach(ndecl;decl.splitInto){
			if(this.isNestedIn(ndecl.scope_))
				return getSplit(ndecl,clearSplitInto);
		}
		return decl;
	}

	void updateStateSnapshot(ref ScopeState state){
		if(auto fd=getFunction()){
			assert(state.prevCapturedDecls.length<=fd.capturedDecls.length);
			assert(state.prevCapturedDecls==fd.capturedDecls[0..state.prevCapturedDecls.length]);
			assert(state.numMovedCaptures<=fd.movedCaptures.length);
			void provide(Declaration decl){
				if(decl.getId !in state.rnsymtab||cast(DeadDecl)state.rnsymtab[decl.getId]){
					if(decl.name.id !in state.symtab||cast(DeadDecl)state.symtab[decl.name.id])
						state.symtab[decl.name.id]=decl;
					state.rnsymtab[decl.getId]=decl;
					auto tracked=trackingDecl(decl);
					if(tracked !is decl&&tracked in state.dependencies.dependencies&&decl !in state.dependencies.dependencies)
						state.dependencies.replace(tracked,decl);
				}
			}
			foreach(decl;fd.capturedDecls[state.prevCapturedDecls.length..$])
				if(fd.isConsumedCapture(decl)) provide(decl);
			foreach(decl;fd.movedCaptures[state.numMovedCaptures..$]) // (also a capture from before the snapshot)
				provide(decl);
			state.prevCapturedDecls=fd.capturedDecls;
			state.numMovedCaptures=fd.movedCaptures.length;
		}
		void splitSymtab(ref MapX!(Id,Declaration) symtab,bool replace){
			Q!(Declaration,Declaration)[] splits;
			foreach(id,ref decl;symtab){
				auto splt=getSplit(decl);
				if(splt !is decl){
					if(replace){
						if(decl in state.dependencies.dependencies)
							state.dependencies.replace(decl,splt);
						state.declProps.replaceDecl(decl,splt);
						if(auto lu=state.lastUses.get(decl,null)){ // (e.g., forgotten on entry)
							state.lastUses.remove(decl);
							state.lastUses[splt]=lu;
						}
					}
					decl=splt;
				}
			}
		}
		splitSymtab(state.rnsymtab,true);
		splitSymtab(state.symtab,false);
	}

	Declaration updateDecl(Declaration decl){
		auto split=getSplit(decl,true);
		if(decl !is split)
			replaceDecl(decl,split);
		return split;
	}

	static if(language==silq) private static bool forgottenBeforeEarlyReturn(Declaration decl){
		for(auto d=decl.splitFrom;d;d=d.splitFrom)
			if(d.forgottenBeforeEarlyReturn) return true;
		return false;
	}
	static if(language==silq) private bool consumedOutside(Declaration decl){ // (in an enclosing scope, which is not restored)
		if(!decl.scope_||decl.scope_ is this||decl.scope_.rnsymtab.get(decl.getId,null) is decl) return false;
		auto lu=lastUses.lastUses.get(decl,null);
		return lu&&lu.isConsumption();
	}
	void restoreStateSnapshot(ref ScopeState state,bool forWithTransTrial=false)in{
		assert(state.restoreable);
	}do{
		updateStateSnapshot(state);
		dependencies=state.dependencies;
		resetDeclProps(state.declProps);
		toRemove=state.toRemove;
		symtab.clear();
		foreach(_,decl;state.symtab){
			if(auto lu=state.lastUses.get(decl,null))
				if(lu.isConsumption()&&!forWithTransTrial)
					continue;
			static if(language==silq) if(!forWithTransTrial&&consumedOutside(decl)) continue;
			symtab[decl.name.id]=updateDecl(decl);
		}
		rnsymtab.clear();
		foreach(_,decl;state.rnsymtab){
			if(auto lu=state.lastUses.get(decl,null)){
				if(lu.isConsumption()&&!forWithTransTrial){
					if(!toRemove.canFind(lu.decl)){ // TODO: make more efficient
						toRemove~=lu.decl;
						if(dependencyTracked(lu.decl)) pushDependencies(lu.decl,true); // (consumed after the snapshot was taken)
					}
					recordConsumption(lu.decl,lu.use);
					continue;
				}
			}
			static if(language==silq) if(!forWithTransTrial){
				if(auto lu=lastUses.lastUses.get(decl,null)){
					if(lu.isConsumption()&&(forgottenBeforeEarlyReturn(decl)||consumedOutside(decl))){
						if(!toRemove.canFind(lu.decl)){
							toRemove~=lu.decl;
							if(dependencyTracked(lu.decl)) pushDependencies(lu.decl,true);
						}
						recordConsumption(lu.decl,lu.use);
						continue;
					}
				}
			}
			rnsymtab[decl.getId]=updateDecl(decl);
		}
		lastUses.restoreSnapshot(state.lastUses,state.numLastUses,this);
		foreach(scopes;mergedNestedScopes[state.numMergedNestedScopes..$])
			foreach(sc;scopes) sc.lastUses.discarded=true;
		state=ScopeState.init;
	}
	void fixLoopSplitMergeGraph( // skip subgraph generated during fixed-point iteration
		BlockScope loopScope,   // scope for non-zero-iterations path
		BlockScope forgetScope, // scope for zero-iterations path
		ref ScopeState origStateSnapshot, // declarations before loop
		ref ScopeState prevStateSnapshot, // declarations before last fixed-point iteration
	)in{
		assert(!!loopScope);
		assert(!!forgetScope); // TODO: repeat ... until loop?
		assert(loopScope.parent is this);
		assert(forgetScope.parent is this);
	}do{
		Declaration adaptOuter(Declaration decl){
			return getSplit(decl);
		}
		foreach(ref outer;loopScope.consumedOuter){
			if(outer.isSemError()) continue;
			assert(outer.scope_ is this);
			assert(outer.splitInto.length==2,text(outer," ",outer.splitInto," ",outer.loc," ",outer.splitInto.map!(x=>x.loc)));
			auto nonZeroIters=outer.splitInto[1];
			auto zeroIters=outer.splitInto[0];
			assert(nonZeroIters&&zeroIters);
			assert(nonZeroIters.splitFrom is outer);
			assert(zeroIters.splitFrom is outer);
			if(nonZeroIters.isSemError()||zeroIters.isSemError()) continue;
			assert(!nonZeroIters.scope_||nonZeroIters.scope_ is loopScope);
			assert(!zeroIters.scope_||zeroIters.scope_ is forgetScope);
			Declaration newOuter=null;
			if(outer.getId !in origStateSnapshot.rnsymtab){
				// declaration captured from outer scope
				auto fd=getFunction();
				assert(!!fd);
				foreach(decl;fd.capturedDecls){
					if(decl.name.id == outer.name.id){
						newOuter=adaptOuter(decl);
						break;
					}
				}
			}else newOuter=adaptOuter(origStateSnapshot.rnsymtab[outer.getId]);
			assert(!!newOuter);
			assert(newOuter.splitInto.length==2);
			assert(!newOuter.scope_||newOuter.scope_ is this);
			if(outer.getId in prevStateSnapshot.rnsymtab){ // TODO: make this always hold, even if there are errors?
				auto prevOuter=adaptOuter(prevStateSnapshot.rnsymtab[nonZeroIters.getId]);
				assert(prevOuter.splitInto.length==2);
				foreach(k;0..2){
					newOuter.splitInto[k]=prevOuter.splitInto[k];
					newOuter.splitInto[k].splitFrom=newOuter;
					newOuter.splitInto[k].resetCanonicalSource();
				}
				outer=newOuter;
			}
		}
	}
	uint typeofOperand=0; // block modifications while analyzing `typeof`
	MapX!(Declaration,Q!(Identifier,Scope)[])[] typeofConsumed; // simulate consumption while analyzing `typeof`
	static if(language==silq){ // support component replacement within `with` transformations
		Scope withTransConsumption=null;
		final Scope getWithTransConsumption(){
			for(auto sc=this;sc;sc=sc.parentScope())
				if(sc.withTransConsumption) return sc.withTransConsumption;
			return null;
		}
		WithTransTrial withTransTrial=null; // the `with` transformation trial analysis this scope belongs to, if any (trial effects on scopes not belonging to the trial are rolled back)
		final WithTransTrial getWithTransTrial(){ // innermost active trial on this scope's chain, if any (tags persist on scopes that outlive the trial, so skip inactive tokens)
			for(auto sc=this;sc;sc=sc.parentScope())
				if(sc.withTransTrial&&sc.withTransTrial.active)
					return sc.withTransTrial;
			return null;
		}
		Scope withTransBody=null;
		final Scope getWithTransBody(){
			for(auto sc=this;sc;sc=sc.parentScope())
				if(sc.withTransBody) return sc.withTransBody;
			return null;
		}
		Scope withTransTransformation=null;
		final Scope getWithTransTransformation(){
			for(auto sc=this;sc;sc=sc.parentScope())
				if(sc.withTransTransformation) return sc.withTransTransformation;
			return null;
		}
		static if(language==silq){ // hoisting of recomputable aliased const lookups (TODO: replace with more general solution)
			static struct AliasedConstReads{
				Expression stmt; // the statement the lookups were hoisted for
				MapX!(Expression,Id) temps; // lookup ↦ name of the temporary holding its value
				CompoundExp analyzedDefs; // the analyzed `__tmp := dup(lookup)` definitions
				bool defsWrapped;
			}
			AliasedConstReads[] aliasedConstReads; // stack, innermost statement last
			final bool lookupAliasedConstReadTemp(Expression e,ref Id name){
				for(auto sc=this;sc;sc=sc.parentScope())
					foreach_reverse(ref acr;sc.aliasedConstReads)
						if(e in acr.temps){
							name=acr.temps[e];
							return true;
						}
				return false;
			}
			bool withTransInverse=false; // analyzing the inverse transformation of a `with` (the write-back machinery)
			final Scope getWithTransInverse(){
				for(auto sc=this;sc;sc=sc.parentScope())
					if(sc.withTransInverse) return sc;
				return null;
			}
			// immediate hoisting (see hoistAliasedConstRead in semantic_.d):
			bool aliasedConstReadHoisting=false; // armed for the current statement
			Expression aliasedConstReadStmt; // the statement being analyzed
			int aliasedConstReadFlags; // the StmFlags at the start of the statement
			bool analyzingAliasedConstReadDef=false; // analyzing a temporary definition
			final Scope getAliasedConstReadHoistingScope(){
				for(auto sc=this;sc;sc=sc.parentScope())
					if(sc.aliasedConstReadHoisting) return sc;
				return null;
			}
		}
	}
	LastUses lastUses;
//private: // TODO
	Dependencies dependencies;
	bool dependenciesMerged=false; // (after a merge, the dependencies of a nested scope are those of the scope it was merged into)
	DeclProps declProps;
	MapX!(Id,Declaration) symtab;
	MapX!(Id,Declaration) rnsymtab;
}

struct RestrictionCause{
	Expression cause; // e.g., quantum `if`, quantum-controlled `return`, `with`, annotated function
	Expression control; // (quantum `if` controlling a `return`)
	bool laterIterations; // (restriction applies to loop iterations after the one containing the `return`)
	bool opCast(T:bool)(){ return !!cause; }
}

class TopScope: Scope{
	private ErrorHandler handler_;
	override @property ErrorHandler handler(){ return handler_; }
	this(string moduleName,ErrorHandler handler){
		this.moduleName=moduleName;
		this.handler_=handler;
	}
	override bool allowsLinear(){
		return false;
	}
	final void import_(Scope sc){
		imports~=sc;
		// TODO: store a location for better error messages
		// TODO: allow symbol lookup by full path
	}
	final Scope[] importedScopes(){ return imports; }
	override Declaration lookupImpl(Identifier ident,bool rnsym,bool lookupImports,Lookup kind,Scope origin,DeadDecl[]* failures){
		if(auto decl=super.lookupImpl(ident,rnsym,lookupImports,kind,origin,failures)) return decl;
		if(lookupImports){
			Declaration[] ds;
			foreach(sc;imports){
				if(auto d=sc.lookupImpl(ident,rnsym,false,kind,origin,failures)){
					ds~=d;
				}
			}
			if(ds.length==1||ds.length>=1&&rnsym) return ds[0];
			if(ds.length>1){
				error(format("multiple imports of %s",ident.name),ident.loc);
				foreach(d;ds) note("declaration here",d.loc);
				// TODO: return error
			}
		}
		return null;
	}
	override FunctionDef getFunction(){ return null; }
	override DatDecl getDatDecl(){ return null; }

	string moduleName;

	ToplevelDefinition[] analyzingDefinitions;
	final ToplevelDefinition analyzingDefinition(){
		return analyzingDefinitions.length?analyzingDefinitions[$-1]:null;
	}
private:
	Scope[] imports; // TODO: local imports, import declarations
}

class WithTransTrial{ // silq: token identifying one activation of the trial analysis of a `with` transformation (whose effects on scopes not belonging to the trial are rolled back)
	bool active=true;
	SetX!Declaration accessedAggregates; // variables accessed as a whole (not only through components) in the transformation (see `accessRoot`)
	SetX!Id liftedComponents; // replacement candidates for consumed components of lifted aggregates (which could be duplicated)
	SetX!Id rereadComponents; // replacement candidates whose component is read again in the transformation
}

class NestedScope: Scope{
	Scope parent;
	override @property ErrorHandler handler(){ return parent.handler; }
	this(Scope parent){
		this.parent=parent;
		static if(language==silq) if(parent) withTransTrial=parent.getWithTransTrial(); // scopes created while a `with` transformation trial analysis is active belong to the trial (`parent` is null for a `TypeScope`)
		if(parent) typeofOperand=parent.typeofOperand; // (scopes created within a `typeof` operand belong to it)
	}
	override Scope parentScope(){ return parent; }
	override @property bool inferenceMode(){
		return parent.inferenceMode;
	}

	private void splitIntoActiveNestedScopes(Declaration odecl,Declaration ndecl,Identifier use,IndexExp consumedComponent,bool splitting){ // (`ndecl` replaced `odecl` in this scope while it has active nested scopes)
		foreach(nsc;activeNestedScopes){
			Expression type;
			if(auto cdecl=nsc.consumeImpl(odecl,ndecl,type,false,use,consumedComponent,splitting)){
				if(getFunction() is nsc.getFunction()){
					if(nsc.dependencyTracked(odecl))
						nsc.removeDependency(odecl);
					nsc.addDependency(odecl,getDependency(ndecl,true).dup);
				}
				if(odecl !is cdecl)
					nsc.replaceDecl(odecl,cdecl);
				nsc.splitIntoActiveNestedScopes(odecl,cdecl,use,consumedComponent,splitting);
			}
		}
	}
	override Declaration consumeImpl(Declaration odecl,Declaration ndecl,ref Expression type,bool remove,Identifier use,IndexExp consumedComponent=null,bool splitting=false)in{
		assert(odecl is ndecl||!remove);
	}do{
		if(this is odecl.scope_) return super.consumeImpl(odecl,ndecl,type,remove,use,consumedComponent,splitting);
		if(rnsymtab.get(odecl.getId,null) !is odecl) return null;
		import ast.semantic_: typeForDecl;
		if(!type) type=typeForDecl(ndecl);
		auto pdep=getDefaultDependency(ndecl);
		Declaration result=ndecl;
		void processCurrent(){
			result=ndecl;
			if(type){
				symtabRemove(odecl);
				if(dependencyTracked(odecl)){
					// if(odecl !is ndecl) dependencies.replace(odecl,ndecl); // reverse-inherit dependencies through split
					auto prevConsumingUse=consumingUse;
					consumingUse=use;
					scope(exit) consumingUse=prevConsumingUse;
					pushDependencies(odecl,true,splitting?null:use);
				}
				// TODO: backtrace forgets and last usages
				if(auto added=addVariable(ndecl,type,true)){
					if(ndecl.isSemError()) added.setSemForceError();
					result=added;
					assert(ndecl.scope_ is parent&&result.scope_ is this,text(ndecl));
					splitVar(ndecl,result);
					retypeDeclaration(result,(Declaration m)=>getSplit(m));
					import ast.semantic_:propErr;
					propErr(ndecl,result);
					//imported!"util.io".writeln("MAKING SPLIT: ",ndecl," ",result," ",cast(void*)ndecl," ",cast(void*)result);
					if(remove){ // TODO: can we get rid of this?
						if(parent.getFunction() is getFunction()){
							if(dependencyTracked(odecl))
								removeDependency(odecl);
							//imported!"util.io".writeln("DEPS: ",dependencies);
							//imported!"util.io".writeln("ADDING DEP: ",odecl," ",result," ",pdep," ",cast(void*)this);
							addDependency(odecl,pdep.dup);
							//imported!"util.io".writeln("DEP IS NOW: ",getDependency(odecl));
						}
						assert(odecl !is result);
						replaceDecl(odecl,result);
					}
				}
			}
		}
		if(remove){
			assert(odecl is ndecl);
			if(auto nndecl=parent.consumeImpl(odecl,ndecl,type,true,use,consumedComponent,splitting)){
				pdep=parent.getDependency(nndecl,true);
				ndecl=nndecl;
				consumedOuter~=ndecl;
				auto siblings=getSiblingScopes();
				if(!siblings.length) processCurrent(); // TODO: get rid of this
				foreach(sc;siblings){
					if(this is sc){
						processCurrent();
						continue;
					}
					static if(language==silq)
					if(auto wtt=getWithTransTrial())
						if(sc.withTransTrial !is wtt)
							continue; // trial analysis of a `with` transformation: its effects are rolled back, so do not propagate consumption into sibling scopes that do not belong to the trial
					if(sc.diverges&&!sc.rnsymtab.get(odecl.getId,null)){ // (dropped by `closeUnreachable`, but the split is still part of the branch)
						if(type) if(auto added=sc.addVariable(ndecl,type,true)){
							sc.splitVar(ndecl,added);
							sc.symtabRemove(added);
							sc.replaceDecl(odecl,added);
						}
						continue;
					}
					if(auto cdecl=sc.consumeImpl(odecl,ndecl,type,false,use,consumedComponent,splitting)){
						if(parent.getFunction() is sc.getFunction()){
							if(sc.dependencyTracked(odecl)) // TODO: can we get rid of this?
								sc.removeDependency(odecl);
							//imported!"util.io".writeln("DEPS: ",sc.dependencies);
							//imported!"util.io".writeln("ADDING DEP: ",odecl," ",result," ",pdep," ",cast(void*)sc);
							sc.addDependency(odecl,pdep.dup);
							//imported!"util.io".writeln("DEP IS NOW: ",sc.getDependency(odecl));
						}
						if(odecl !is cdecl)
							sc.replaceDecl(odecl,cdecl);
						sc.splitIntoActiveNestedScopes(odecl,cdecl,use,consumedComponent,splitting);
					}
				}
			}else processCurrent();
		}else{
			consumedOuter~=ndecl;
			processCurrent();
		}
		if(!type&&remove){
			symtabRemove(odecl);
			if(dependencyTracked(odecl))
				pushDependencies(odecl,true,splitting?null:use);
			if(odecl !is result)
				replaceDecl(odecl,result);
			return result;
		}
		return remove?consume(result,use,consumedComponent,splitting):result;
	}

	override Declaration lookupImpl(Identifier ident,bool rnsym,bool lookupImports,Lookup kind,Scope origin,DeadDecl[]* failures){
		if(auto decl=lookupHereImpl(ident,rnsym,failures)) return decl;
		return parent.lookupImpl(ident,rnsym,lookupImports,kind,origin,failures);
	}

	override Annotation restriction(ref FunctionDef reason){ return parent.restriction(reason); }
	override RestrictionCause restrictionCause(Annotation annotation){ return parent.restrictionCause(annotation); }
	override int outerDeclProps(scope int delegate(ref DeclProps) dg){
		return parent.nestedDeclProps(dg);
	}
	override int outerComponentConstBlocks(scope int delegate(ComponentConstBlock) dg){
		return parent.nestedComponentConstBlocks(dg);
	}

	override bool isNestedIn(Scope rhs){ return rhs is this || parent.isNestedIn(rhs); }

	protected override bool insertCaptureImpl(Identifier id,Declaration meaning,Expression type,Scope outermost){
		if(this is outermost){
			if(!lastUses.get(meaning,true))
				lastUses.definition(meaning,null);
			return true;
		}
		foreach(sc;getSiblingScopes()){
			static if(language==silq)
			if(sc !is this)
				if(auto wtt=getWithTransTrial())
					if(sc.withTransTrial !is wtt) continue; // do not leak trial state into sibling scopes that do not belong to the trial
			if(meaning.getId in sc.rnsymtab) // TODO: make sure captures are inserted only once, remove this
				sc.symtabRemove(sc.rnsymtab[meaning.getId]);
			sc.symtabInsert(meaning);
			sc.lastUses.definition(meaning,null);
		}
		lastUses.definition(meaning,null);
		//if(rnsymtab.get(meaning.getId,null) !is meaning) lastUses.consumption(meaning,id,this);
		return parent.insertCaptureImpl(id,meaning,type,outermost);
	}

	override FunctionDef getFunction(){ return parent.getFunction(); }
	override DatDecl getDatDecl(){ return parent.getDatDecl(); }

	NestedScope[] siblingScopes;
	bool siblingsFinal;
	NestedScope[] getSiblingScopes(){
		if(siblingsFinal) return siblingScopes;
		return parent.activeNestedScopes;
	}
}

class RawProductScope: NestedScope{
	Annotation annotation;
	Expression productTy;
	this(Scope parent,Annotation annotation,Expression productTy=null){
		super(parent);
		this.annotation=annotation;
		this.productTy=productTy;
	}
	override Annotation restriction(ref FunctionDef reason){
		return annotation;
	}
	override RestrictionCause restrictionCause(Annotation annotation){
		return RestrictionCause(this.annotation>=annotation?productTy:null);
	}
	void forceClose(){}
	override Declaration lookupImpl(Identifier ident,bool rnsym,bool lookupImports,Lookup kind,Scope origin,DeadDecl[]* failures){
		if(auto decl=lookupHereImpl(ident,rnsym,failures)) return decl;
		auto decl=parent.lookupImpl(ident,rnsym,lookupImports,kind,origin,failures);
		if(decl&&kind==Lookup.consuming&&!decl.isToplevelDeclaration()&&!ident.typeofSuppressedCapture){
			error(format("cannot consume `%s` in a type",ident),ident.loc);
			ident.typeofSuppressedCapture=true;
			ident.setSemError();
		}
		return decl;
	}
}

class CapturingScope(T): NestedScope{
	T decl;
	this(Scope parent,T decl){
		super(parent);
		this.decl=decl;
		typeofOperand=0; // (a closure within a `typeof` operand captures as usual)
	}
	protected override void captureTypeDependencyImpl(Identifier id,Declaration meaning,Scope origin){
		if(!typeofOperand) addCapture(id,meaning,Lookup.constant,origin);
	}
	protected Declaration addCapture(Identifier id,Declaration meaning,Lookup kind,Scope origin){
		if(kind==Lookup.probing) return null;
		if(!meaning) return null;
		auto type=id.typeFromMeaning(meaning);
		/+if(type&&type.isClassical()&&id.byRef){
			origin.error("cannot consume classical variable from outer scope", id.loc);
			id.setSemError();
		}+/
		if(!meaning.scope_||!meaning.scope_.getFunction()) return null; // no need to capture global declarations
		if(meaning.isAggregateMember()) return null; // (members are accessed through `this`)
		if(id.isSemError()) return null;
		//imported!"util.io".writeln("capturing ",meaning," into ",decl);
		static if(is(T==FunctionDef)){
			// for recursive nested closures
			if(meaning.isSplitFrom(decl)){
				decl.seal();
				id.lazyCapture=true;
				Identifier[] recaptures;
				foreach(capture;decl.capturedDecls){
					if(capture.isSplitFrom(decl)) continue;
					auto recapture=new Identifier(capture.getId);
					recapture.loc=id.loc;
					recapture.scope_=origin;
					//imported!"util.io".writeln("RECAPTURING: ",capture," ",decl.isConsumedCapture(capture)," ",kind);
					bool isConsuming=decl.isConsumedCapture(capture)&&kind==Lookup.consuming;
					static if(language==silq) recapture.moved=isConsuming; // (also a classical capture, e.g., for an enclosing closure)
					DeadDecl[] failures;
					recapture.meaning=origin.lookup(recapture,true,false,isConsuming?Lookup.consuming:Lookup.constant,&failures);
					bool callErrorShown=false;
					void callError(){
						if(callErrorShown) return;
						callErrorShown=true;
						origin.error(format("cannot recursively call function `%s` at this location",decl.name),id.loc);
						id.setSemError();
					}
					if(!recapture.meaning){
						callError();
						origin.note(format("capture `%s` is missing",capture),capture.loc);
						if(failures.length){
							if(auto cd=cast(ConsumedDecl)failures[0]) cd.explain("capture",origin);
							else origin.note("captures cannot be modified on a path leading to a recursive call",id.loc);
						}
						recapture.setSemError();
					}else if(recapture.meaning.isSemError()) recapture.setSemError(); // (e.g., the capture was redefined erroneously)
					recapture.type=recapture.typeFromMeaning;
					assert(recapture.type||recapture.isSemError());
					if(!recapture.isSemError()){
						recapture.setSemCompleted();
						/+import ast.semantic_:typeForDecl;
						auto oldType=typeForDecl(capture);
						if(!isSubtype(recapture.type,oldType)){
							if(!recapture.isSemError()){
								callError();
								origin.note(format("capture `%s` changed type from `%s` to `%s`",capture.name,oldType,recapture.type),capture.loc);
								if(recapture.meaning)
									origin.note("capture is redeclared here",recapture.meaning.loc);
								recapture.setSemError();
							}
						}+/
						if(!recapture.meaning.isDerivedFrom(capture)){
							callError();
							origin.note(format("capture `%s` was modified",capture),capture.loc);
							// TODO: show first modification instead?
							origin.note("last modification is here",recapture.meaning.loc);
						}
					}
					if(recapture.isSemError())
						id.setSemError();
					recaptures~=recapture;
				}
				id.recaptures=recaptures;
			}else if(decl.sealed&&meaning.isLinear()&&meaning !in decl.captures){
				/+if(!id.isSemError()){
					origin.error("capturing additional quantum variables after a recursive call is not supported yet", id.loc);
					id.setSemError();
				}+/
				decl.unseal();
			}
		}
		if(!type) return null;
		foreach(free;type.freeVars){
			if(free.meaning)
				addCapture(free,free.meaning,Lookup.constant,origin);
		}
		import ast.semantic_:typeConstBlocked;
		bool isConstDecl=meaning.isConst||typeConstBlocked(meaning,origin)||origin.isConst(meaning);
		bool isConstLookup=kind==Lookup.constant||isConstDecl;
		static if(language==silq&&is(T==FunctionDef)){
			auto captureAnnotation=decl.ftype?decl.ftype.captureAnnotation:CaptureAnnotation.const_; // TODO: store in function def
			bool recomputeType=isConstLookup?captureAnnotation==CaptureAnnotation.moved:captureAnnotation==CaptureAnnotation.const_;
		}
		static if(language==silq)
		if(type.hasQuantumComponent()){
			if(origin.componentReplacements(meaning).length){
				origin.lastUses.definition(meaning,null);
				return null; // not captured, will be replaced (TODO: ok?)
			}
			/+if(isConstLookup&&!astopt.allowUnsafeCaptureConst){
				if(isConstDecl){
					origin.error(text("cannot capture `const` quantum ",meaning.kind), id.loc);
					if(meaning.typeConstBlocker){
						import ast.semantic_:typeConstBlockNote;
						typeConstBlockNote(meaning,this);
					}
					if(auto read=origin.isConst(meaning))
						origin.note(text(meaning.kind,"variable was made `const` here"), read.loc);
					id.setSemError();
					return null;
				}else{
					if(kind==Lookup.constant){
						origin.error(text("cannot capture quantum ",meaning.kind," as constant"), id.loc);
						id.setSemError();
					}
				}
			}+/
			static if(is(T==FunctionDef)){
				auto fd=decl;
				if(fd&&fd.context&&fd.context.vtype==contextTy(true)){
					if(fd.ftype&&fd.ftypeFinal){
						assert(fd.ftype.isClassical_);
						if(!id.isSemError()){
							origin.error(text("cannot capture quantum ",meaning.kind," in classical function"), id.loc);
							id.setSemError();
						}
					}else{
						if(fd.sealed) fd.unseal();
						fd.context.vtype=contextTy(false);
						recomputeType=true;
					}
				}
			}
		}
		auto meaningBefore=meaning,pmeaning=meaning;
		if(!id.lazyCapture){
			bool consumed=!isConstLookup&&(meaning.isLinear()||id.byRef);
			bool consumedClassical=false;
			static if(language==silq&&is(T==FunctionDef)) if(!isConstLookup&&meaning.name&&(meaning.name.id in decl.consumingCaptures||id.moved)) consumed=consumedClassical=true;
			static if(language==silq&&is(T==FunctionDef)) if(consumed&&consumesOutsideType(meaning,decl.typeBoundary?decl.typeBoundary:parent.letTypeBoundary())){
				origin.error(format("cannot consume `%s` in a type",meaning.name),id.loc);
				id.typeofSuppressedCapture=true; // (as within a product type)
				id.setSemError();
				return null;
			}
			static if(language==silq&&is(T==FunctionDef)) if(consumed&&id.typeofSuppressedCapture){ // (an enclosing `typeof` operand only simulates the capture)
				if(!id.isSemError) decl.addCapture(meaning,id);
				if(meaning.name) decl.consumingCaptures.insert(meaning.name.id);
				return meaning;
			}
			if(!id.isSemError){
				if(consumed) meaning=parent.split(meaning,id);
				decl.addCapture(meaning,id);
				pmeaning=meaning;
			}
			if(consumed){
				static if(is(T==FunctionDef)) decl.movedCaptures~=meaning;
				symtabInsert(meaning);
				meaning=consume(meaning,id);
				origin.insertCapture(id,meaning,this,consumedClassical);
				static if(language==silq&&is(T==FunctionDef)) if(consumedClassical&&!meaningBefore.isLinear()&&decl.fscope_.returnAnalyzed) decl.captureReanalysis=true; // (the returns analyzed before did not forget it)
				auto tracked=trackingDecl(meaningBefore);
				void replace(Scope csc){ // TODO: this is a bit hacky
					foreach(sc;csc.activeNestedScopes){
						sc.replaceDecl(meaningBefore,meaning);
						if(tracked !is meaningBefore) sc.replaceDecl(tracked,meaning);
						replace(sc);
					}
				}
				replace(this);
				static if(is(T==FunctionDef)){
					// (the scopes of nested functions that are being analyzed, e.g., of a closure in a closure that takes over the
					// capture, use the new version as well, but they keep tracking it through the declaration outside of their function)
					void replaceNested(Scope csc){
						csc.replaceDecl(meaningBefore,meaning);
						foreach(sc;csc.activeNestedScopes) replaceNested(sc);
					}
					if(meaning) for(Scope sc=origin;sc&&sc !is this;sc=sc.parentScope())
						if(cast(FunctionScope)sc) replaceNested(sc);
				}
				if(meaning) foreach(cid;decl.captures.get(pmeaning,null)) // (e.g., earlier constant captures, renamed when an enclosing function consumed its own capture)
					if(cid !is id&&cid.meaning is pmeaning) cid.meaning=meaning;
			}
			if(!id.isSemError()){
				static if(is(T==FunctionDef)){
					import ast.semantic_:updateFunctionDependency;
					auto origMeaning=id.meaning; // TODO: this is a hack
					id.meaning=meaning;// TODO: this is a hack
					updateFunctionDependency(decl);
					id.meaning=origMeaning; // TODO: this is a hack
				}
			}
		}else origin.lastUses.definition(meaning,null);
		parent.lastUses.capture(pmeaning,id,parent,decl);
		parent.recordAccess(id,pmeaning);
		if(!id.lazyCapture) parent.recordCapturer(decl,pmeaning);
		static if(language==silq&&is(T==FunctionDef)){
			auto fd=decl;
			if(recomputeType){
				fd.ftype=null;
				auto origMeaning=id.meaning; // TODO: this is a hack
				id.meaning=meaning;// TODO: this is a hack
				import ast.semantic_:setFtype;
				setFtype(fd,true);
				id.meaning=origMeaning; // TODO: this is a hack
			}
		}
		return meaning;
	}
	override Declaration lookupImpl(Identifier ident,bool rnsym,bool lookupImports,Lookup kind,Scope origin,DeadDecl[]* failures){
		if(auto decl=lookupHereImpl(ident,rnsym,failures)) return decl;
		if(auto pdecl=parent.lookupImpl(ident,rnsym,lookupImports,kind,origin,failures)){
			if(typeofOperand){
				if(kind==Lookup.probing) return pdecl; // tentative lookup: no side effects
				if(!ident.typeofSuppressedCapture){
					ident.typeofSuppressedCapture=true;
					static if(language==silq)
					if(auto fsc=origin.typeofFrame())
						if(!fsc.simulateTypeofConsumption(ident,pdecl,kind,origin,failures))
							return null;
				}
				return pdecl;
			}
			if(auto r=addCapture(ident,pdecl,kind,origin))
				return r;
			return pdecl;
		}
		return null;
	}
}

class FunctionScope: CapturingScope!FunctionDef{
	alias fd=decl;
	static if(language==silq) bool returnAnalyzed=false; // (a capture consumed afterwards requires another analysis)
	this(Scope parent,FunctionDef fd){
		super(parent,fd);
	}
	override Annotation restriction(ref FunctionDef reason){
		reason=fd;
		return fd.annotation;
	}
	override RestrictionCause restrictionCause(Annotation annotation){
		return RestrictionCause(fd.annotation>=annotation?fd:null);
	}
	void forceClose(){}
	override FunctionDef getFunction(){ return fd; }
	override @property bool inferenceMode(){
		if(fd.finalPassDone) return false;
		if(fd.inferringReturnType && !fd.ftypeFinal) return true;
		if(fd.tainted) return true;
		return parent.inferenceMode;
	}
}
class DataScope: CapturingScope!DatDecl{
	override bool allowsLinear(){
		return false; // TODO!
	}
	this(Scope parent,DatDecl decl){
		super(parent,decl);
	}
	override DatDecl getDatDecl(){ return decl; }
}
class BlockScope: NestedScope{
	this(Scope parent,Annotation restriction_=Annotation.none,RestrictionCause restrictionCause_=RestrictionCause.init){
		super(parent);
		if(parent&&parent.allowsLinear()) parent.nest(this);
		this.restriction_=restriction_;
		this.restrictionCause_=restrictionCause_;
	}
	Annotation restriction_;
	RestrictionCause restrictionCause_;
	bool isLoopBody=false;
	bool isLetBody=false;
	bool isLoopReset=false; // (of a `do`-`while` loop)
	bool keepConstLocals=false; // (not forgotten when merging, e.g., for a `with` transformation)
	bool loopFinalPass=false;
	bool speculative=false,cutShort=false;
	bool loopDeferredSpecificityCheck=false;
	override @property bool inferenceMode(){
		if(isLoopBody && !loopFinalPass) return true;
		return parent.inferenceMode;
	}
	override Annotation restriction(ref FunctionDef reason){
		FunctionDef parentReason=null;
		auto parentRestriction=super.restriction(parentReason);
		if(restriction_<parentRestriction){
			reason=parentReason;
			return parentRestriction;
		}
		return restriction_;
	}
	override RestrictionCause restrictionCause(Annotation annotation){
		if(restrictionCause_&&restriction_>=annotation) return restrictionCause_;
		return super.restrictionCause(annotation);
	}
	static if(language==silq) Scope typeBoundary=null; // (of a `let` expression within a type: the scope in which the analysis of the type started)
}

static if(language==silq)
bool consumesOutsideType(Declaration decl,Scope boundary){ // (a type cannot consume variables declared outside of it)
	if(!boundary||!decl||decl.isToplevelDeclaration()) return false;
	auto cs=decl.canonicalSource.scope_;
	return cs&&(cs is boundary||!cs.isNestedIn(boundary));
}

class TypeScope: BlockScope{
	Scope origin; // the scope at the call site
	LetExp reanalyzed; // (the substituted `let` expression analyzed in this scope, see ast.substitute.reanalyzeLet)
	MapSX!(Id,Declaration) freeDecls; // (the free variables of an analyzed copy, for parts that the analysis copies without meanings)
	this(Scope origin){
		super(null);
		this.origin=origin;
	}
	override @property ErrorHandler handler(){ assert(origin,"TypeScope without origin"); return origin.handler; }
	override @property bool inferenceMode(){ return false; }
	override Annotation restriction(ref FunctionDef reason){
		if(origin) return origin.restriction(reason);
		return restriction_;
	}
	override RestrictionCause restrictionCause(Annotation annotation){
		if(origin) return origin.restrictionCause(annotation);
		return RestrictionCause.init;
	}
	override Declaration lookupImpl(Identifier ident,bool rnsym,bool lookupImports,Lookup kind,Scope origin,DeadDecl[]* failures){
		if(auto decl=lookupHereImpl(ident,rnsym,failures)) return decl;
		if(auto decl=freeDecls.get(ident.id,null)) return decl;
		if(this.origin) if(auto top=this.origin.getTopScope()) return top.lookupImpl(ident,rnsym,lookupImports,kind,origin,failures); // (e.g., a prelude function used by a reversed `with` transformation)
		return null; // note: free identifiers carry their own scopes
	}
	override bool isNestedIn(Scope rhs){ return rhs is this || (parent && parent.isNestedIn(rhs)); }
	override FunctionDef getFunction(){ return origin?origin.getFunction():null; } // TODO: ok?
	override DatDecl getDatDecl(){ return origin?origin.getDatDecl():null; } // TODO: ok?
	override NestedScope[] getSiblingScopes(){ return siblingScopes; }
	override int outerDeclProps(scope int delegate(ref DeclProps) dg){ return 0; }
	override Declaration consumeImpl(Declaration odecl,Declaration ndecl,ref Expression type,bool remove,Identifier use,IndexExp consumedComponent=null,bool splitting=false)in{
		assert(odecl is ndecl||!remove);
	}do{
		if(this is odecl.scope_) return super.consumeImpl(odecl,ndecl,type,remove,use,consumedComponent,splitting);
		return null;
	}
	protected override bool insertCaptureImpl(Identifier id,Declaration meaning,Expression type,Scope outermost){
		if(this is outermost){
			if(!lastUses.get(meaning,true))
				lastUses.definition(meaning,null);
			return true;
		}
		lastUses.definition(meaning,null);
		return parent?parent.insertCaptureImpl(id,meaning,type,outermost):false;
	}
}

struct TypeTransition{
	Scope target;
	Scope localRoot;
	SetX!Id taken;
	MapSX!(Declaration,Declaration) declMap;
	SetX!Scope codScopes;
	MapSX!(Declaration,Scope) declRegion;
	MapSX!(Scope,TypeScope) scopes;

	Id freshName(Id b){
		auto nb=b;
		do nb=nb.apos; while(nb in taken);
		taken[nb]=[];
		return nb;
	}

	TypeScope mapScope(Scope sc){
		if(auto p = scopes.getPtr(sc)) return *p;
		auto ts=new TypeScope(target);
		scopes[sc]=ts;
		if(auto parent=sc.parentScope())
			if(parent in codScopes)
				ts.parent=mapScope(parent);
		return ts;
	}
}
class AggregateScope: NestedScope{
	this(Scope parent){ super(parent); }
	override bool allowsLinear(){
		return false; // TODO!
	}
}
