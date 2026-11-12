// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.scope_;
import astopt;

import std.format, std.conv, std.range, std.algorithm;
import util.tuple:Q=Tuple,q=tuple;
import ast.lexer, ast.expression, ast.declaration, ast.type, ast.error;
import util, util.hashtable: HashMap, PersistentMap, Storage;

alias SymbolTable=PersistentMap!(Id,Declaration,(a,b)=>a==b,hashOf,symbolProperties); // (the copies for nested scopes share the entries that did not change; `liveValues` skips the dead entries, which accumulate in long scopes)
enum SymbolProperty:ubyte{
	live=1,
	notFixedClassical=2, // (live, and not a classical variable whose type mentions no variables, which stays classical, see `Scope.close`)
}
ubyte symbolProperties(Declaration d){
	static bool quantum(Expression type){ // (as `hasQuantumComponent`, but without its lookup for the usual kinds of types)
		if(type.type is qtypeTy) return true;
		if(type.type is ctypeTy) return false;
		return hasQuantumComponent(type);
	}
	if(auto vd=cast(VarDecl)d){
		auto type=vd.vtype;
		if(type&&type.isSemEvaluated()&&!quantum(type)&&!type.freeIdentifiers.any!(id=>!!id.meaning)) return SymbolProperty.live;
		return SymbolProperty.live|SymbolProperty.notFixedClassical;
	}
	return cast(DeadDecl)d?0:SymbolProperty.live|SymbolProperty.notFixedClassical;
}

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
	private alias Table=PersistentMap!(Declaration,Dependency*,(a,b)=>a is b,(a)=>a.toHash()); // (an entry is not changed in place: a change replaces it)
	private alias Keys=PersistentMap!(Declaration,bool,(a,b)=>a is b,(a)=>a.toHash());
	private alias Index=PersistentMap!(Declaration,Keys,(a,b)=>a is b,(a)=>a.toHash());
	private static final class State{
		Table table; // (the copies for nested scopes share the entries that did not change)
		Index mentionedBy; // (for each declaration, the variables whose dependencies mention it)
		Keys nontrivial; // (the variables whose dependencies mention some variable)
	}
	private State state; // (apart from the scope, which then stays within its size class of the garbage collector; a copy shares it, see `dup`)
	private @property ref Table table(){ if(!state) state=new State; return state.table; }
	private @property ref Index mentionedBy(){ if(!state) state=new State; return state.mentionedBy; }
	private @property ref Keys nontrivial(){ if(!state) state=new State; return state.nontrivial; }
	private static bool isNontrivial(ref Dependency v){ return !v.isTop&&v.dependencies.length; }
	private static Dependency* box(Dependency v){
		auto r=new Dependency;
		*r=v;
		return r;
	}
	private void addIndex(Declaration x,Declaration k){
		auto s=mentionedBy.get(x,Keys.init);
		s[k]=true;
		mentionedBy[x]=s;
	}
	private void removeIndex(Declaration x,Declaration k){
		auto s=mentionedBy.get(x,Keys.init);
		if(k !in s) return;
		s.remove(k);
		if(s.length) mentionedBy[x]=s;
		else mentionedBy.remove(x);
	}
	private void reindex(Declaration k,Dependency* old,ref Dependency nv){ // (`old`: the entry for `k` before, if any)
		if(old&&!old.isTop) foreach(x;old.dependencies) if(nv.isTop||x !in nv.dependencies) removeIndex(x,k);
		if(!nv.isTop) foreach(x;nv.dependencies) if(!old||old.isTop||x !in old.dependencies) addIndex(x,k);
		auto was=old&&isNontrivial(*old),now=isNontrivial(nv);
		if(was==now) return;
		if(now) nontrivial[k]=true;
		else nontrivial.remove(k);
	}
	Declaration[] nontrivialKeys(){ // (the variables whose dependencies mention some variable)
		Declaration[] r;
		nontrivial.eachKey((Declaration k){ r~=k; });
		return r;
	}
	bool tracked(Declaration decl){ pragma(inline,true); return !!(decl in table); }
	@property size_t numChanges(){ return table.numChanges; } // (equal for a copy and the table it was copied from while neither changes)
	void startLog(Declaration[] initial=null){ table.startLog(initial); }
	void stopLog(){ table.stopLog(); }
	@property bool isLogging(){ return table.isLogging; }
	@property Declaration[] changeLog(){ return table.changeLog; } // (see `PersistentMap.changeLog`)
	Dependency getCopy(Declaration decl){ return table[decl].dup; }
	private static bool same(ref Dependency a,ref Dependency b){
		return a.isTop==b.isTop&&a.lostVar is b.lostVar&&a.lostAt is b.lostAt&&a.dependencies==b.dependencies;
	}
	Dependency get(Declaration decl){
		auto v=*table[decl];
		return v.dependencies.isSmall?v:v.dup; // (the caller cannot change the entry, which the copies share)
	}
	Declaration[] keys(){ return table.keys; }
	void set(Declaration decl,Dependency dep){
		Dependency* old;
		table.tryGet(decl,old);
		reindex(decl,old,dep);
		table[decl]=box(dep);
	}
	void remove(Declaration decl){
		Dependency* old;
		if(table.tryGet(decl,old)){
			auto top=Dependency(true);
			reindex(decl,old,top);
		}
		table.remove(decl);
	}
	Declaration[] mentioning(Declaration decl){ // (the variables whose dependencies mention `decl`, in the order of the table)
		auto s=mentionedBy.peek(decl);
		if(!s) return null;
		Q!(size_t,Declaration)[] r;
		s.eachKey((Declaration k){
			size_t pos;
			auto found=table.tryGetPosition(k,pos);
			assert(found);
			r~=q(pos,k);
		});
		sort!"a[0]<b[0]"(r);
		return r.map!(x=>x[1]).array;
	}
	void update(scope void delegate(Declaration,ref Dependency) dg){ updateKeys(dg,table.keys); } // (of all variables)
	void updateKeys(scope void delegate(Declaration,ref Dependency) dg,Declaration[] keys){ // (of the variables `keys` that have entries)
		foreach(k;keys){
			Dependency* v;
			if(!table.tryGet(k,v)) continue;
			auto nv=v.dup;
			dg(k,nv);
			if(!same(nv,*v)) set(k,nv);
		}
	}
	void joinWith(ref Dependencies rhs){ joinWithKeys(rhs,table.keys); }
	void joinWithKeys(ref Dependencies rhs,Declaration[] keys){ // (of the variables `keys` that have entries in both)
		foreach(k;keys){
			Dependency* v,r;
			if(!table.tryGet(k,v)||!rhs.table.tryGet(k,r)) continue;
			auto nv=v.dup;
			nv.joinWith(*r);
			if(k in nv.dependencies) nv=Dependency(true); // TODO: get rid of this
			if(!same(nv,*v)) set(k,nv);
		}
	}
	void pushUp(Declaration removed, bool keep, Identifier consumedAt=null)in{
		assert(removed in table,text(removed," ",removed.loc," ",toString()));
	}do{
		Dependency x=*table[removed];
		if(!keep) remove(removed);
		foreach(k;mentioning(removed)){
			auto v=table[k].dup;
			v.replace(removed, x, consumedAt);
			if(k in v.dependencies)
				v=Dependency(true); // TODO: get rid of this
			set(k,v);
		}
	}
	void replace(Declaration decl,Declaration ndecl)in{
		assert(decl in table,text(decl.loc," ",toString()));
		assert(ndecl !in table,text(ndecl.loc," ",toString()));
	}do{
		replaceInDependencies(decl,ndecl);
		set(ndecl,*table[decl]);
		remove(decl);
	}
	void replaceInDependencies(Declaration decl,Declaration ndecl,Declaration except=null){ // (in those of all variables except `except`)
		foreach(k;mentioning(decl)){
			if(k is except) continue;
			auto v=table[k].dup;
			v.replace(decl,ndecl);
			set(k,v);
		}
	}
	void merge(Declaration decl,Declaration ndecl)in{ // (`ndecl` is another version of the variable of `decl`)
		assert(decl in table&&ndecl in table);
	}do{
		auto dep=*table[decl];
		remove(decl);
		auto changed=mentioning(decl);
		foreach(k;changed){
			auto v=table[k].dup;
			v.replace(decl,ndecl);
			set(k,v);
		}
		auto nv=table[ndecl].dup;
		nv.joinWith(dep);
		set(ndecl,nv);
		foreach(k;chain(changed,only(ndecl))){ // (only these can come to mention themselves)
			auto v=table[k];
			if(k in v.dependencies)
				set(k,Dependency(true)); // TODO: get rid of this
		}
	}
	void substitute(Declaration decl,Dependency dep){ // substitute `decl` by `dep` inside all tracked sets (`decl` itself has no entry)
		foreach(k;mentioning(decl)){
			auto v=table[k].dup;
			v.replace(decl,dep);
			if(k in v.dependencies)
				v=Dependency(true); // TODO: get rid of this
			set(k,v);
		}
	}
	Dependencies dup(){
		Dependencies r;
		r.state=new State;
		r.state.table=table.dup;
		r.state.mentionedBy=mentionedBy.dup;
		r.state.nontrivial=nontrivial.dup;
		return r;
	}
	bool canForget(Declaration decl)in{
		assert(decl in table||decl.isSemError(),text(decl," ",toString()));
	}do{
		if(decl !in table) return true;
		return !table[decl].isTop;
	}
	void clear(){
		table.clear();
		mentionedBy.clear();
		nontrivial.clear();
	}
	private HashMap!(Id,typeof(Dependency.getIds()),(a,b)=>a is b,(a)=>a.toHash) getIds(){
		typeof(return) result;
		foreach(decl,dependency;table){
			auto id=decl.getId;
			if(id==Id()) continue;
			assert(id !in result,text(decl," ",toString()," ",result));
			result[id]=dependency.getIds();
		}
		return result;
	}
	bool matches(Dependencies rhs){ // TODO: make faster?
		auto ids=getIds,rids=rhs.getIds;
		return ids==rids;
	}
	string toString(){
		string r="[";
		foreach(k,v;table) r~=text(k,":",*v)~", ";
		if(r.length>2) r=r[0..$-2];
		return r~"]";
	}
}

struct DummyWitnessContext{
	MapX!(Declaration,Declaration) dummies; // candidate -> dummy placeholder
	MapX!(Declaration,Declaration) results; // candidates witnessed so far
	MapSX!(Declaration,Dependency) consumedDeps; // dependency each decl had when it was consumed while this context was active
	SetX!Id[] nestedLoopCarried; // the loop-carried candidates of each nested quantum loop analyzed while this context was active
	Dependency[] reconstructed; // dependencies of quantum guards whose inputs change while borrowed, and of variables that recomputed temporaries depend on (see `noteImplicitDupCancelled`)
	size_t order; // (of the implicit duplications and the recomputed temporaries below)
	MapX!(Identifier,size_t) dupOrder; // implicit duplications
	Q!(size_t,SetX!Id)[] recomputed; // variables that temporaries forgotten by recomputation depend on
}

import ast.lastuse;
enum Lookup{
	consuming,
	constant,
	probing,
	probingWithCapture,
}

final class Mentions{ // (the variables that a branch or a loop body that diverges mentions, see `Scope.closeUnreachable`)
	private bool[Id] names;
	Id[] ids;
	void add(Id id){
		if(id in names) return;
		names[id]=true;
		ids~=id;
	}
	bool opCall(Declaration d){ return !!(d.getId in names); }
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
	int droppedCodeAnalysis; // loop lowering: the code after a loop that the lowering drops is being analyzed, without lowering its loops (see `unreachableSemantic`)
	uint typeofOperand=0; // block modifications while analyzing `typeof`
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
		auto prev=symtabLookup(decl.name,false,null);
		Declaration hidden=null; // (a classical variable from outside that a `return` dropped, see `hiddenAfterReturn`: the declaration does not redefine it)
		if(prev&&hiddenAfterReturn(prev)) swap(prev,hidden);
		if(auto d=prev){
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
				if(!d||hiddenAfterReturn(d)) continue;
				if(auto dd=cast(DeadDecl)d)
					if(dd.reportRedefinition(decl,this))
						return false;
				break;
			}
			if(!checkCaptureRedefinition(decl)) return false;
		}
		rename(decl);
		if(hidden) symtabRemove(hidden);
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
		if(auto old=rnsymtab.get(decl.getId,null)){
			if(isRenamedDead(old)) numRenamedDead--;
			if(declProps.tracked) leftTable~=old;
			if(sinceMergeLogged&&dependencyTracked(old)) removedTracked~=old;
		}
		rnsymtab[decl.getId]=decl;
		if(isRenamedDead(decl)) numRenamedDead++;
		if(mayMentionInType(decl)) noteTypeMentioning(decl);
		static if(language==silq) noteInserted(decl);
	}
	static if(language==silq) void noteInserted(Declaration decl){} // (see `NestedScope.continuedLog`)
	private static bool isRenamedDead(Declaration decl){ return cast(DeadDecl)decl&&decl.name&&decl.getId!=decl.name.id; }
	private SetX!Declaration typeMentioning_; // (the declarations of `rnsymtab` whose types may mention variables, see `typeMentioning`; and others that are no longer there)
	private size_t numTypeMentioningAtPrune; // (the size of `typeMentioning_` after its last pruning)
	private void noteTypeMentioning(Declaration decl){
		typeMentioning_.insert(decl);
		if(typeMentioning_.length>2*numTypeMentioningAtPrune+16) pruneTypeMentioning();
	}
	private void pruneTypeMentioning(){ // (removes the declarations that are no longer in `rnsymtab` or whose types mention no variable)
		Declaration[] gone;
		foreach(d;typeMentioning_) if(rnsymtab.get(d.getId,null) !is d||!mayMentionInType(d)) gone~=d;
		foreach(d;gone) typeMentioning_.remove(d);
		numTypeMentioningAtPrune=typeMentioning_.length;
	}
	static bool mayMentionInType(Declaration decl){ // (or its type is still to be determined)
		import ast.semantic_: typeForDeclNoAnalyze;
		auto type=typeForDeclNoAnalyze(decl);
		if(!type) return cast(VarDecl)decl||cast(FunctionDef)decl; // (e.g., `addVariable` determines the type after the insertion)
		return decl.typeWithoutMentions !is type&&!(type.isSemEvaluated()&&!type.freeIdentifiers.any!(id=>!!id.meaning));
	}
	final void noteType(Declaration decl){ // (its type changed: it may be in the tables of the nested scopes as well)
		if(!mayMentionInType(decl)) return;
		void add(Scope sc){
			sc.noteTypeMentioning(decl);
			foreach(nsc;sc.activeNestedScopes) add(nsc);
		}
		add(this);
		for(auto nsc=cast(NestedScope)this;nsc&&nsc.parent;nsc=cast(NestedScope)nsc.parent) // (e.g., merged into the enclosing scopes)
			if(nsc.parent.rnsymtab.get(decl.getId,null) is decl) add(nsc.parent);
	}
	final Declaration[] typeMentioning(){ // (the declarations of `rnsymtab` whose types may mention variables, in the order of `rnsymtab`)
		Q!(size_t,Declaration)[] r;
		Declaration[] gone;
		foreach(d;typeMentioning_){
			size_t pos;
			if(rnsymtab.get(d.getId,null) !is d||!mayMentionInType(d)||!rnsymtab.tryGetPosition(d.getId,pos)){ gone~=d; continue; }
			r~=q(pos,d);
		}
		foreach(d;gone) typeMentioning_.remove(d);
		numTypeMentioningAtPrune=typeMentioning_.length;
		sort!"a[0]<b[0]"(r);
		return r.map!(x=>x[1]).array;
	}
	private void resetTypeMentioning(){ // (after `rnsymtab` was replaced)
		typeMentioning_=typeof(typeMentioning_).init;
		foreach(_,d;rnsymtab) if(mayMentionInType(d)) typeMentioning_.insert(d);
		numTypeMentioningAtPrune=typeMentioning_.length;
	}
	void symtabRemove(Declaration decl)in{
		assert(!!decl);
		assert(rnsymtab.get(decl.getId,null) is decl);
	}do{
		if(symtab.get(decl.name.id,null) is decl)
			symtab.remove(decl.name.id);
		rnsymtab.remove(decl.getId);
		if(isRenamedDead(decl)) numRenamedDead--;
		if(sinceMergeLogged&&dependencyTracked(decl)) removedTracked~=decl;
		if(declProps.tracked) leftTable~=decl;
	}
	private Declaration[] leftTable; // (the declarations that left `rnsymtab` since the last statement, see `afterStatement`)

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
		size_t seq; // (in the order of recording, see `DeclProps.inOrder`)
		size_t activated; // (in the order of `DeclProps.props`, see `DeclProps.set`)
		static DeclProp default_(){
			return DeclProp.init;
		}
		DeclProp dup(){
			return DeclProp(constBlock,componentReplacements.dup,accesses.dup,capturers.dup,seq);
		}
		DeclProp move(){
			auto r=DeclProp(constBlock,componentReplacements,accesses,capturers,seq);
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
	static final class RetiredDeclProps{ // (of the declarations that are no longer live in a scope, see `afterStatement`)
		MapSX!(Declaration,DeclProp) props;
		MapX!(Declaration,Declaration[]) typeMentions; // (by the variables that their types mention, see `Scope.replaceDecl`)
		size_t numRecorded; // (see `DeclProp.seq`)
	}
	static struct DeclProps{
		private MapSX!(Declaration,DeclProp) props; // (the properties that statements change, e.g., `const` blocks, are only those of live declarations)
		private RetiredDeclProps retired; // (snapshots share it without changing it, see `resetDeclProps`)
		private bool snapshot;
		private size_t numRemoved; // (from `props` since it was compacted)
		private Declaration[] blocked; // (the declarations whose `const` blocks may be nonempty, see `noteBlocked`)
		private size_t numBlockedAtPrune;
		private Declaration[] replaced; // (the declarations whose component replacements may be nonempty, see `noteReplaced`)
		private size_t numReplacedAtPrune;
		private Declaration[] added; // (those whose properties became active since the last retirement, or are not retired because of nonempty `const` blocks or component replacements, see `retire`)
		private bool tracked; // (whether `added` is maintained, otherwise each retirement considers all properties)
		private bool retireAll; // (whether the next retirement considers all properties)
		private size_t numActivated; // (see `DeclProp.activated`)
		private Q!(Declaration,size_t)[] removedLog; // (from `props`, with `DeclProp.activated`, while component replacements are moved, see `ComponentReplacementContext`)
		private size_t numMoves;
		DeclProps dup(){
			auto r=DeclProps(props.dup,retired,true,numRemoved);
			r.blocked=blocked.dup;
			r.numBlockedAtPrune=numBlockedAtPrune;
			r.replaced=replaced.dup;
			r.numReplacedAtPrune=numReplacedAtPrune;
			r.retireAll=true;
			r.tracked=tracked;
			r.numActivated=numActivated;
			return r;
		}
		void noteAdded(Declaration decl){ if(tracked) added~=decl; } // (see `retire`)
		void noteReplaced(Declaration decl){ // (its component replacements may be nonempty)
			replaced~=decl;
			if(replaced.length>2*numReplacedAtPrune+16){
				replaced=ordered(replaced,(ref DeclProp p)=>p.componentReplacements.length!=0);
				numReplacedAtPrune=replaced.length;
			}
		}
		private Declaration[] ordered(Declaration[] decls,scope bool delegate(ref DeclProp) has){ // (the declarations with active properties that `has`, without repetitions, in the order of `props`)
			if(!decls.length) return null;
			Q!(size_t,Declaration)[] r;
			SetX!Declaration seen;
			foreach(d;decls){
				if(d in seen) continue;
				seen.insert(d);
				if(auto p=tryGet(d)) if(has(*p)) r~=q(p.activated,d);
			}
			sort!"a[0]<b[0]"(r);
			return r.map!(x=>x[1]).array;
		}
		Declaration[] withConstBlocks(){ // (in the order of `props`)
			if(!blocked.length) return null;
			blocked=ordered(blocked,(ref DeclProp p)=>p.constBlock.length!=0);
			numBlockedAtPrune=blocked.length;
			return blocked.dup;
		}
		Declaration[] withReplacements(){ // (in the order of `props`)
			if(!replaced.length) return null;
			replaced=ordered(replaced,(ref DeclProp p)=>p.componentReplacements.length!=0);
			numReplacedAtPrune=replaced.length;
			return replaced.dup;
		}
		void noteBlocked(Declaration decl){ // (its `const` block may be nonempty)
			blocked~=decl;
			if(blocked.length>2*numBlockedAtPrune+16){
				blocked=ordered(blocked,(ref DeclProp p)=>p.constBlock.length!=0);
				numBlockedAtPrune=blocked.length;
			}
		}
		private size_t nextSeq(){
			if(!retired) retired=new RetiredDeclProps;
			return retired.numRecorded++;
		}
		DeclProp* tryGet(Declaration decl){ return props.getPtr(decl); }
		private DeclProp* tryGetRetired(Declaration decl){
			if(snapshot||!retired) return null;
			return retired.props.getPtr(decl);
		}
		DeclProp* tryGetAny(Declaration decl){ // (also of a declaration that is no longer live, e.g., its accesses)
			if(auto r=tryGet(decl)) return r;
			return tryGetRetired(decl);
		}
		ref DeclProp set(Declaration decl,DeclProp prop){
			if(auto p=tryGet(decl)){
				prop.seq=p.seq;
				prop.activated=p.activated;
			}else{
				if(auto p=tryGetRetired(decl)) prop.seq=p.seq;
				else prop.seq=nextSeq();
				prop.activated=++numActivated;
				noteAdded(decl);
			}
			auto r=&(props[decl]=prop);
			if(prop.constBlock.length) noteBlocked(decl); // (after it is stored, which a pruning keeps)
			if(prop.componentReplacements.length) noteReplaced(decl);
			return *r;
		}
		DeclProp* active(Declaration decl){
			if(auto r=tryGet(decl)) return r;
			if(auto r=tryGetRetired(decl)) return &set(decl,*r); // (e.g., a `const` block of a version that a statement consumes)
			return &set(decl,DeclProp.default_());
		}
		DeclProp* history(Declaration decl){ // (for accesses and capturers)
			if(auto r=tryGetAny(decl)) return r;
			return &set(decl,DeclProp.default_());
		}
		Q!(Declaration,DeclProp*)[] inOrder(){ // (also the retired properties)
			Q!(Declaration,DeclProp*)[] r;
			foreach(decl,ref prop;props) r~=q(decl,&prop);
			if(!snapshot&&retired) foreach(decl,ref prop;retired.props) if(decl !in props) r~=q(decl,&prop);
			sort!"a[1].seq<b[1].seq"(r);
			return r;
		}
		void merge(ref DeclProps nested){
			foreach(e;nested.inOrder){
				if(auto prop=tryGetAny(e[0])) prop.merge(*e[1]);
				else set(e[0],e[1].merged());
			}
		}
		void replaceDecl(Declaration splitFrom,Declaration splitInto){
			if(auto declProp=tryGet(splitFrom)){
				declProp.replaceDecl(splitFrom,splitInto);
				auto activated=declProp.activated;
				set(splitInto,declProp.move());
				if(numMoves) removedLog~=q(splitFrom,activated);
				props.remove(splitFrom);
				numRemoved++;
				if(tryGetRetired(splitFrom)) retired.props.remove(splitFrom); // (from before it was active again, see `active`)
			}else if(auto declProp=tryGetRetired(splitFrom)){
				declProp.replaceDecl(splitFrom,splitInto);
				auto moved=declProp.move();
				if(tryGet(splitInto)) set(splitInto,moved);
				else{
					if(auto p=tryGetRetired(splitInto)) moved.seq=p.seq;
					else moved.seq=nextSeq();
					retired.props[splitInto]=moved;
					indexRetired(splitInto);
				}
				retired.props.remove(splitFrom);
			}
		}
		void moveComponentReplacements(Declaration prev,Declaration new_){
			if(auto prevProp=tryGetAny(prev)){
				auto newProp=active(new_);
				assert(newProp&&!newProp.componentReplacements.length);
				newProp.componentReplacements=prevProp.componentReplacements;
				prevProp.componentReplacements=[];
				if(newProp.componentReplacements.length) noteReplaced(new_);
				noteAdded(prev);
			}
		}
		private void retire(scope bool delegate(Declaration) live,Declaration[] left){ // (`left`: the declarations that left the table since the last retirement)
			Declaration[] gone,pending;
			if(retireAll||!tracked){
				foreach(decl,ref prop;props){
					if(live(decl)) continue;
					if(!prop.constBlock.length&&!prop.componentReplacements.length) gone~=decl;
					else pending~=decl;
				}
			}else foreach(decl;ordered(added~left,(ref DeclProp p)=>true)){
				auto prop=tryGet(decl);
				if(live(decl)) continue;
				if(!prop.constBlock.length&&!prop.componentReplacements.length) gone~=decl;
				else pending~=decl;
			}
			added=pending;
			retireAll=false;
			if(!gone.length) return;
			if(!retired) retired=new RetiredDeclProps;
			foreach(decl;gone){
				retired.props[decl]=*tryGet(decl);
				indexRetired(decl);
				if(numMoves) removedLog~=q(decl,tryGet(decl).activated);
				props.remove(decl);
			}
			numRemoved+=gone.length;
			if(numRemoved>props.length+16){ // (the entries of a stable map stay where they are)
				MapSX!(Declaration,DeclProp) nprops;
				foreach(decl,ref prop;props) nprops[decl]=prop;
				props=nprops;
				numRemoved=0;
			}
		}
		private void indexRetired(Declaration decl){
			auto vd=cast(VarDecl)decl;
			if(!vd||!vd.vtype) return;
			foreach(id;vd.vtype.freeIdentifiers)
				if(id.meaning&&!retired.typeMentions.get(id.meaning,null).canFind!(d=>d is decl))
					retired.typeMentions[id.meaning]~=decl;
		}
		private Declaration[] retiredMentioning(Declaration decl){
			if(snapshot||!retired) return null;
			return retired.typeMentions.get(decl,null).filter!(d=>tryGetRetired(d)&&!tryGet(d)).array;
		}
	}
	final DeclProps saveDeclProps(){ return declProps.dup; }
	final void resetDeclProps(DeclProps previous){
		auto retired=declProps.retired;
		declProps=previous;
		declProps.retireAll=true;
		declProps.retired=retired;
		declProps.snapshot=false;
		if(retired) foreach(decl,ref _;declProps.props) retired.props.remove(decl); // (retired after the snapshot)
	}
	final void afterStatement(){
		// (the properties of a declaration that is no longer live only matter when its accesses are renamed or retyped, or when a use of a version that it derives from is cancelled)
		auto tracked=restrictsToChanges();
		if(tracked&&!declProps.tracked) declProps.retireAll=true;
		declProps.tracked=tracked;
		declProps.retire((Declaration decl)=>!decl.scope_||(decl.scope_ is this?rnsymtab.get(decl.getId,null) is decl:!decl.scope_.isNestedIn(this)),leftTable);
		leftTable=null;
		// (no later statement refers to a temporary that the statement consumed)
		foreach(cd;consumedTemporaries){
			if(symtab.get(cd.name.id,null) is cd) symtab.remove(cd.name.id);
			if(rnsymtab.get(cd.getId,null) is cd){
				rnsymtab.remove(cd.getId);
				if(isRenamedDead(cd)) numRenamedDead--;
				if(sinceMergeLogged&&dependencyTracked(cd)) removedTracked~=cd;
				if(declProps.tracked) leftTable~=cd;
			}
		}
		consumedTemporaries=[];
	}
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
		return declProps.active(decl);
	}
	final void recordAccess(Identifier id,Declaration meaning){
		if(id.typeofSuppressedCapture) return;
		if(!meaning.isToplevelDeclaration()&&!meaning.isAggregateMember()){
			lastUses.pin(meaning,false); // previous last use cannot be used to forget anymore
			static if(language==silq) pinTypeMentions(meaning); // (as are the variables that its type mentions)
			if(!id.constLookup&&!id.implicitDup)
				lastUses.consumption(meaning,id,this); // TODO: ok?
			declProps.history(meaning).accesses~=id;
		}
	}
	static if(language==silq)
	final void pinTypeMentions(Declaration meaning){ // (the variables that the type of `meaning` mentions are live where it is used)
		import ast.semantic_: typeForDeclNoAnalyze;
		if(auto type=typeForDeclNoAnalyze(meaning)) pinMentions(type);
	}
	static if(language==silq)
	final void pinMentions(Expression type){ // (the variables that `type` mentions are live here, also through the values of type variables, e.g., `n` for `x:a` after `a:=𝔹^n`, see `unfoldTypeVariables`)
		void pin(Expression t){
			foreach(fid;t.freeIdentifiers){
				auto decl=fid.meaning;
				if(!decl||decl.isToplevelDeclaration()||decl.isAggregateMember()) continue;
				lastUses.pin(getSplit(decl),false);
				if(auto cur=sameValueVersion(decl)) lastUses.pin(getSplit(cur),false); // (e.g., `n` for `x` after `do{ n:=dup(m); b:=𝔹^n; a:=b; x:=x coerce a; }while c;`: the value of the version of `b` after the loop mentions the version of `n` in the body)
			}
		}
		pin(type);
		auto unfolded=unfoldTypeVariables(type);
		if(unfolded !is type) pin(unfolded);
	}
	static if(language==silq)
	private final Declaration sameValueVersion(Declaration decl){ // (the version of the variable of `decl` here, if it has the same value, see `unavailableAt`)
		for(Scope c=this;c;c=c.parentScope()){
			if(auto cur=c.rnsymtab.get(decl.getId,null)) return cast(DeadDecl)cur||cur.canonicalSource !is decl.canonicalSource?null:cur;
			if(c is decl.scope_) return null;
		}
		return null;
	}
	final void recordCapturer(Declaration capturer,Declaration meaning){
		if(!meaning.isToplevelDeclaration){
			declProps.history(meaning).capturers~=capturer;
		}
	}
	final void recordCapturers(Expression type){ // (the closures in a type whose uses are recorded as accesses: their captures are renamed with the uses, e.g., to later splits)
		foreach(se;type.subexpressions){
			FunctionDef fd;
			if(auto le=cast(LambdaExp)se) fd=le.fd;
			else fd=cast(FunctionDef)se;
			if(!fd) continue;
			foreach(decl;fd.capturedDecls) recordCapturer(fd,decl);
			if(fd.body_) recordCapturers(fd.body_);
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
		recordAccess(cid,decl); // (renamed with the other accesses, e.g., to a split of `decl`, as for the const blocks of `mergeDeclProps`)
	}
	final void blockConst(Declaration decl,Identifier constBlock){
		if(!decl.isToplevelDeclaration){
			if(auto props=updateDeclProps(decl))
				props.constBlock~=constBlock;
			declProps.noteBlocked(decl);
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
		if(auto declProp=declProps.tryGetAny(decl)) accesses=declProp.accesses;
		if(use&&use.scope_ !is this) // (all accesses here are after `use`, also those of versions split from `decl` in nested scopes)
			foreach(e;declProps.inOrder) if(e[0] !is decl&&e[0].isDerivedFrom(decl)) accesses~=e[1].accesses;
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
				foreach(e;nsc.declProps.inOrder){
					if(origin(e[0]) !is origin(decl)) continue;
					foreach(access;e[1].accesses) if(!access.isSemError()) reportLater(access,nsc);
				}
				visitActive(nsc);
			}
		}
		for(auto inner=cast(NestedScope)this;inner;inner=cast(NestedScope)inner.parent){
			auto outer=inner.parent;
			if(!outer||outer.getFunction() !is getFunction()) break;
			if(!outer.activeNestedScopes.canFind(inner)) visitActive(outer);
			DeclProp* prop=null;
			for(auto d=decl;d&&!prop;d=d.splitFrom) prop=outer.declProps.tryGetAny(d);
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
			if(!tt.dep.isTop){ // nothing to do for recomputable temporaries
				if(!cast(Identifier)tt.expr) noteRecomputedTemporary(tt.dep);
				continue;
			}
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
	final Declaration[] constBlocked(){ // (a superset of the declarations that `isConst` holds for)
		Declaration[] r;
		foreach(ref props;&nestedDeclProps) r~=props.blocked;
		return r;
	}
	final void inheritConstBlocks(Declaration prev,Declaration new_){ // new_ replaces prev, so it inherits prev's active const blocks
		foreach(ref props;&nestedDeclProps){
			bool done=false;
			for(auto d=prev;d&&!done;d=d.splitFrom)
				if(auto prop=props.tryGet(d))
					if(prop.constBlock.length){
						props.active(new_).constBlock~=prop.constBlock;
						props.noteBlocked(new_);
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
		foreach(decl;declProps.withConstBlocks()) constBlock[decl]=declProps.tryGet(decl).constBlock;
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
		Declaration[] versions(Declaration decl){ // (with properties, also those split from it, in the order of the properties)
			Declaration[] r;
			SetX!Declaration seen;
			void visit(Declaration d){
				if(d in seen) return;
				seen.insert(d);
				r~=d;
				foreach(s;d.splitInto) visit(s);
			}
			visit(decl);
			return declProps.ordered(r,(ref DeclProp p)=>true);
		}
		Declaration lookupCurrent(Declaration decl){
			if(declProps.tryGet(decl)) return decl;
			auto r=versions(decl);
			return r.length?r[0]:null;
		}
		auto affected=declProps.withConstBlocks(); // (the others keep their empty `const` blocks)
		foreach(decl,_;context.constBlock) affected~=versions(decl);
		foreach(decl;declProps.ordered(affected,(ref DeclProp p)=>true)){
			auto prop=declProps.tryGet(decl);
			auto nconstBlock=lookupSnapshot(decl);
			if(prop.constBlock.length&&prop.constBlock!=nconstBlock){
				auto reads=prop.constBlock;
				recordOuterConstReads(decl,reads.filter!(read=>!nconstBlock.canFind(read)));
				prop.constBlock=nconstBlock; // (the forget after the last use follows the reads that end here, e.g., both in `t⊕t`)
				if(nconstBlock.length) declProps.noteBlocked(decl);
				recordResetConst(decl,reads[$-1],parent,isStatement,inType);
			}
			prop.constBlock=nconstBlock;
			if(nconstBlock.length) declProps.noteBlocked(decl);
			else declProps.noteAdded(decl);
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
		foreach(decl;declProps.withConstBlocks()){
			auto prop=declProps.tryGet(decl);
			if(prop.constBlock.length){
				auto reads=prop.constBlock;
				recordOuterConstReads(decl,reads);
				prop.constBlock=[];
				declProps.noteAdded(decl);
				recordResetConst(decl,reads[$-1],parent,isStatement,inType);
			}
		}
		auto success=checkTrackedTemporaries(trackedTemporaries,parent);
		trackedTemporaries=[];
		componentConstBlocks=[];
		return success;
	}
	final void resetLocalComponentReplacements(){
		foreach(decl;declProps.withReplacements()){
			declProps.tryGet(decl).componentReplacements=[];
			declProps.noteAdded(decl);
		}
	}
	final DeclProp.ComponentReplacement[] localComponentReplacements(){
		typeof(return) r;
		foreach(decl;declProps.withReplacements())
			r~=declProps.tryGet(decl).componentReplacements;
		return r;
	}
	final DeclProp.ComponentReplacement[][] localComponentReplacementsByDecl(){
		Declaration[] decls;
		typeof(return) r;
		foreach(decl;declProps.withReplacements()){
			decls~=decl;
			r~=declProps.tryGet(decl).componentReplacements;
		}
		sort!"a[0].getName<b[0].getName"(zip(decls,r));
		return r;
	}
	DeclProp.ComponentReplacement*[] allComponentReplacements(){ // TODO: get rid of this?
		typeof(return) r=[];
		foreach(ref props;&nestedDeclProps){
			foreach(decl;props.withReplacements()){
				auto prop=props.tryGet(decl);
				r~=iota(prop.componentReplacements.length).map!(i=>&prop.componentReplacements[i]).array;
			}
		}
		return r;
	}
	final DeclProp.ComponentReplacement*[] componentReplacements(Declaration decl){ // TODO: get rid of this?
		typeof(return) r=[];
		foreach(ref prop;nestedDeclProp(decl))
			r~=iota(prop.componentReplacements.length).map!(i=>&prop.componentReplacements[i]).array;
		return r;
	}
	// the component replacements of the versions of the aggregate that `decl` derives from, which also apply to it (through
	// splits, merges, promotions and writes of other components, e.g., to `x` after `x[2]:=X(x[2]);` in the body of
	// `with{ t:=x[1]; }do{ … }`), with the versions they are registered for
	final Q!(Declaration,DeclProp.ComponentReplacement*)[] versionComponentReplacements(Declaration decl){
		typeof(return) r=[];
		if(!decl.replacementVersions.length){ // (the versions of one chain of splits are distinct)
			for(auto d=decl;d;d=d.splitFrom) foreach(crepl;componentReplacements(d)) r~=q(d,crepl);
			return r;
		}
		Declaration[] visited;
		void add(Declaration version_){
			for(auto d=version_;d;d=d.splitFrom){ // (the replacements may move to a split, see `DeclProps.replaceDecl`)
				if(visited.canFind(d)) continue;
				visited~=d;
				foreach(crepl;componentReplacements(d)) r~=q(d,crepl);
			}
		}
		add(decl);
		foreach(version_;decl.replacementVersions) add(version_);
		return r;
	}
	final void deriveVersion(Declaration from,Declaration into){ // (`into` is a version of the aggregate `from`, see `versionComponentReplacements`)
		void add(Declaration version_){
			if(componentReplacements(version_).length&&!into.replacementVersions.canFind(version_)) into.replacementVersions~=version_; // (e.g., not the versions of the earlier writes of components that have completed)
		}
		foreach(version_;from.replacementVersions) add(version_);
		add(from);
	}
	final DeclProp.ComponentReplacement* blockingComponentReplacement(Declaration decl){
		auto blocking=versionComponentReplacements(decl).find!(vcrepl=>vcrepl[1].blocksAggregate);
		return blocking.empty?null:blocking.front[1];
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
	static struct ComponentReplacementContext{ // (of the declarations whose properties were active, in the order of the properties: only the nonempty ones, see `restoreLocalComponentReplacements`)
		private MapX!(Declaration,Q!(size_t,DeclProp.ComponentReplacement[])) componentReplacements; // (with `DeclProp.activated`)
		private size_t numActivated,numRetired; // (at the move; `numRetired`: the length of `DeclProps.removedLog`)
		bool empty(){ return !componentReplacements.length; }
	}
	final ComponentReplacementContext moveLocalComponentReplacements(){ // TODO: get rid of this
		MapX!(Declaration,Q!(size_t,DeclProp.ComponentReplacement[])) r;
		foreach(decl;declProps.withReplacements()){
			auto prop=declProps.tryGet(decl);
			r[decl]=q(prop.activated,prop.componentReplacements);
			prop.componentReplacements=[];
			declProps.noteAdded(decl);
		}
		if(!declProps.numMoves++) declProps.removedLog=null;
		return typeof(return)(r,declProps.numActivated,declProps.removedLog.length);
	}
	final void isolateComponentReplacements(){ // TODO: this is a bit hacky
		foreach(decl;declProps.withReplacements()){
			auto prop=declProps.tryGet(decl);
			prop.componentReplacements=prop.componentReplacements.dup;
		}
	}
	final void restoreLocalComponentReplacements(ComponentReplacementContext previous){ // TODO: get rid of this
		// (as for all properties that were active at the move, in their order: those with replacements then, and those that are empty now or still retired are not changed)
		Q!(size_t,Declaration,DeclProp.ComponentReplacement[])[] todo;
		foreach(decl,e;previous.componentReplacements) todo~=q(e[0],decl,e[1]);
		auto log=declProps.removedLog;
		if(previous.numRetired<=log.length) foreach(e;log[previous.numRetired..$]){ // (active at the move, then retired or renamed: activated again or recorded anew, or emptied)
			if(e[0] in previous.componentReplacements||e[1]>previous.numActivated) continue;
			todo~=q(e[1],e[0],cast(DeclProp.ComponentReplacement[])null);
		}
		foreach(d;declProps.withReplacements()){ // (emptied)
			if(d in previous.componentReplacements) continue;
			if(auto p=declProps.tryGet(d)) if(p.activated<=previous.numActivated) todo~=q(p.activated,d,cast(DeclProp.ComponentReplacement[])null);
		}
		sort!"a[0]<b[0]"(todo);
		SetX!Declaration seen;
		foreach(t;todo){
			if(t[1] in seen) continue;
			seen.insert(t[1]);
			updateDeclProps(t[1]).componentReplacements=t[2];
			if(t[2].length) declProps.noteReplaced(t[1]);
			else declProps.noteAdded(t[1]);
		}
		if(declProps.numMoves) declProps.numMoves--;
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
		if(canInsert(cd.name.id)){
			symtabInsert(cd);
			if(decl.scope_ is this){
				auto vd=cast(VarDecl)decl;
				if(vd&&vd.isTemporary||consumedTemporaries.any!(t=>t.name.id==decl.name.id)) consumedTemporaries~=cd; // (also a later version, e.g., the component of an index replacement)
			}
		}
		return cd;
	}
	private ConsumedDecl[] consumedTemporaries; // (in the current statement, see `afterStatement`)
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
		deriveVersion(splitFrom,splitInto);
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
		lastUses.prepareChange(splitFrom);
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
		foreach(d;typeMentioning()) retype(d); // (the others have types without variables)
		foreach(d,ref prop;declProps.props) retype(d);
		foreach(d;declProps.retiredMentioning(splitFrom)){
			retype(d);
			declProps.indexRetired(d);
		}
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
		if(auto prop=declProps.tryGetAny(decl)){
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
		lastUses.prepareChange(odecl);
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
		dependency.replace(removed,dependencies.get(removed));
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
	static if(language==silq) final Scope typeBoundary(){ // (also of a closure within a type, e.g., for a variable that it captures after the first consumption in it failed)
		if(auto r=letTypeBoundary()) return r;
		if(auto fd=getFunction()) return fd.typeBoundary;
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
		static if(language==silq) if(consumesOutsideType(meaning,typeBoundary())){ // (e.g., `forget(x)` in a `let` expression within a type)
			if(!id.isSemError()) error(format("cannot consume `%s` in a type",meaning.name),id.loc);
			meaning.setSemForceError(); // (as below, e.g., for a parameter that its own type consumes, whose last uses are not tracked yet)
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
		return lookupHereFrom(ident,rnsym,origin,failures);
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
	protected final Declaration lookupHereFrom(Identifier ident,bool rnsym,Scope origin,DeadDecl[]* failures){
		auto r=lookupHereImpl(ident,rnsym,failures);
		if(r&&!rnsym&&origin&&r.scope_){
			for(Scope sc=origin;sc;sc=sc.parentScope()){ // (the consumption can be in a scope nested in the declaring one: it records them, see `noteDeadOnPath`)
				foreach(e;sc.deadOnPaths){
					if(e[0] !is r) continue;
					auto csc=e[3].scope_;
					if(!origin.isNestedIn(csc)&&!csc.isNestedIn(origin)||origin is sc&&csc !is sc&&!e[4]) continue; // (after the consumption on its path; the merge decides about the variables of this scope)
					if(failures){
						auto dd=new OutOfScopeDecl(r,e[1],e[3],e[2]);
						dd.scope_=r.scope_;
						dd.setSemCompleted();
						*failures~=dd;
					}
					return null;
				}
				if(sc is r.scope_) break;
			}
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
		static if(is(T==ReturnExp)){
			auto dropsClassical=dropsClassicalAtReturn();
			bool dropped(Declaration d){ return dropsClassical&&d.scope_ !is this&&isClassicalValue(d); } // (forgetting it has no effect, while consuming it would split it into the other branches; dropping it does not change what blocks the others)
			if(dropsClassical) returnDropped=true;
			if(dropsClassical&&logSinceNesting&&rnsymtab.isLogging) pending=rnsymtab.liveValues(SymbolProperty.notFixedClassical,rnsymtab.changeLog,SymbolProperty.live); // (the others are classical variables from outside, which are dropped: those of this scope are among its changes)
			else pending=rnsymtab.liveValues();
		}else{
			static bool dropped(Declaration d){ return false; }
			pending=rnsymtab.liveValues();
		}
		SetX!Declaration blockedAtStart; // (forgotten after the live variables whose types mention them, e.g., `n` after `y:=vector(n,0:!𝔹)`)
		foreach(d;pending) if(!cast(DeadDecl)d&&!d.isSemError()&&!dropped(d)&&typeConstBlocked(d,this)) blockedAtStart.insert(d);
		for(bool deferBlocked=true,firstPass=true;pending.length;firstPass=false){
			Declaration[] blocked;
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
				if(dropped(d)) continue;
				if(deferBlocked&&(firstPass&&d in blockedAtStart||typeConstBlocked(d,this))){
					blocked~=d;
					continue;
				}
				// (a blocked variable is forgotten here, after the variables whose types mention it, rather than at its last use,
				// which may precede their forgets, e.g., `n` at the end in `x:=vector(n,0:𝔹); if c { return 0; } else { m:=x.length;
				// for i in 0..2 { y:=vector(n,0:𝔹); } } return 1;`, which forgets `x`)
				if(!(d in blockedAtStart?canForgetAppend(loc,d,false)||canForgetAppend(loc,d):canForgetAppend(loc,d))){
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
	bool returnDropped=false; // (a `return` dropped the classical variables from outside, which the unreachable code after it cannot use, see `hiddenAfterReturn`)
	final bool hiddenAfterReturn(Declaration d){
		return returnDropped&&d.scope_&&d.scope_ !is this&&d.scope_.getFunction() is getFunction()&&isClassicalValue(d);
	}
	private bool dropsClassicalAtReturn(){ // (a `return` in a branch outside of loops and other nested scopes: the branch diverges)
		for(Scope s=this;;){
			auto bs=cast(BlockScope)s;
			if(!bs) return false;
			auto p=bs.parentScope();
			if(cast(FunctionScope)p) return s !is this;
			if(!bs.isBranch||bs.returningConditional) return false;
			s=p;
		}
	}
	static bool isClassicalValue(Declaration d){
		if(!cast(VarDecl)d) return false;
		import ast.semantic_: typeForDecl;
		auto type=typeForDecl(d);
		return type&&!hasQuantumComponent(type);
	}

	bool diverges=false;
	bool quantumControlled=false;
	bool allowMerge=false;
	private bool sinceMergeLogged; // (whether `removedTracked`, `consumedLogged` and the log of `dependencies` from `depsMark` hold all changes since the last merge, also of the enclosing scopes before the nestings, see `MergeKeys`)
	private bool logSinceNesting; // (whether the logs of `rnsymtab` and `dependencies` hold all changes since the nesting, see `MergeKeys`)
	bool dependenciesMerged=false; // (after a merge, the dependencies of a nested scope are those of the scope it was merged into)
	final bool closeUnreachable(Scope mergeScope,Scope consumptionScope=null,Mentions mentions=null){ // (`mentions`: the variables from outside that the branch mentions, the others are not split into it, e.g., for `if c { assert(false); }`)
		bool dropped(Declaration d){ return mentions&&d.scope_&&d.scope_ !is this&&!mentions(d); }
		Id[] candidates; // (the variables that it does not drop: those that it mentions, and its own, which are among its changes)
		auto restricted=mentions&&logSinceNesting&&rnsymtab.isLogging;
		if(restricted){
			SetX!Id seen;
			foreach(id;chain(mentions.ids,rnsymtab.changeLog)) if(id !in seen){ seen.insert(id); candidates~=id; }
		}
		lastUses.createDeferred((Declaration d)=>!dropped(d),candidates,restricted); // (the last uses of the variables that it drops cannot be observed: they are not split into it)
		clearConsumed();
		activeNestedScopes=[];
		allowMerge=false;
		diverges=true;
		if(!consumptionScope) consumptionScope=mergeScope;
		CloseAction action(Declaration d){
			if(dropped(d)) return CloseAction.remove; // (the conditional abort leaves it unsplit, as `assert` does, so that the backend can still uncompute values that depend on it at their last uses, e.g., `o:=dup(x)` in `if c { assert(false); } forget(o);`)
			if(d.isLinear()&&(!consumptionScope||!d.scope_||d.scope_.isNestedIn(consumptionScope))||d.scope_ is this){ // (variables of scopes that enclose the merge are not split into the branch, e.g., through the scope of a `let` expression)
				if(auto p=cast(Parameter)d) if(p.isConst) return CloseAction.keep;
				return CloseAction.consume;
			}
			return CloseAction.remove;
		}
		if(!mentions||!closeChanged(mentions,&action)){
			// (a variable is consumed before the variables that its dependency mentions: consuming a variable from outside of the
			// branch splits it into the other branches, where the variables that are not split yet would lose their dependency on it)
			Declaration[] decls;
			size_t[const(void)*] index;
			foreach(d;rnsymtab.liveValues()){
				index[cast(const(void)*)d]=decls.length;
				decls~=d;
			}
			size_t[] mentioned(Declaration d){ // (the variables of the scope that the dependency of `d` mentions)
				for(Scope sc=this;sc;sc=sc.parentScope()){
					if(!sc.dependencyTracked(d)) continue;
					auto dep=sc.dependencies.get(d);
					size_t[] r;
					if(!dep.isTop) foreach(x;dep.dependencies) if(auto j=cast(const(void)*)x in index) if(decls[*j] !is d) r~=*j;
					return r;
				}
				return null;
			}
			auto dependents=new size_t[](decls.length);
			foreach(d;decls) foreach(j;mentioned(d)) dependents[j]++;
			Declaration[] ordered;
			auto done=new bool[](decls.length);
			for(bool progress=true;progress;){
				progress=false;
				foreach(i,d;decls){
					if(done[i]||dependents[i]) continue;
					done[i]=true;
					progress=true;
					ordered~=d;
					foreach(j;mentioned(d)) dependents[j]--;
				}
			}
			foreach(i,d;decls) if(!done[i]) ordered~=d;
			foreach(d;ordered){
				final switch(action(d)){
					case CloseAction.remove: symtabRemove(d); break;
					case CloseAction.keep: break;
					case CloseAction.consume:
						consume(d,null);
						clearConsumed();
						break;
				}
			}
		}
		if(mergeScope){
			if(auto fsc=cast(FunctionScope)this) foreach(decl;fsc.fd.capturedDecls) mergeScope.recordCapturer(fsc.fd,decl); // (the merged uses of the captured variables are renamed with the captures, e.g., uses with meanings from a copy)
			mergeScope.mergeDeclProps(this.declProps,this.componentConstBlocks);
		}
		return false;
	}
	private enum CloseAction{ remove, keep, consume }
	private bool closeChanged(Mentions mentions,scope CloseAction delegate(Declaration) action){ // (as `closeUnreachable` for a branch, if it consumes nothing: only the entries that changed since the nesting or that the branch mentions stay, the others are dropped at once; `false` if it would consume something, or if the changes are not known)
		auto bs=cast(BlockScope)this;
		if(!bs||!bs.isBranch||!logSinceNesting||!rnsymtab.isLogging) return false;
		Id[] ids;
		SetX!Id seen;
		foreach(id;chain(rnsymtab.changeLog,mentions.ids)) if(id !in seen){ seen.insert(id); ids~=id; }
		Declaration[] removed;
		foreach(id;ids){
			auto d=rnsymtab.get(id,null);
			if(!d||cast(DeadDecl)d) continue;
			final switch(action(d)){
				case CloseAction.remove: removed~=d; break;
				case CloseAction.keep: break;
				case CloseAction.consume: return false;
			}
		}
		foreach(d;removed) symtabRemove(d);
		Q!(size_t,Id)[] kept;
		foreach(id;ids){
			size_t pos;
			if(rnsymtab.tryGetPosition(id,pos)) kept~=q(pos,id);
		}
		sort!"a[0]<b[0]"(kept);
		SymbolTable nrnsymtab,nsymtab;
		numRenamedDead=0;
		foreach(k;kept){
			auto d=rnsymtab[k[1]];
			nrnsymtab[k[1]]=d;
			if(d.name&&symtab.get(d.name.id,null) is d) nsymtab[d.name.id]=d;
			if(isRenamedDead(d)) numRenamedDead++;
		}
		nrnsymtab.startLog(rnsymtab.changeLog);
		rnsymtab=nrnsymtab;
		symtab=nsymtab;
		return true;
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
			auto d=dependencies.get(decl);
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
	// (a temporary is forgotten using its dependencies, also those of the variables it depends on whose earlier implicit
	// duplications are cancelled later, which consumes them before, e.g., `b` in `X(b)` for `(X(b),)` in `b:=(X(b),)[0]` under
	// quantum control, or in `t:=X(b)` before `b:=(X(move(t)),)[0]`)
	final void noteImplicitDup(Identifier use){
		if(!dummyWitnessActive) return;
		foreach(ref context;dummyWitnessContexts) context.dupOrder[use]=++context.order;
	}
	final void noteRecomputedTemporary(Dependency dep){
		if(dep.isTop||!dummyWitnessActive) return;
		noteDependencyResolved(dep);
		SetX!Id ids;
		foreach(decl;dep.dependencies) ids.insert(decl.getId);
		foreach(ref context;dummyWitnessContexts) context.recomputed~=q(++context.order,ids);
	}
	final void noteImplicitDupCancelled(Identifier use,Dependency dep){
		if(!dummyWitnessActive||!use.meaning) return;
		foreach(ref context;dummyWitnessContexts){
			auto order=context.dupOrder.get(use,size_t.max);
			if(context.recomputed.any!(r=>r[0]>order&&use.meaning.getId in r[1])){
				noteReconstructed(dep); // (resolved through the variables consumed later, e.g., `t` for the dependency `{t}` of `b` after `b:=X(t)`)
				return;
			}
		}
	}
	final void noteNestedLoopCarried(SetX!Id ids){
		if(!dummyWitnessActive||!ids.length) return;
		foreach(ref context;dummyWitnessContexts)
			context.nestedLoopCarried~=ids;
	}

	auto controlDependency=Dependency(false,SetX!Declaration.init);
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
		dependencies.remove(decl);
	}
	void addDependencies(scope Q!(Declaration,Dependency)[] deps,bool sourcesTracked=false){
		static if(language==psi) return; // (in PSI, all data is classical: dependencies are not tracked)
		//imported!"util.io".writeln("ADDING: ",deps);
		foreach(i,ref dep;deps){
			assert(!!dep[0]);
			substituteConsumed(dep[1],consumedDepLog);
			if(dependencies.tracked(dep[0])){
				//writeln(dep[0]," ",toRemove," ",dependencies)
				dep[1].remove(dep[0]); // (its previous value is joined, e.g., a replaced component computed from other components)
				dep[1].joinWith(dependencies.get(dep[0]));
				if(!sourcesTracked) dep[0].definitionSources=DefinitionSources.init;
			}
		}
		foreach(decl,dep;deps.map!(x=>x)){
			assert(decl&&!cast(DeadDecl)decl);
			dependencies.set(decl,dep);
		}
	}
	final bool dependencyTracked(Declaration decl){
		static if(language==psi) return true; // (in PSI, all data is classical: dependencies are not tracked)
		return dependencies.tracked(decl);
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
			if(auto dsc=dependencyScope(decl)) if(dsc !is this) return dsc.dependencies.get(decl);
			auto cur=rnsymtab.get(decl.getId,null);
			if(cur&&cur !is decl&&!cast(DeadDecl)cur) return getDefaultDependency(decl);
			static if(language==silq) if(cast(DeadDecl)cur){ // (the variable was consumed here: its dependency is not tracked again)
				if(auto pd=consumedDepLog.getPtr(decl)) return pd.dup;
				return getDefaultDependency(decl);
			}
			addDefaultDependency(decl); // TODO: ideally can be removed
		}
		return dependencies.get(decl);
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
	final void continueDependencies(Declaration decl,Declaration ndecl){ // (`ndecl` has the value of `decl`, which it replaces)
		static if(language==psi) return; // (in PSI, all data is classical: dependencies are not tracked)
		consumedDepLog[decl]=getDependency(decl).dup;
		if(sinceMergeLogged) consumedLogged~=decl;
		dependencies.remove(decl);
		dependencies.replaceInDependencies(decl,ndecl,ndecl);
		controlDependency.replace(decl,ndecl);
		foreach(ref tt;trackedTemporaries) tt.dep.replace(decl,ndecl);
	}
	final void pushDependencies(Declaration decl,bool keep,Identifier consumedAt=null){
		static if(language==psi) return; // (in PSI, all data is classical: dependencies are not tracked)
		consumedDepLog[decl]=getDependency(decl).dup;
		if(sinceMergeLogged) consumedLogged~=decl;
		noteDependencyConsumed(decl,getDependency(decl));
		if(getDependency(decl).isTop){
			bool done=false;
			do{ // TODO: improve
				done=true;
				foreach(ndecl;dependencies.mentioning(decl)){
					auto v=getDependency(ndecl);
					//imported!"util.io".writeln("CHECKING: ",decl," ",ndecl," ",v.dependencies," ",decl in v.dependencies);
					if(decl in v.dependencies){
						if(auto lu=lastUses.get(ndecl,true)){
							auto last=lu;
							while(last.forwardTo) last=last.forwardTo;
							auto keptBy=last.use&&last.use.implicitDup?last:last.kind==LastUse.Kind.lazyMerge&&last.prevImplicitDup&&last.canCancelImplicitDup()?last.prevImplicitDup:null; // (also through the merge of an earlier conditional whose branches do not use it, see `unusedSplitOfImplicitDup`)
							if(lu.forwardTo&&(lu.kind==LastUse.Kind.lazySplitSink||lu.kind==LastUse.Kind.constPinned)&&keptBy&&deferDupCancels()){ // (the value continues into the branches (lazy splitting), which may use it before they consume `decl`, e.g., `y0` for `y1:=y0; if c { z:=H(x); } else { w:=!y0; forget(w); z:=H(x); }`: decided at the merge, see `cancelDeferredDups`; not after a `const` use, e.g., `t:=dup(y0)`, where it is forgotten, as before)
								deferredDupCancels~=q(ndecl,consumingUse);
								noteDeadOnPath(ndecl,keptBy,consumingUse);
								continue;
							}
							if(lu.forwardTo&&deferDupCancels()||last.kind==LastUse.Kind.lazySplit) noteDeadOnPath(ndecl,splitBasis(last),consumingUse); // (e.g., after a `const` use that follows the implicit `dup`, which a branch that uses the variable pins; or the version that a branch has not used yet when it consumes its own version of what it depends on, e.g., when the other branch consumed it before)
							//imported!"util.io".writeln("CHECKING PUSH: ",last," ",last.use?last.use.implicitDup:false);
							if(cancelDup(ndecl,last,consumingUse)) done=false;
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

	private bool cancelDup(Declaration ndecl,LastUse lu,Identifier consumingUse){
		if(!lu.canCancelImplicitDup()) return false;
		if(!consumingUse&&lu.kind==LastUse.Kind.lazyMerge&&!LastUse.canCancelImplicitDupMerge(lu.decl,lu.nestedScopes,false)) return false; // (not when a merge consumes the versions of the branches, e.g., of a variable that a nested conditional merged after a branch returned)
		if(consumingUse) if(auto vd=cast(VarDecl)ndecl) if(!vd.outOfScopeCause){
			vd.outOfScopeCause=consumingUse;
			if(!isConstLocal(vd)&&lu.kind==LastUse.Kind.constUse&&lu.prevImplicitDup)
				vd.outOfScopeDup=lu.prevImplicitDup.use;
		}
		if(consumingUse&&lu.kind==LastUse.Kind.lazyMerge&&lu.prevImplicitDup) if(auto vd=cast(VarDecl)lu.prevImplicitDup.decl) if(!vd.outOfScopeCause) vd.outOfScopeCause=consumingUse; // (cancelled if all branches forget their versions at the split)
		if(!lu.cancelImplicitDup()) return false; // TODO
		assert(lu.isConsumption(),text(lu));
		return true;
	}
	private Q!(Declaration,Identifier)[] deferredDupCancels; // (the variables live at a conditional whose implicit `dup`s a consumption in one of its branches would cancel)
	private Q!(Declaration,Identifier,Identifier,Identifier,bool)[] deadOnPaths; // (the variables that a consumption in a nested scope makes unavailable on its path, also through the variables that depend on them, with the uses whose implicit `dup`s it would cancel, as in straight-line code, e.g., `y0` after `x:=H(x)` in `y1:=y0; if c { x:=H(x); w:=!y0; }`)
	private void forgetDeadSplits(){ // (the versions that this branch does not use and that its consumptions make unavailable on its path: forgotten at the split, also when the other branches return, e.g., `v` for `e:=v; if c { a:=X(a); } else { return (a,e); }`)
		bool returned(Scope sc){ // (the consumption is on a path that returns before the end of this branch)
			for(;sc&&sc !is this;sc=sc.parentScope()) if(sc.diverges) return true;
			return false;
		}
		foreach(e;deadOnPaths){
			if(returned(e[3].scope_)) continue;
			auto cur=rnsymtab.get(e[0].getId,null);
			if(!cur||cast(DeadDecl)cur||cur !is e[0]&&!cur.isSplitFrom(e[0])) continue;
			auto lu=lastUses.here(cur);
			while(lu&&lu.forwardTo&&lu.kind==LastUse.Kind.lazySplitSink) lu=lu.forwardTo; // (also after nested conditionals that do not use it)
			if(!lu||lu.forwardTo||lu.kind!=LastUse.Kind.lazySplit&&lu.kind!=LastUse.Kind.lazyMerge||lu.use||!lastUses.canForget(cur,false,false)) continue;
			foreach(d;only(e[0],cur)) if(auto vd=cast(VarDecl)d) if(!vd.outOfScopeCause) vd.outOfScopeCause=e[3];
			lastUses.forget(cur,false);
			if(!rnsymtab.get(cur.getId,null)) recordConsumption(cur,e[1]); // (explained by the implicit `dup` and the consumption on this path)
		}
	}
	private void dropDeadOnPaths(){ // (those of the nested scopes, at their merge: the merge decides about the variables, see `cancelDeferredDups`)
		if(deadOnPaths.length) deadOnPaths=deadOnPaths.filter!(e=>e[3].scope_ is this||e[4]).array; // (a version whose implicit `dup` is in an enclosing scope stays unavailable)
	}
	private static LastUse splitBasis(LastUse lu){ // (the last use before the split, for a version that the nested scope has not used yet)
		for(;;){
			while(lu.forwardTo) lu=lu.forwardTo;
			if(lu.kind==LastUse.Kind.lazyMerge&&lu.prevImplicitDup&&lu.canCancelImplicitDup()) return lu.prevImplicitDup; // (the merge of an earlier conditional whose branches do not use it, see `unusedSplitOfImplicitDup`)
			if(lu.kind!=LastUse.Kind.lazySplit||!lu.splitFrom) return lu;
			lu=lu.splitFrom;
		}
	}
	private void noteDeadOnPath(Declaration decl,LastUse last,Identifier consumingUse){
		if(!consumingUse||!consumingUse.scope_||!consumingUse.scope_.isNestedIn(this)||!last.use) return;
		if(deadOnPaths.any!(e=>e[0] is decl&&e[3] is consumingUse)) return;
		Identifier dupUse=null;
		if(!last.use.implicitDup){
			if(!last.prevImplicitDup||last.kind!=LastUse.Kind.constUse&&last.kind!=LastUse.Kind.constPinned) return; // (a `const` use after an implicit `dup`)
			if(auto vd=cast(VarDecl)decl) if(!isConstLocal(vd)) dupUse=last.prevImplicitDup.use;
		}
		deadOnPaths~=q(decl,last.use,dupUse,consumingUse,last.scope_ !is this);
		foreach(d;dependencies.mentioning(decl)){
			if(decl !in getDependency(d).dependencies) continue;
			auto lu=lastUses.get(d,true);
			if(!lu) continue;
			noteDeadOnPath(d,splitBasis(lu),consumingUse);
		}
	}
	private bool cancellingDeferredDups;
	private bool deferDupCancels(){
		return !cancellingDeferredDups&&activeNestedScopes.length&&activeNestedScopes.all!(LastUse.isBranch);
	}
	private void cancelDeferredDups(){ // (those of the variables that no branch used, and of the variables that depend on them)
		auto todo=deferredDupCancels;
		deferredDupCancels=[];
		dropDeadOnPaths();
		cancellingDeferredDups=true;
		scope(exit) cancellingDeferredDups=false;
		for(size_t i=0;i<todo.length;i++){
			auto ndecl=todo[i][0];
			auto lu=lastUses.get(ndecl,true);
			if(!lu||lu.kind!=LastUse.Kind.lazySplitSink||!lu.forwardTo) continue; // (a branch uses it: the branches forget their versions before their consumptions)
			auto dependents=dependencies.mentioning(ndecl).dup;
			while(lu.forwardTo) lu=lu.forwardTo;
			if(cancelDup(ndecl,lu,todo[i][1]))
				foreach(d;dependents) todo~=q(d,todo[i][1]);
		}
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
	final bool canForgetAppend(T)(T cause,Declaration decl,bool atLastUse=true)if(is(T==Scope)||is(T==ReturnExp))in{
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
		if(atLastUse&&lastUses.canForget(decl,true,false,earlyReturn)&&!(earlyReturn&&atLoopGuard())){
			lastUses.forget(decl,false,earlyReturn);
			return true;
		}
		if(!canSplit(decl)) return false;
		if(canForget(decl)){
			decl=split(decl,null);
			assert(decl.scope_ is this);
			static if(is(T==Scope)) if(cause.forgottenVars.canFind(decl)) return true; // (e.g., `const` locals are forgotten before merging; a `return` forgets each variable once)
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
		if(auto lu=lastUses.get(decl,true))
			if(auto llu=LastUse.lostDependency(lu)) return explainUnknownDependency(decl,llu.dep);
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
		deriveVersion(mergedFrom,mergedInto);
		mergedVars~=mergedFrom;
	}

	NestedScope[] activeNestedScopes;
	final bool restrictsToChanges(){ return rnsymtab.length>=64; } // (whether the nestings and merges only consider the variables that change, see `MergeKeys` and `LastUses.prepareNesting`: in a small scope, visiting all of them costs less)
	private size_t nestChanges,nestDepsChanges,nestRenamedDead; // (of the enclosing scope at the nesting, see `MergeKeys`)
	private size_t numRenamedDead; // (of the dead declarations in `rnsymtab` whose identifiers are renamed, see `MergeKeys`)
	private size_t nestLogMark; // (the length of the log of `rnsymtab` at the latest nesting)
	private size_t depsMark;
	private Declaration[] removedTracked; // (variables with tracked dependencies that may not be the entries of their identifiers in `rnsymtab`: removed, replaced, merged, or changed in an enclosing scope since its last merge, see `merge`)
	private Declaration[] consumedLogged; // (the variables added to `consumedDepLog`)
	void nest(NestedScope r)in{
		static if(language==silq) assert(allowsLinear());
		assert(r.parent is this);
	}do{
		r.controlDependency.joinWith(controlDependency); // TODO: replace
		r.quantumControlled|=quantumControlled;
		r.dependencies=dependencies.dup;
		r.symtab=symtab.dup;
		r.rnsymtab=rnsymtab.dup;
		if(restrictsToChanges()){ // (the nested scope logs its changes, see `MergeKeys`)
			r.dependencies.startLog();
			r.rnsymtab.startLog();
			r.logSinceNesting=true;
			r.sinceMergeLogged=sinceMergeLogged;
			if(sinceMergeLogged) r.removedTracked=removedTracked~dependencies.changeLog[depsMark..$];
		}
		r.numRenamedDead=r.nestRenamedDead=numRenamedDead;
		r.nestChanges=rnsymtab.numChanges;
		r.nestDepsChanges=dependencies.numChanges;
		r.typeMentioning_=typeMentioning_.dup;
		r.numTypeMentioningAtPrune=numTypeMentioningAtPrune;
		if(!allowMerge){
			if(deferredDupCancels.length) cancelDeferredDups(); // (of nested scopes that were not merged)
			dropDeadOnPaths();
			lastUses.prepareNesting(this);
			nestLogMark=rnsymtab.changeLog.length;
		}
		allowMerge=true;
		activeNestedScopes~=r;
		lastUses.nest(r);
	}

	NestedScope[][] mergedNestedScopes;

	private static final class MergeKeys{ // (the variables that the loops of a merge visit: all, or those whose entries in the tables of the nested scopes changed since the nesting, also during the merge, in the order of the table that a loop visits; the merge does not change the others, except for the positions of dead entries that no nested scope changed)
		bool all;
		private Id[] ids;
		private SetX!Id seen;
		private Q!(SymbolTable*,size_t)[] logs;
		this(Scope sc,NestedScope[] scopes){
			all=sc.handler.nerrors||!sc.restrictsToChanges()||!sc.sinceMergeLogged||scopes.any!(s=>s.parent !is sc||!s.logSinceNesting||!s.rnsymtab.isLogging||!s.dependencies.isLogging||s.nestChanges!=scopes[0].nestChanges||s.nestDepsChanges!=scopes[0].nestDepsChanges||s.nestRenamedDead);
			if(!all) foreach(s;scopes) watch(&s.rnsymtab,true);
		}
		void watch(SymbolTable* table,bool logged){ // (`logged`: also the changes so far)
			auto log=(*table).changeLog;
			if(logged) add(log);
			logs~=q(table,log.length);
		}
		void add(Id[] changed){
			foreach(id;changed) if(id !in seen){ seen.insert(id); ids~=id; }
		}
		bool has(Id id){ return all||id in seen; }
		private void poll(){
			foreach(ref l;logs){
				auto log=(*l[0]).changeLog;
				if(log.length>l[1]) add(log[l[1]..$]);
				l[1]=log.length;
			}
		}
		Id[] changed(){ poll(); return ids; }
		void forEach(SymbolTable order,scope void delegate(Declaration) dg){ // (the entries of `order` whose variables changed so far, also those that change before their turns)
			if(all){ foreach(_,d;order) dg(d); return; }
			poll();
			import std.container.binaryheap: heapify;
			Q!(size_t,Id)[] entries;
			foreach(id;ids){ size_t pos; if(order.tryGetPosition(id,pos)) entries~=q(pos,id); }
			auto queue=heapify!"a[0]>b[0]"(entries); // (by position)
			while(!queue.empty){
				auto cur=queue.front;
				queue.removeFront();
				dg(order[cur[1]]);
				auto n=ids.length;
				poll();
				foreach(id;ids[n..$]){
					size_t pos;
					if(order.tryGetPosition(id,pos)&&pos>cur[0]) queue.insert(q(pos,id));
				}
			}
		}
	}
	final bool merge(bool quantumControl,NestedScope[] scopes...)in{
		assert(scopes.length);
	}do{
		return merge(quantumControl,false,scopes);
	}
	final bool mergeLoop(bool returns,NestedScope forgetScope,NestedScope loopScope,Mentions mentions=null)in{
		assert(equal(activeNestedScopes,only(forgetScope,loopScope)));
	}do{
		if(returns) loopScope.closeUnreachable(this,null,mentions);
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
		if(deferredDupCancels.length) cancelDeferredDups();
		dropDeadOnPaths();
		static if(language==silq) if(!isLoop&&activeNestedScopes.all!(LastUse.isBranch)) foreach(sc;scopes) if(!sc.diverges) sc.forgetDeadSplits();
		bool allUsed;
		auto used=LastUses.prepareMerge(scopes,allUsed);
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
		static if(language==silq) bool continued=scopes.any!((sc){ auto bs=cast(BlockScope)sc; return bs&&bs.diverges&&bs.returningBeforeContinuation; }); // (the code after the conditional continues the other branch, see `NestedScope.continuedLog`)
		if(scopes.any!(sc=>sc.diverges))
			scopes=scopes.filter!(sc=>!sc.diverges).array;
		if(!scopes.length) return false;
		auto keys=new MergeKeys(this,scopes);
		auto numErrors=handler.nerrors;
		SetX!Declaration goneConstLocals; // (the types of the merged variables do not mention them)
		static if(language==silq){
			foreach(sc;scopes){
				if(auto bsc=cast(BlockScope)sc) if(bsc.keepConstLocals) continue;
				keys.forEach(sc.rnsymtab.dup,(Declaration d){
					if(cast(DeadDecl)d||d.isSemError()||!isConstLocal(d)) return;
					if(sc.rnsymtab.get(d.getId,null) !is d) return;
					auto origin=d;
					while(origin.splitFrom) origin=origin.splitFrom;
					if(!origin.scope_||!origin.scope_.isNestedIn(sc)) return;
					if(!sc.canForgetAppend(d)){
						if(!sc.lastUses.betterUnforgettableError(d,sc))
							sc.error(format("`const` variable `%s` cannot be forgotten at the end of its scope",d.getName),d.loc);
						d.setSemForceError();
					}else{
						sc.consume(d,null); // (not merged, e.g., with a variable of the same name in another branch)
						sc.clearConsumed();
						for(auto x=d;x;x=x.splitFrom) goneConstLocals.insert(x);
					}
				});
			}
		}
		symtab=scopes[0].symtab.dup;
		auto log=rnsymtab.changeLog,logged=logSinceNesting&&rnsymtab.isLogging&&scopes[0].logSinceNesting;
		auto oldTable=rnsymtab;
		Id[] changedHere=rnsymtab.isLogging&&nestLogMark<=log.length?log[nestLogMark..$]:null; // (while the nested scopes were analyzed)
		bool leftLogged=rnsymtab.isLogging&&nestLogMark<=log.length;
		if(logged) log~=scopes[0].rnsymtab.changeLog;
		rnsymtab=scopes[0].rnsymtab.dup;
		auto logs=logged||!keys.all||restrictsToChanges(); // (for the enclosing scope or for the next merge)
		if(logs) rnsymtab.startLog(logged?log:null);
		keys.watch(&rnsymtab,false);
		numRenamedDead=scopes[0].numRenamedDead;
		typeMentioning_=scopes[0].typeMentioning_.dup;
		numTypeMentioningAtPrune=scopes[0].numTypeMentioningAtPrune;
		//imported!"util.io".writeln("TO REMOVE: ",toRemove," DEPS: ",dependencies," ",toRemove.map!(t=>!!(t in dependencies.dependencies)));
		MapX!(Declaration,Dependency) carryOverDependencies;
		static if(language==silq) foreach(decl;toRemove) if(dependencyTracked(decl)) carryOverDependencies[decl]=getDependency(decl); // TODO: this is a bit hacky
		Declaration[] depKeys; // (whose entries may change in the loops over the entries of the dependencies below: those that changed since the nesting or the last merge, see `MergeKeys`)
		if(!keys.all){
			depKeys=dependencies.changeLog[depsMark..$]~removedTracked;
			foreach(sc;scopes) depKeys~=sc.dependencies.changeLog~sc.removedTracked;
		}
		auto depLog=dependencies.changeLog;
		if(logged) depLog~=scopes[0].dependencies.changeLog;
		dependencies=scopes[0].dependencies.dup;
		if(logs) dependencies.startLog(logged?depLog:null);
		auto depLogStart=dependencies.changeLog.length;
		logSinceNesting=logged;
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
		Expression unfoldBranchTypeVariables(Expression type){ // (the type variables of the branches stand for their values, which their merged versions do not keep, see `typeVariableValue`)
			static if(language==silq) if(type) return unfoldTypeVariables(type,(Declaration d)=>d.scope_&&scopes.any!(sc=>d.scope_.isNestedIn(sc)));
			return type;
		}
		foreach(sc;scopes) if(auto bs=cast(BlockScope)sc) bs.eagerMerges=null; // (of an earlier analysis)
		SetX!Id eagerIds; // (variables whose versions in the branches have no known dependency in some branch, but values that are merged as well depend on them: those depend on the merged versions instead, which the code generator merges first, see `genEagerMerges` in hqir.d)
		static if(language==silq) if(!isLoop&&scopes.length>1&&scopes.all!(s=>LastUse.interleavable(s)&&!(cast(BlockScope)s).returnsOnSomePath)){
			import ast.semantic_:typeForDecl;
			Q!(Id,Declaration[])[] candidates;
			keys.forEach(scopes[0].rnsymtab,(Declaration d0){
				auto id=d0.getId;
				Declaration[] versions;
				bool dependents=false; // (on a version without a known dependency)
				foreach(s;scopes){
					auto d=s.rnsymtab.get(id,null);
					if(!d||cast(DeadDecl)d||d.isSemError()||!s.dependencyTracked(d)){ versions=null; break; }
					auto ty=typeForDecl(d);
					if(!ty||!isQuantum(ty)||versions.length&&ty!=typeForDecl(versions[0])){ versions=null; break; }
					bool readsOnly=true; // (the values computed from `d` only read it, so they can be recomputed from the merged version, whose reads replace those of `d`, see `genEagerMerges`)
					foreach(k;s.dependencies.mentioning(d)){
						if(k is d) continue;
						auto v=s.dependencies.get(k);
						if(!LastUse.readsSplitAtDefinition(s,d,k,v)) readsOnly=false;
						else if(s.getDependency(d).isTop&&scopes.all!(t=>t.rnsymtab.get(k.getId,null)&&!cast(DeadDecl)t.rnsymtab.get(k.getId,null))) dependents=true; // (merged as well)
					}
					if(!readsOnly){ versions=null; break; }
					versions~=d;
				}
				if(versions.length&&dependents&&!versions.all!(v=>v is versions[0])) candidates~=q(id,versions);
			});
			if(candidates.length) eagerIds=eagerMergeOrder(this,scopes,candidates);
		}
		Expression visibleType(Expression type){ // (a supertype of `type` that does not mention the `const` locals of the branches, as the join with a type in another branch, or `null`)
			type=unfoldBranchTypeVariables(type);
			return goneConstLocals.length?eliminateVariables(type,(Declaration d)=>!!(d in goneConstLocals)):type;
		}
		keys.forEach(rnsymtab.dup,(Declaration psym){
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
				if(scopes.length==1||sym.getId in eagerIds) continueDependencies(sym,var); // (the only branch that reaches the merge, e.g., `o` in `o:=dup(x); if n>0 { assert(false); } forget(o);`, or values computed from it depend on the merged version, see `eagerIds`)
				else pushDependencies(sym,false);
				if(sym.isSemError())
					var.setSemForceError();
				sym=var;
				needMerge=true;
			}
			if(cast(DeadDecl)sym){
				removeOSym(this,sym);
				return;
			}
			auto cur=scopes[0].rnsymtab.get(sym.getId,null);
			if(!cur||cast(DeadDecl)cur){ // (consumed when merging the dependencies of another variable)
				removeOSym(this,sym);
				return;
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
						static if(language==silq) auto uot=unfoldBranchTypeVariables(ot),ust=unfoldBranchTypeVariables(st);
						if(mergeTypeSubst.length){ // compare types after, not before, merging the variables they mention
							if(ot) ot=ot.substitute(mergeTypeSubst);
							if(st) st=st.substitute(mergeTypeSubst);
							static if(language==silq){
								if(uot) uot=uot.substitute(mergeTypeSubst);
								if(ust) ust=ust.substitute(mergeTypeSubst);
							}
						}
						static if(language==silq) if(uot&&ust&&(uot !is ot||ust !is st)&&joinTypes(uot,ust)){ // (the type variables of the branches stand for their values if that joins the types, e.g., `x:w` after `w:=𝔹^3` in one branch and `w:=𝔹^n` in the other, whose merged version does not keep a value, see `typeVariableValue`; otherwise, the merged version keeps them apart, e.g., `a:T` after `T:=!𝔹` in one branch and `T:=!ℚ` in the other)
							ot=uot;
							st=ust;
						}
						bool trivialSplit=sym.canonicalSource is osym.canonicalSource;
						if(ot&&st){
							if(quantumControl&&!trivialSplit){ // automatically promote to quantum if possible
								if(auto qt=ot.getQuantum)
									ot=qt;
								if(isEmpty(ot)) if(auto qt=st.getQuantum) st=qt; // (e.g., the version after an erroneous assignment)
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
						if(sym.getId in eagerIds){
							if(auto bs=cast(BlockScope)sc) bs.eagerMerges~=sym;
							sc.continueDependencies(osym,sym);
						}else sc.pushDependencies(osym,false);
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
		});
		if(mergeTypeSubst.length) foreach(sym;producedOuter[numProducedOuter..$]){ // (the types of the merged variables mention the merged versions, independently of the order of merging)
			auto vd=cast(VarDecl)sym;
			if(vd&&vd.vtype&&vd.scope_ is this) vd.vtype=vd.vtype.substitute(mergeTypeSubst);
		}
		static if(language==silq) if(scopes.length==1&&!continued){ // (versions merged after branches that diverge do not depend on each other, as for merges of several branches: the backend uncomputes a value right after its last use, here its merge, which comes after the splits of the others, e.g., of `x` for `o:=dup(x)` in `if c { y:=x&o; forget(y); assert(false); } forget(o);`)
			auto merged=producedOuter[numProducedOuter..$];
			foreach(m;merged) if(dependencyTracked(m)){
				auto dep=getDependency(m).dup;
				foreach(i;0..merged.length){
					if(dep.isTop||!merged.any!(n=>n !is m&&n in dep.dependencies)) break;
					foreach(n;merged) if(n !is m&&n in dep.dependencies) dep.replace(n,getDependency(n));
				}
				if(merged.any!(n=>n in dep.dependencies)) dep=Dependency(true);
				dependencies.set(m,dep);
			}
		}
		SetX!Declaration forgotten; // (or not consumed, after an error)
		if(handler.nerrors!=numErrors) keys.all=true;
		for(bool changed=true;changed;){ // (consumed in a branch when merging the dependencies of another variable, after it was merged, or when forgetting another variable)
			changed=false;
			keys.forEach(rnsymtab.dup,(Declaration sym){
				if(cast(DeadDecl)sym){ // (before it was split into the branches: its versions in the other branches are forgotten below)
					symtabRemove(sym);
					return;
				}
				if(!scopes.any!(sc=>!!cast(DeadDecl)sc.rnsymtab.get(sym.getId,null))) return;
				addDeadMerge(sym);
				symtabRemove(sym);
				foreach(sc;scopes) if(sc.mergedVars.any!(d=>d.mergedInto is sym)) sc.mergedVars=sc.mergedVars.filter!(d=>d.mergedInto !is sym).array; // (not merged after all: the versions that are not consumed are forgotten below)
				if(dependencyTracked(sym)) pushDependencies(sym,false);
				changed=true;
			});
			foreach(sc;scopes){
				keys.forEach(sc.rnsymtab.dup,(Declaration sym){
					if(sc.rnsymtab.get(sym.getId,null) !is sym) return; // (consumed when pushing the dependencies of another variable)
					if(cast(DeadDecl)sym||sym.getId in rnsymtab||sym in forgotten) return;
					if(sym.isSemError()&&(!sym.scope_||!isNestedIn(sym.scope_))) return; // (see below)
					if(sym.scope_ !is sc&&sym.isSemError()){ // (not split into `sc` after an error in another branch)
						sc.symtabRemove(sym);
						return;
					}
					if(sym.scope_ !is this&&sym.scope_ !is sc) if(auto cur=getSplit(sym)) if(cur.scope_ is this){ // (split into this scope after the branches started, e.g., when a branch of an enclosing conditional consumed it while merging, see `LastUse.consume`)
						sc.symtabRemove(sym);
						sc.reinsert(cur);
						sc.replaceDecl(sym,cur);
						sym=cur;
					}
					sym=sc.split(sym,null);
					forgotten.insert(sym);
					if(!sc.canForgetAppend(sym)&&!consumedByError(sym.getId)){
						error(format("variable `%s` is not consumed", sym.getName), sym.loc);
						sc.explainUnforgettable(sym);
						errors=true;
					}
					if(sc.dependencyTracked(sym))
						sc.pushDependencies(sym,false);
					changed=true;
				});
			}
		}
		if(handler.nerrors!=numErrors) keys.all=true;
		if(!keys.all) foreach(id;deadMergeIds(keys,scopes,deadMerges)) keys.add([id]);
		foreach(sc;scopes){
			keys.forEach(sc.rnsymtab.dup,(Declaration sym){
				if(sc.rnsymtab.get(sym.getId,null) !is sym) return; // (consumed when pushing the dependencies of another variable)
				if(sym.isSemError()&&(!sym.scope_||!isNestedIn(sym.scope_))){
					// TODO: why needed?
					sym.scope_=this;
					return;
				}
				if(auto dd=cast(DeadDecl)sym){
					auto dm=addDeadMerge(sym);
					static if(language==silq) bool force=!!cast(EarlyForgottenDecl)dd||!!cast(IllegalConsumedDecl)dd;
					else bool force=false;
					if(force||dm.mergedFrom.all!(d=>cast(DeadDecl)d))
					   dm.mergedFrom~=dd;
					assert(sym.getId !in rnsymtab||cast(DeadDecl)rnsymtab[sym.getId]);
				}
			});
		}
		Declaration[] changedDeps;
		MapX!(void*,bool) changedDepsSeen;
		size_t[] depCursors; // (in the logs below)
		Declaration[] changedDependencies(){ // (the variables whose entries in the dependencies may differ from those at the nesting or after the last merge, see `MergeKeys`)
			void add(Declaration[] ds){
				foreach(d;ds){
					auto k=cast(void*)d;
					if(k in changedDepsSeen) continue;
					changedDepsSeen[k]=true;
					changedDeps~=d;
				}
			}
			if(!depCursors.length){
				add(depKeys);
				depCursors=new size_t[](2+2*scopes.length);
				depCursors[0]=depLogStart;
			}
			void poll(size_t i,Declaration[] log){
				if(log.length>depCursors[i]) add(log[depCursors[i]..$]);
				depCursors[i]=log.length;
			}
			poll(0,dependencies.changeLog);
			poll(1,removedTracked);
			foreach(j,sc;scopes){
				poll(2+2*j,sc.dependencies.changeLog);
				poll(3+2*j,sc.removedTracked);
			}
			return changedDeps;
		}
		foreach(sc;scopes[1..$]){
			if(keys.all) dependencies.joinWith(sc.dependencies);
			else dependencies.joinWithKeys(sc.dependencies,changedDependencies());
		}
		foreach(sc;scopes){ // TODO: needed?
			foreach(decl,ref dep;sc.consumedDepLog){
				if(decl !in consumedDepLog){
					consumedDepLog[decl]=dep;
					if(!keys.all) consumedLogged~=decl;
				}
			}
		}
		void substituteAllConsumed(){
			if(keys.all) dependencies.update((Declaration k,ref Dependency v){ substituteConsumed(v,consumedDepLog); });
			else{
				auto ks=changedDependencies().dup;
				foreach(x;consumedLogged) ks~=dependencies.mentioning(x);
				dependencies.updateKeys((Declaration k,ref Dependency v){ substituteConsumed(v,consumedDepLog); },ks);
			}
		}
		substituteAllConsumed();
		Declaration[] nonCurrent;
		foreach(k;keys.all?dependencies.keys:changedDependencies()){
			if(k.getId !in rnsymtab){
				if(dependencyTracked(k))
					removeDependency(k);
			}else if(dependencies.isLogging&&dependencyTracked(k)&&rnsymtab[k.getId] !is k) nonCurrent~=k; // (stale when its identifier is removed)
		}
		depsMark=dependencies.changeLog.length;
		removedTracked=nonCurrent;
		sinceMergeLogged=dependencies.isLogging;
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
			sc.rnsymtab.stopLog();
			sc.dependencies.stopLog();
			sc.dependencies.clear();
			sc.dependenciesMerged=true;
		}
		if(keys.all){
			foreach(k,v;symtab) assert(this.isNestedIn(v.scope_),text(v));
			foreach(k,v;rnsymtab) assert(this.isNestedIn(v.scope_),text(v));
		}else foreach(id;keys.changed) if(auto v=rnsymtab.get(id,null)){
			assert(this.isNestedIn(v.scope_),text(v));
			if(auto w=symtab.get(v.name.id,null)) assert(this.isNestedIn(w.scope_),text(w));
		}
		foreach(decl,ref dep;carryOverDependencies){
			if(!dependencies.tracked(decl))
				dependencies.set(decl,dep);
		}
		if(keys.all||allUsed) lastUses.merge(isLoop,this,scopes);
		else{
			Q!(size_t,Declaration)[] ordered;
			SetX!Declaration seen;
			void consider(Id id){
				size_t pos;
				auto d=rnsymtab.get(id,null);
				if(!d||d in seen||!rnsymtab.tryGetPosition(id,pos)) return;
				seen.insert(d);
				ordered~=q(pos,d);
			}
			foreach(id;keys.changed) consider(id);
			foreach(d;used) consider(d.getId);
			sort!"a[0]<b[0]"(ordered);
			lastUses.merge(isLoop,this,scopes,ordered.map!(x=>x[1]).array,false);
		}
		// TODO: needed?
		substituteAllConsumed();
		consumedLogged=null;
		if(keys.all||!leftLogged) declProps.retireAll=true;
		else if(declProps.tracked) foreach(id;keys.changed~changedHere) if(auto o=oldTable.get(id,null)) if(rnsymtab.get(id,null) !is o) leftTable~=o; // (see `afterStatement`)
		return errors;
	}
	private Id[] deadMergeIds(MergeKeys keys,NestedScope[] scopes,ref MapSX!(Id,DeadMerge) deadMerges){ // (the dead entries that no nested scope changed, but whose names merged dead entries have: their merges are not trivial, see `MergeKeys`)
		SetX!Id names;
		foreach(name,_;deadMerges) names.insert(name);
		foreach(id;keys.changed) foreach(sc;scopes) if(auto d=cast(DeadDecl)sc.rnsymtab.get(id,null)) names.insert(d.name.id);
		Id[] r;
		foreach(name;names){
			if(keys.has(name)) continue;
			auto dd=cast(DeadDecl)scopes[0].rnsymtab.get(name,null);
			if(!dd) continue;
			if(rnsymtab.get(name,null) is dd) symtabRemove(dd); // (as the loop over the merged entries does)
			r~=name;
		}
		return r;
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
	protected void captureTypeCapturersImpl(Expression type){}
	final void captureTypeDependencies(Expression type){ // (e.g., the type of a `typeof` operand, whose uses of outer variables do not capture)
		Scope[] capturing;
		foreach(free;type.freeVars){
			auto meaning=free.meaning;
			if(!meaning||!meaning.scope_||meaning.isToplevelDeclaration()||!isNestedIn(meaning.scope_)) continue;
			Scope[] chain;
			for(Scope s=this;s&&s !is meaning.scope_;s=s.parentScope()) chain~=s;
			foreach_reverse(s;chain) s.captureTypeDependencyImpl(free,meaning,this);
			foreach(s;chain) if(!capturing.canFind(s)) capturing~=s;
		}
		foreach(s;capturing) s.captureTypeCapturersImpl(type);
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
		declProps.noteReplaced(id.meaning);
	}
	static if(language==silq)
	void reregisterComponentReplacement(IndexExp write,Id name,IndexExp read){
		import ast.semantic_:getIdFromIndex;
		auto id=getIdFromIndex(write);
		assert(id&&id.meaning);
		updateDeclProps(id.meaning).componentReplacements~=DeclProp.ComponentReplacement(write,name,read);
		declProps.noteReplaced(id.meaning);
	}
	static if(language==silq)
	void blockConvertedAggregate(Declaration decl,IndexExp convertedWrite,Id name){
		updateDeclProps(decl).componentReplacements~=DeclProp.ComponentReplacement(null,name,null,null,convertedWrite);
		declProps.noteReplaced(decl);
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
			bool compareTables(SymbolTable symtab,SymbolTable rsymtab){
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
		Q!(Id,Declaration,Expression,bool)[][2] loopParams(NestedScope loopScope, scope MapX!(Declaration,Declaration)* mustBeConstFromDummies=null, bool separateConstParams=true, scope SetX!Declaration* accessedDecls=null, scope SetX!Id* namesInLoop=null, scope SetX!Id* unchangedConst=null, scope SetX!Id* consumedAfter=null, scope SetX!Id* freed=null, scope Declaration[]* forgetBefore=null, NestedScope exitScope=null)in{
			assert(!!loopScope);
		}do{ // (name,decl,type,mayChange)
			typeof(return) r;
			SetX!Id mustBeConst;
			if(mustBeConstFromDummies)
				foreach(v;(*mustBeConstFromDummies).byValue)
					mustBeConst.insert(v.getId);
			import ast.semantic_: typeForDecl;
			Expression typeCopy(Expression type){ // (a free identifier whose name denotes another declaration at the loop keeps its meaning, e.g., the generic parameter `n` in the type of `x` after `n:=3`, which the lowered loop then captures)
				bool[const(void)*] free; // (not those that the type binds, e.g., `r` in `𝔹^(let { r:=dup(n); } in r)`)
				foreach(id;type.freeIdentifiers) free[cast(const(void)*)id]=true;
				Expression.CopyArgs cargs;
				cargs.mapExp=(Expression e,ref Expression.CopyArgs args){
					auto id=cast(Identifier)e;
					if(!id||cast(const(void)*)id !in free||!id.meaning||!id.meaning.name||id.meaning.isToplevelDeclaration()) return null;
					auto probe=new Identifier(id.meaning.name.id);
					probe.loc=id.loc;
					auto cur=loopScope.lookup(probe,false,true,Lookup.probing,null);
					if(!cur||cur.canonicalSource is id.meaning.canonicalSource) return null;
					Expression.CopyArgs keep={preserveMeanings:true};
					return id.copy(keep);
				};
				return type.copy(cargs);
			}
			Scope letScope=null; // (variables declared outside of a `let` expression are captured, such that its lowering does not depend on where it is analyzed)
			for(Scope s=loopScope;s&&!cast(FunctionScope)s;s=cast(NestedScope)s?(cast(NestedScope)s).parent:null)
				if(auto bs=cast(BlockScope)s) if(bs.isLetBody){ letScope=bs; break; }
			SetX!Declaration inTypes; // (types of parameters cannot depend on other parameters)
			if(separateConstParams) foreach(id,decl;rnsymtab)
				if(auto type=typeForDecl(decl)){
					foreach(tid;type.freeIdentifiers) if(tid.meaning) inTypes.insert(tid.meaning.canonicalSource);
					static if(language==silq){ // (nor on the variables that the values of type variables mention, e.g., `n` for `x:t` after `t:=𝔹^n`, or for `t` itself, see `unfoldTypeVariables`)
						import ast.semantic_: typeVariableDependency;
						foreach(e;only(unfoldTypeVariables(type),typeVariableDependency(decl)))
							if(e) foreach(tid;e.freeIdentifiers) if(tid.meaning) inTypes.insert(tid.meaning.canonicalSource);
					}
				}
			foreach(id,decl;rnsymtab){
				auto type=typeForDecl(decl);
				if(!type) continue;
				// variables whose names do not occur in the loop cannot change in it (they may still be split into the
				// loop scope, e.g. by an early `return` that has to forget them); they are not loop parameters
				if(namesInLoop&&id !in *namesInLoop&&(!decl.name||decl.name.id !in *namesInLoop)) continue;
				bool mayChange=isNonConstDecl(decl)||decl.isLinear();
				if(!mayChange&&forgetBefore&&namesInLoop&&type.isClassical()&&!decl.isConst&&!isConst(decl)&&decl.typeConstBlocker is null&&rnsymtab.get(decl.getId,null) is decl&&decl.splitInto.any!(d=>d.scope_ is loopScope)&&!unchangedOnContinuingPaths(decl,loopScope,exitScope)){
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
						r[1]~=q(id,decl,typeCopy(type),true);
						if(freed) freed.insert(decl.name.id);
						continue;
					}
					if(!separateConstParams) continue;
					if(!accessedDecls||decl.canonicalSource !in *accessedDecls) continue; // not captured
					// (classical variables are passed as well: a function without captures is analyzed only once)
					if(type.isClassical()&&(!cast(VarDecl)decl&&!cast(Parameter)decl||decl.isToplevelDeclaration()||isTypeTy(type)||cast(FunTy)type||decl.canonicalSource in inTypes)) continue; // (const capture)
					if(type.isClassical()&&letScope&&!(decl.canonicalSource.scope_&&decl.canonicalSource.scope_.isNestedIn(letScope))) continue; // (const capture)
					r[0]~=q(id,decl,typeCopy(type),false); // separate const parameter
					continue;
				}
				bool canForget=type.isClassical()||dependencies.canForget(decl);
				bool isConstParamDecl=false;
				if(canForget&&!type.isClassical())
					isConstParamDecl=mustBeConstFromDummies?decl.getId in mustBeConst:true;
				if(canForget&&mayChange&&unchangedConst&&unchangedOnContinuingPaths(decl,loopScope,exitScope)){ // (also a classical variable, e.g., `s` in `if j>=10 { s+=1; assert(false); }`: the loop does not return it, which it could not do under a quantum `if`)
					isConstParamDecl=true;
					unchangedConst.insert(id);
				}
				r[isConstParamDecl?0:1]~=q(id,decl,typeCopy(type),mayChange);
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
		static bool unchangedOnContinuingPaths(Declaration decl,NestedScope loopScope,NestedScope exitScope){
			Declaration split=null;
			foreach(d;decl.splitInto) if(d.scope_ is loopScope) split=d;
			if(!split) return false;
			if(loopScope.diverges){ // (no path continues the loop, e.g., the reset of a `do`-`while` loop returns: its exit follows the body)
				if(!exitScope) return true;
				auto atExit=exitScope.rnsymtab.get(split.getId,null);
				return atExit&&atExit.isDerivedFrom(split);
			}
			auto current=loopScope.rnsymtab.get(split.getId,null);
			return current&&current.isDerivedFrom(split);
		}
		Dependency dependencyOf(Declaration decl){
			if(!dependencies.tracked(decl)) return Dependency(true);
			return dependencies.get(decl).dup;
		}
	private:
		Dependencies dependencies;
		DeclProps declProps;
		Declaration[] toRemove;
		TrackedTemporary[] trackedTemporaries;
		SymbolTable symtab;
		SymbolTable rnsymtab;
		MapX!(Declaration,LastUse) lastUses;
		Declaration[] prevCapturedDecls; // TODO: only store how many there are?
		bool restoreable=false;
		size_t numMergedNestedScopes;
		size_t numLastUses;
		size_t numMovedCaptures;
		SetX!Declaration consumedBefore; // (in the tables, although their last uses before the snapshot consume them: the splits that a `return` hides and inserts again, see `close`)
	}
	ScopeState getStateSnapshot(bool restoreable=false){
		SymbolTable nsymtab=symtab.dup;
		SymbolTable nrnsymtab=rnsymtab.dup;
		MapX!(Declaration,LastUse) nlastUses;
		DeclProps declProps;
		TrackedTemporary[] trackedTemporaries;
		Declaration[] prevCapturedDecls;
		size_t numMovedCaptures;
		SetX!Declaration consumedBefore;
		if(restoreable){
			declProps=saveDeclProps();
			trackedTemporaries=trackedTemporaries.map!(x=>x.dup).array;
			nlastUses=lastUses.getSnapshot(this);
			foreach(d,lu;nlastUses) if(lu&&lu.isConsumption()) consumedBefore.insert(d);
			if(auto fd=getFunction()){
				prevCapturedDecls=fd.capturedDecls;
				numMovedCaptures=fd.movedCaptures.length;
			}
		}
		auto r=ScopeState(dependencies.dup,declProps,toRemove,trackedTemporaries,nsymtab,nrnsymtab,nlastUses,prevCapturedDecls,restoreable);
		r.consumedBefore=consumedBefore;
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
					if(tracked !is decl&&state.dependencies.tracked(tracked)&&!state.dependencies.tracked(decl))
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
		void splitSymtab(ref SymbolTable symtab,bool replace){
			Q!(Declaration,Declaration)[] splits;
			foreach(id,ref decl;symtab){
				auto splt=getSplit(decl);
				if(splt !is decl){
					if(replace){
						if(state.dependencies.tracked(decl))
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
		auto lu=lastUses.here(decl);
		return lu&&lu.isConsumption();
	}
	void restoreStateSnapshot(ref ScopeState state,bool forWithTransTrial=false)in{
		assert(state.restoreable);
	}do{
		lastUses.createDeferred();
		logSinceNesting=sinceMergeLogged=false; // (see `MergeKeys`)
		rnsymtab.stopLog();
		updateStateSnapshot(state);
		dependencies=state.dependencies;
		resetDeclProps(state.declProps);
		toRemove=state.toRemove;
		symtab.clear();
		foreach(_,decl;state.symtab){
			if(auto lu=state.lastUses.get(decl,null))
				if(lu.isConsumption()&&!forWithTransTrial&&decl !in state.consumedBefore) // (consumed after the snapshot was taken)
					continue;
			static if(language==silq) if(!forWithTransTrial&&consumedOutside(decl)) continue;
			symtab[decl.name.id]=updateDecl(decl);
		}
		rnsymtab.clear();
		foreach(_,decl;state.rnsymtab){
			if(auto lu=state.lastUses.get(decl,null)){
				if(lu.isConsumption()&&!forWithTransTrial&&decl !in state.consumedBefore){
					if(!toRemove.canFind(lu.decl)){ // TODO: make more efficient
						toRemove~=lu.decl;
						if(dependencyTracked(lu.decl)) pushDependencies(lu.decl,true); // (consumed after the snapshot was taken)
					}
					recordConsumption(lu.decl,lu.use);
					continue;
				}
			}
			static if(language==silq) if(!forWithTransTrial){
				if(auto lu=lastUses.here(decl)){
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
		foreach(_,decl;rnsymtab) consumedDepLog.remove(decl); // (logged after the snapshot, e.g., the version before a loop that the merge of the loop replaced)
		resetTypeMentioning();
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
					lastUses.noteSplitFromChanged(newOuter.splitInto[k]);
				}
				outer=newOuter;
			}
		}
	}
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
	DeclProps declProps;
	SymbolTable symtab;
	SymbolTable rnsymtab;
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
			Declaration first=null;
			Declaration[] ds; // (if there are several)
			foreach(sc;imports){
				if(auto d=sc.lookupImpl(ident,rnsym,false,kind,origin,failures)){
					if(!first) first=d;
					else{
						if(!ds.length) ds~=first;
						ds~=d;
					}
				}
			}
			if(first&&(!ds.length||rnsym)) return first;
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
	IndexExp[] accessedComponents; // components accessed as a whole in the transformation (e.g., `x[1]` in `dup(x[1])`, but not in `x[1][0]`)
	SetX!Id liftedComponents; // replacement candidates for consumed components of lifted aggregates (which could be duplicated)
	SetX!Id rereadComponents; // replacement candidates whose component is read again in the transformation
}

class NestedScope: Scope{
	Scope parent;
	private bool splitForDivergingSibling=false; // (a sibling that diverges consumes a variable from outside, see `closeUnreachable`: the variables of this scope keep depending on its split here, as merges ignore the sibling)
	private bool splitForSibling=false; // (another branch consumes a variable from outside: without a known dependency, the variables of this branch keep depending on its version from before the split, see `checkBranchOrder`)
	static if(language==silq) ContinuedLog continuedLog; // (of the conditionals in this scope whose other branch returns: the code after them runs as part of them, see `checkBranchOrder`)
	static if(language==silq) override void noteInserted(Declaration decl){
		if(continuedLog&&decl !in continuedLog.createdAt&&continuedLog.initial.get(decl.getId,null) !is decl) continuedLog.createdAt[decl]=continuedLog.branches.length;
	}
	static if(language==silq) final void addContinuedBranch(BlockScope bs)in{
		assert(bs.parent is this);
	}do{
		if(!continuedLog){
			continuedLog=new ContinuedLog;
			continuedLog.initial=rnsymtab.dup;
		}
		if(bs !in continuedLog.numbers) continuedLog.numbers[bs]=continuedLog.branches.length;
		continuedLog.branches~=bs;
		continuedLog.starts[bs]=continuedLog.starts.get(bs,null)~continuedLog.events.length;
	}
	Q!(Declaration,LastUse)[] forgottenAtSplit; // (versions that are uncomputed at their split, with the last uses that keep their dependencies there, see `dependenciesAtSplit`)
	final Q!(Declaration,Dependency)[] dependenciesAtSplit(){ // (they are split before the variables that those mention)
		return forgottenAtSplit.map!(f=>q(f[0],f[1].kind==LastUse.Kind.lazySplit?f[1].depAtSplit:f[1].dep)).array;
	}
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
		lastUses.prepareChange(odecl);
		import ast.semantic_: typeForDecl;
		if(!type) type=typeForDecl(ndecl);
		auto pdep=getDefaultDependency(ndecl);
		bool merged(NestedScope sc){ return sc.siblingsFinal; } // (see `merge`)
		Declaration oldVersion(NestedScope sc){ // (the version that `sc` refers to: the split in the enclosing scope already replaced `odecl` in its merged nested scopes, see `replaceDecl`)
			return ndecl !is odecl&&merged(sc)?ndecl:odecl;
		}
		Dependency splitDependency(NestedScope sc){ // (without a known dependency in the enclosing scope, a branch keeps the one it has there: a sibling consumed something it depends on, see `checkBranchOrder`; a branch that already ended keeps the one it has at its end, as the enclosing scope continues another branch while merging)
			auto old=oldVersion(sc);
			if(merged(sc)&&sc.dependencyTracked(old)) return sc.getDependency(old).dup;
			if(!pdep.isTop||!LastUse.interleavable(sc)||!sc.dependencyTracked(old)) return pdep.dup;
			auto own=sc.getDependency(old);
			return own.isTop?pdep.dup:own.dup;
		}
		Declaration result=ndecl;
		void processCurrent(){
			result=ndecl;
			if(type){
				auto old=oldVersion(this);
				symtabRemove(odecl);
				if(dependencyTracked(old)&&!splitForDivergingSibling&&!(splitForSibling&&getDependency(old).isTop)){
					// if(odecl !is ndecl) dependencies.replace(odecl,ndecl); // reverse-inherit dependencies through split
					auto prevConsumingUse=consumingUse;
					consumingUse=use;
					scope(exit) consumingUse=prevConsumingUse;
					pushDependencies(old,true,splitting?null:use);
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
							auto ndep=splitDependency(this);
							if(dependencyTracked(old))
								removeDependency(old);
							//imported!"util.io".writeln("DEPS: ",dependencies);
							//imported!"util.io".writeln("ADDING DEP: ",odecl," ",result," ",pdep," ",cast(void*)this);
							addDependency(old,ndep);
							//imported!"util.io".writeln("DEP IS NOW: ",getDependency(odecl));
						}
						assert(old !is result);
						replaceDecl(old,result);
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
					sc.splitForDivergingSibling=diverges;
					sc.splitForSibling=LastUse.interleavable(sc);
					auto cdecl=sc.consumeImpl(odecl,ndecl,type,false,use,consumedComponent,splitting);
					sc.splitForDivergingSibling=sc.splitForSibling=false;
					if(cdecl){
						auto old=oldVersion(sc);
						if(parent.getFunction() is sc.getFunction()){
							auto ndep=splitDependency(sc);
							if(sc.dependencyTracked(old)) // TODO: can we get rid of this?
								sc.removeDependency(old);
							//imported!"util.io".writeln("DEPS: ",sc.dependencies);
							//imported!"util.io".writeln("ADDING DEP: ",odecl," ",result," ",pdep," ",cast(void*)sc);
							sc.addDependency(old,ndep);
							//imported!"util.io".writeln("DEP IS NOW: ",sc.getDependency(odecl));
						}
						if(old !is cdecl)
							sc.replaceDecl(old,cdecl);
						sc.splitIntoActiveNestedScopes(odecl,cdecl,use,consumedComponent,splitting);
					}
				}
			}else processCurrent();
		}else{
			consumedOuter~=ndecl;
			processCurrent();
		}
		if(!type&&remove){
			auto old=oldVersion(this);
			symtabRemove(odecl);
			if(dependencyTracked(old))
				pushDependencies(old,true,splitting?null:use);
			if(old !is result)
				replaceDecl(old,result);
			return result;
		}
		return remove?consume(result,use,consumedComponent,splitting):result;
	}

	override Declaration lookupImpl(Identifier ident,bool rnsym,bool lookupImports,Lookup kind,Scope origin,DeadDecl[]* failures){
		if(auto decl=lookupHereFrom(ident,rnsym,origin,failures)) return hiddenAfterReturn(decl)?null:decl;
		auto decl=parent.lookupImpl(ident,rnsym,lookupImports,kind,origin,failures);
		return decl&&hiddenAfterReturn(decl)?null:decl;
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
		if(auto decl=lookupHereFrom(ident,rnsym,origin,failures)) return decl;
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
	protected override void captureTypeCapturersImpl(Expression type){
		if(!typeofOperand) parent.recordCapturers(type);
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
		void captureMention(Identifier free){ // (through a copy: types share identifiers with expressions, which the renamings of the capture must not change, e.g., `n` of `vector(n,0:𝔹)` in the type of its result, or of `a:=𝔹^n` in the value of `a`, for a closure in a branch that splits `n`)
			if(!free.meaning) return;
			auto mentioned=free.meaning;
			for(Scope c=parent;c;c=c.parentScope()){ // (the version with the same value that is current here, e.g., of `n` after a loop body that defines `n` and `a:=𝔹^n`, as for the uses of `n` in the closure, see `unavailableAt`)
				if(auto cur=c.rnsymtab.get(mentioned.getId,null)){
					if(!cast(DeadDecl)cur&&cur.canonicalSource is mentioned.canonicalSource) mentioned=cur;
					break;
				}
				if(c is mentioned.scope_) break;
			}
			Expression.CopyArgs cargs={preserveSemantic:true};
			auto mention=free.copy(cargs);
			mention.meaning=mentioned;
			mention.typeofSuppressedCapture=free.typeofSuppressedCapture;
			addCapture(mention,mentioned,Lookup.constant,origin);
		}
		foreach(free;type.freeVars) captureMention(free);
		static if(language==silq){ // (and the variables that the values of type variables mention, through which the closure can look, see `unfoldTypeVariables`)
			import ast.semantic_:typeVariableDependency,typeVariableValueUnavailable;
			auto utype=unfoldTypeVariables(type);
			auto value=typeVariableValueUnavailable(meaning,origin)?null:typeVariableDependency(meaning);
			foreach(e;only(utype !is type?utype:null,value))
				if(e) foreach(free;e.freeVars) captureMention(free);
		}
		parent.recordCapturers(type);
		import ast.semantic_:typeConstBlocked;
		bool isConstDecl=meaning.isConst||typeConstBlocked(meaning,origin)||origin.isConst(meaning);
		bool isConstLookup=kind==Lookup.constant||isConstDecl;
		static if(language==silq&&is(T==FunctionDef)){
			auto captureAnnotation=decl.ftype?decl.ftype.captureAnnotation:CaptureAnnotation.const_; // TODO: store in function def
			bool recomputeType=isConstLookup?captureAnnotation==CaptureAnnotation.moved:captureAnnotation==CaptureAnnotation.const_;
		}
		static if(language==silq)
		if(type.hasQuantumComponent()){
			if(origin.versionComponentReplacements(meaning).length){
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
		if(auto decl=lookupHereFrom(ident,rnsym,origin,failures)) return decl;
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
	static if(language==silq) Q!(Scope,BlockScope[])[] pendingBranchOrders; // (of the conditionals of the function, see `checkBranchOrder`)
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
	bool isLoopEntry=false; // (merged with the loop body for the state at the start of an iteration: its forgets happen before the loop)
	bool isLetBody=false;
	bool isLoopReset=false; // (of a `do`-`while` loop)
	bool isBranch=false; // (of a conditional, see `LastUses.dependencyAtSplit`)
	Q!(LastUse,size_t)[] uncomputations; // (in the branch and its nested scopes, with the numbers of the events of the code after the conditional at them, see `checkBranchOrder` and `LastUse.noteBranchEvent`)
	Declaration[] eagerMerges; // (merged versions of variables whose versions in the branch have no known dependency, which values merged after them depend on instead, see `Scope.merge`)
	Q!(Declaration,LastUse,size_t)[] outerConsumptions; // (of versions of variables of the enclosing scope, with the same numbers)
	bool interleave=false; // (the code generator interleaves the statements of the branches, see `checkBranchOrder`)
	bool returningConditional=false; // (in a loop body, a branch of the conditional returns on some path: the code generator does not interleave the branches)
	bool returnsOnSomePath=false; // (no eager merges, see `eagerIds` in `Scope.merge`)
	bool returningBeforeContinuation=false; // (it returns on every path, and the code after the conditional continues the other branch, see `NestedScope.continuedLog`)
	bool returns=false; // (on every path, see `returnsOnEveryPath`)
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
	BlockScope substitutedFrom=null; // (a copy that a substitution made to remap the declarations in the lists of the scope that still declares them, see substituteBlockCompound)
}

static if(language==silq)
bool consumesOutsideType(Declaration decl,Scope boundary){ // (a type cannot consume variables declared outside of it, also through the versions that splits and merges derive from them)
	if(!boundary||!decl||decl.isToplevelDeclaration()) return false;
	bool outside(Declaration d){
		auto cs=d.canonicalSource.scope_;
		if(cs&&(cs is boundary||!cs.isNestedIn(boundary))) return true;
		if(d.splitFrom&&outside(d.splitFrom)) return true;
		foreach(m;d.mergedFrom) if(outside(m)) return true; // (e.g., after a branch that consumed it)
		return false;
	}
	return outside(decl);
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
		if(auto decl=lookupHereFrom(ident,rnsym,origin,failures)) return decl;
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
