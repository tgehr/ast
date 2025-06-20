// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.scope_;
import astopt;

import std.format, std.conv, std.range, std.algorithm;
import util.tuple:Q=Tuple,q=tuple;
import ast.lexer, ast.expression, ast.declaration, ast.type, ast.error;
import util, util.hashtable: HashMap;

static if(language==silq){
struct Dependency{
	bool isTop;
	SetX!Declaration dependencies;
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
	void replace(Declaration decl, Dependency rhs){
		if(decl !in dependencies) return;
		dependencies.remove(decl);
		joinWith(rhs);
	}
	void replace(Declaration decl,Declaration ndecl){
		if(decl in dependencies){
			dependencies.remove(decl);
			dependencies.insert(ndecl);
		}
	}
	Dependency dup(){
		return Dependency(isTop, dependencies.dup);
	}
	private Q!(bool,SetX!Id) getIds(){
		SetX!Id result;
		foreach(decl;dependencies) result.insert(decl.getId);
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
	void pushUp(Declaration removed, bool keep)in{
		assert(removed in dependencies,text(removed," ",removed.loc," ",dependencies));
	}do{
		Dependency x=dependencies[removed];
		if(!keep) dependencies.remove(removed);
		foreach(k,ref v;dependencies){
			v.replace(removed, x);
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
		foreach(decl,ref dependency;dependencies)
			result[decl.getId]=dependency.getIds();
		return result;
	}
	bool matches(Dependencies rhs){ // TODO: make faster?
		auto ids=getIds,rids=rhs.getIds;
		return ids==rids;
	}
}
}
enum Lookup{
	consuming,
	constant,
	probing,
	probingWithCapture,
}

abstract class Scope{
	abstract @property ErrorHandler handler();
	bool allowsLinear(){
		return true;
	}
	bool canInsert(Id id){
		auto decl=symtabLookup(id,false,null);
		return !decl;
	}
	bool insert(Declaration decl,bool force=false)in{assert(!decl.scope_);}do{
		if(auto d=symtabLookup(decl.name,false,null)){
			if(!decl.isSemError()) redefinitionError(decl, d);
			decl.setSemError();
			return false;
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

	void redefinitionError(Declaration decl, Declaration prev) in{
		assert(decl&&prev);
		assert(!cast(DeadDecl)decl&&!cast(DeadDecl)prev);
	}do{
		error(format("redefinition of \"%s\"",decl.name), decl.name.loc);
		note("previous definition was here",prev.name.loc);
		decl.setSemError();;
	}

	static if(language==silq){
		static struct DeclProp{
			private Identifier constBlock;
			static if(language==silq){
				static struct ComponentReplacement{
					IndexExp write;
					Id name;
					IndexExp read;
				}
				ComponentReplacement[] componentReplacements;
				void nameIndex(IndexExp index,Id name){
					auto r=ComponentReplacement(index,name,IndexExp.init);
					if(index.isSemError()) swap(r.write,r.read);
					componentReplacements~=r;
				}
			}
			private Identifier[] accesses;
			private Declaration[] capturers;
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
			DeclProp merged()in{
				//assert(!constBlock);
				assert(!componentReplacements.length);
			}do{
				constBlock=null; // TODO: ok?
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
				foreach(id;accesses){ // foreach(id,decl;declProps.accesses.map!(x=>x)) hangs the compiler
					if(id.meaning !is splitFrom) continue;
					id.meaning=splitInto;
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
							if(id.meaning is splitFrom) id.meaning=splitInto;
					}
					if(auto fd=cast(FunctionDef)capturer) doIt(fd);
					else if(auto dat=cast(DatDecl)capturer) doIt(dat);
					else assert(0,text(typeid(capturer)));
				}
			}
		}
		static struct DeclProps{
			private DeclProp[Declaration] props;
			DeclProps dup(){ return DeclProps(props.dup); }
			void clear(){ props.clear(); }
			DeclProp* tryGet(Declaration decl){ return decl in props; }
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
				}
			}
		}
		final DeclProps saveDeclProps(){ return declProps.dup; }
		final void resetDeclProps(DeclProps previous){ declProps=previous; }
		final void resetDeclProps(){ declProps.clear(); }
		final void mergeDeclProps(ref DeclProps nested){
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
			foreach(ref prop;nestedDeclProp(decl)){
				return &declProps.set(decl,prop.inherit);
			}
			return &declProps.set(decl,DeclProp.default_());
		}
		final void recordAccess(Identifier id,Declaration meaning){
			updateDeclProps(meaning).accesses~=id;
		}
		final void recordCapturer(Declaration capturer,Declaration meaning){
			updateDeclProps(meaning).capturers~=capturer;
		}
		private final Identifier isConstHere(Declaration decl){
			if(auto r=declProps.tryGet(decl)) return r.constBlock;
			return null;
		}
		final void blockConst(Declaration decl,Identifier constBlock){
			updateDeclProps(decl).constBlock=constBlock;
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
			auto dep=getDependency(expr,this);
			if(dep.isTop) return false;
			trackedTemporaries~=TrackedTemporary(expr,dep);
			return true;
		}
		final void recordConstBlockedConsumption(Identifier read,Identifier use)in{
			assert(read.meaning&&read is isConst(read.meaning));
			assert(canForget(read.meaning),text(read.loc," ",use.loc));
		}do{
			import ast.semantic_:getDependency;
			auto dep=getDependency(read,read.scope_);
			assert(!dep.isTop);
			read.scope_.trackedTemporaries~=TrackedTemporary(use,dep,read);
		}
		final bool checkTrackedTemporaries(TrackedTemporary[] trackedTemporaries){
			//imported!"util.io".writeln("CHECKING TEMPORARIES: ",trackedTemporaries);
			bool success=true;
			foreach(tt;trackedTemporaries){
				if(!tt.dep.isTop) continue;
				success=false;
				if(auto id=cast(Identifier)tt.expr){
					if(id.meaning&&(!id.constLookup&&!id.implicitDup)){
						assert(tt.read&&tt.read.meaning);
						blockConst(tt.read.meaning,tt.read); // TODO: why neede?
						if(checkConsumable(id,tt.read.meaning))
							assert(tt.read.meaning.isSemError);
						id.setSemForceError();
						id.meaning.setSemForceError();
						continue;
					}
				}
				import ast.semantic_:nonLiftedError;
				nonLiftedError(tt.expr,this);
				tt.expr.setSemError();
			}
			return success;
		}
		final Identifier isConst(Declaration decl){
			foreach(ref prop;nestedDeclProp(decl))
				if(auto r=prop.constBlock)
					return r;
			return null;
		}
		static struct ConstBlockContext{
			private Identifier[Declaration] constBlock;
			private size_t numTrackedTemporaries;
		}
		final ConstBlockContext saveConst(){
			Identifier[Declaration] constBlock;
			foreach(decl,ref prop;declProps.props) constBlock[decl]=prop.constBlock;
			return ConstBlockContext(constBlock,trackedTemporaries.length);
		}
		final bool resetConst(ConstBlockContext context){
			foreach(decl,constBlock;context.constBlock)
				updateDeclProps(decl).constBlock=constBlock;
			foreach(decl,ref prop;declProps.props)
				if(decl !in context.constBlock)
					prop.constBlock=null;
			auto success=checkTrackedTemporaries(trackedTemporaries[context.numTrackedTemporaries..$]);
			trackedTemporaries=trackedTemporaries[0..context.numTrackedTemporaries];
			return success;
		}
		final bool resetConst(){
			foreach(decl,ref prop;declProps.props)
				prop.constBlock=null;
			auto success=checkTrackedTemporaries(trackedTemporaries);
			trackedTemporaries=[];
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
		static struct ComponentReplacementContext{
			private DeclProp.ComponentReplacement[][Declaration] componentReplacements;
		}
		final ComponentReplacementContext moveLocalComponentReplacements(){ // TODO: get rid of this
			DeclProp.ComponentReplacement[][Declaration] r;
			foreach(decl,ref prop;declProps.props){
				r[decl]=prop.componentReplacements;
				prop.componentReplacements=[];
			}
			return typeof(return)(r);
		}
		final void restoreLocalComponentReplacements(ComponentReplacementContext previous){ // TODO: get rid of this
			foreach(decl,crepls;previous.componentReplacements)
				updateDeclProps(decl).componentReplacements=crepls;
		}
	}else{
		struct DeclProps{ }
		struct ConstBlockContext{ }
		final DeclProps saveDeclProps(){ return DeclProps.init; }
		final void resetDeclProps(DeclProps previous){ }
		final void resetDeclProps(){ }
		final Identifier isConst(Declaration decl){ return null; }
		final ConstBlockContext saveConst(){ return ConstBlockContext.init; }
		final void resetConst(ConstBlockContext previous){ }
		final void resetConst(){ }
		final void resetComponentReplacement(){ }
	}
	final void recordConsumption(Declaration decl,Identifier use){
		if(allowMerge) return;
		if(!use) return;
		auto cd=new ConsumedDecl(decl,use);
		if(decl.rename){
			cd.rename=new Identifier(decl.rename.id);
			cd.rename.loc=decl.rename.loc;
		}
		cd.scope_=decl.scope_;
		cd.setSemCompleted();
		if(canInsert(cd.name.id))
			symtabInsert(cd);
	}
	final Declaration consume(Declaration decl,Identifier use){
		if(use&&!decl.isSemError&&!use.isSemError){
			if(auto read=isConst(decl))
				recordConstBlockedConsumption(read,use);
		}
		if(rnsymtab.get(decl.getId,null) !is decl) return null;
		if(cast(DeadDecl)decl) return null;
		Expression type;
		return consumeImpl(decl,decl,type,true,use); // TODO: separate splitting and consuming
	}
	final bool canSplit(Declaration decl)in{
		assert(decl.scope_&&this.isNestedIn(decl.scope_));
	}do{
		if(decl.scope_ is this) return true;
		auto vd=cast(VarDecl)decl;
		if(vd&&(vd.isConst||vd.typeConstBlocker)||isConst(decl)&&!canForget(decl)) return false;
		return true;
	}
	final Declaration split(Declaration decl,Identifier use)in{
		assert(decl.scope_&&this.isNestedIn(decl.scope_));
	}do{
		if(decl.scope_ is this) return decl;
		if(!canSplit(decl)) return decl;
		Expression type;
		auto result=consume(decl,use);
		if(!result) return decl;
		unconsume(result);
		return result;
	}
	final void unconsume(Declaration decl)in{
		assert(decl.scope_ is null||decl.scope_ is this||decl.isSemError(),text(decl," ",decl.loc));
	}do{
		toRemove=toRemove.filter!(pdecl=>pdecl!is decl).array;
		symtabInsert(decl);
		decl.scope_=this;
	}
	Declaration[] consumedOuter;
	Declaration[] splitVars;
	final void splitVar(Declaration splitFrom,Declaration splitInto){
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
	final void replaceDecl(Declaration splitFrom,Declaration splitInto)in{
		assert(splitFrom !is splitInto);
	}do{
		if(language==silq){
			if(dependencyTracked(splitFrom))
				replaceDependencies(splitFrom,splitInto);
			declProps.replaceDecl(splitFrom,splitInto);
		}
	}

	final void updateType(Declaration decl){
		if(auto prop=declProps.tryGet(decl)){
			foreach(id;prop.accesses){
				if(auto ty=id.typeFromMeaning)
					id.type=ty;
			}
		}
	}

	protected Declaration consumeImpl(Declaration odecl,Declaration ndecl,ref Expression type,bool remove,Identifier use)in{
		assert(odecl is ndecl||!remove);
	}do{
		assert(odecl.scope_ is this&&ndecl.scope_ is this);
		if(rnsymtab.get(odecl.getId,null) !is odecl) return null;
		if(remove){
			symtabRemove(odecl);
			static if(language==silq){
				static if(language==silq){
					if(odecl !is ndecl)
						replaceDecl(odecl,ndecl);
				}
				if(dependencyTracked(ndecl))
					pushDependencies(ndecl,true);
			}
			recordConsumption(odecl,use);
		}else if(odecl !is ndecl){
			assert(odecl.name.id == ndecl.name.id);
			symtabRemove(odecl);
			symtabInsert(ndecl);
			static if(language==silq)
				replaceDecl(odecl,ndecl);
		}
		return ndecl;
	}
	static if(language==silq){
		private Declaration[] toRemove;
		private TrackedTemporary[] trackedTemporaries;
		final void pushUp(ref Dependency dependency,Declaration removed){
			if(!dependencyTracked(removed)) return; // TODO: ideally can be removed
			dependency.replace(removed,dependencies.dependencies[removed]);
		}
		final void clearConsumed(){
			foreach(removed;toRemove){
				removeDependency(removed);
				declProps.remove(removed);
			}
			toRemove=[];
		}
	}

	protected final Declaration symtabLookup(Identifier ident,bool rnsym,DeadDecl[]* failures){
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

	final bool checkConsumable(Identifier id,Declaration meaning=null)in{
		assert(id.meaning||meaning);
	}do{
		if(!meaning) meaning=id.meaning;
		if(id.isSemError||meaning&&meaning.isSemError) return true;
		assert(!!meaning);
		if(auto vd=cast(VarDecl)meaning){
			if(vd.typeConstBlocker){
				error(format("cannot consume 'const' variable '%s'",id), id.loc);
				id.setSemError();
				vd.setSemForceError();
				import ast.semantic_:typeConstBlockNote;
				typeConstBlockNote(vd,this);
				return false;
			}
		}
		if(canForget(meaning))
			return true;
		if(auto read=isConst(meaning)){
			error(format("cannot consume 'const' variable '%s'",id), id.loc);
			note("variable was made 'const' here", read.loc);
			id.setSemForceError();
			meaning.setSemForceError();
			return false;
		}else if(meaning.isConst){
			error(format("cannot consume 'const' variable '%s'",id), id.loc);
			note("declared 'const' here", meaning.loc);
			id.setSemForceError();
			meaning.setSemForceError();
			return false;
		}
		return true;
	}

	private Declaration postprocessLookup(Identifier id,Declaration meaning,Lookup kind){
		static if(language==silq) enum performConsume=true;
		else auto performConsume=id.byRef;
		if(kind!=Lookup.probing&&meaning){
			recordAccess(id,meaning);
		}
		if(performConsume){
			if(!meaning) return meaning;
			if(kind==Lookup.consuming){
				bool doConsume=true;
				if(doConsume){
					if(!checkConsumable(id,meaning))
						doConsume=false;
					if(doConsume&&meaning.scope_){
						assert(!meaning.isConst);
						if(auto nmeaning=consume(meaning,id))
							meaning=nmeaning;
					}
				}
			}
			static if(language==silq)
			if(kind==Lookup.constant&&meaning.isLinear()){
				if(!isConstHere(meaning))
					blockConst(meaning,id);
			}
		}
		return meaning;
	}

	final Declaration lookup(Identifier ident,bool rnsym,bool lookupImports,Lookup kind,DeadDecl[]* failures){
		auto meaning=lookupImpl(ident,rnsym,lookupImports,kind,this,failures);
		return postprocessLookup(ident,meaning,kind);
	}
	Declaration lookupImpl(Identifier ident,bool rnsym,bool lookupImports,Lookup kind,Scope origin,DeadDecl[]* failures){
		return lookupHereImpl(ident,rnsym,failures);
	}
	Identifier getRenamed(Identifier cname){
		for(;;){ // TODO: quite hacky
			auto d=lookup(cname,true,true,Lookup.probing,null);
			import ast.semantic_: isBuiltIn;
			if(!d&&!isBuiltIn(cname)) break;
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
		import ast.semantic_: unrealizable;
		bool errors=false;
		static if(language==silq){
			foreach(_,d;rnsymtab.dup){
				if(cast(DeadDecl)d) continue;
				if(d.isSemError()) continue;
				//if(d.scope_ !is this && !d.isLinear()) continue;
				if(!canSplit(d)){
					if(!d.isSemError()){
						if(auto read=isConst(d)){
							error(format("cannot forget 'const' variable '%s'",d), d.loc);
							note("variable was made 'const' here", read.loc);
							d.setSemForceError();
							errors=true;
						}
					}
					continue;
				}
				if(d.scope_.getFunction() !is getFunction()) continue;
				d=split(d,null);
				assert(d.scope_ is this);
				if(auto vd=cast(VarDecl)d) if(!vd.vtype||unrealizable(vd.vtype)) {
					d.setSemForceError();
					continue;
				}
				if(!canForgetAppend(loc,d)){
					if(cast(Parameter)d) error(format("%s '%s' is not consumed (perhaps return it or annotate it 'const')",d.kind,d.getName),d.loc);
					else error(format("%s '%s' is not consumed (perhaps return it)",d.kind,d.getName),d.loc);
					d.setSemForceError();
					errors=true;
				}else{
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
		}
		return errors;
	}

	final bool close(){
		return Scope.close(this);
	}

	final bool closeUnreachable(Scope mergeScope){
		static if(language==silq)
			clearConsumed();
		activeNestedScopes=[];
		allowMerge=false;
		foreach(_,d;rnsymtab.dup){
			if(d.isLinear()||d.scope_ is this){
				if(auto p=cast(Parameter)d) if(p.isConst) continue;
				consume(d,null);
				static if(language==silq){
					clearConsumed();
				}
			}
		}
		static if(language==silq)
			if(mergeScope)
				mergeScope.mergeDeclProps(this.declProps);
		return false;
	}

	static if(language==silq){
		auto controlDependency=Dependency(false,SetX!Declaration.init);
		void addControlDependency(Dependency dep){
			controlDependency.joinWith(dep);
		}

		void addDefaultDependency(Declaration decl)in{
			assert(!dependencyTracked(decl));
		}do{
			//imported!"util.io".writeln("ADDING DEFAULT: ",decl," ",Dependency(decl.isSemCompleted()&&decl.isLinear));
			addDependency(decl,Dependency(decl.isSemCompleted()&&decl.isLinear));
			//foreach(ddecl,ref dep;dependencies.dependencies) imported!"util.io".writeln(ddecl," ",cast(void*)ddecl);
			//imported!"util.io".writeln("ADDED DEFAULT: ",decl," ",dependencies," ",cast(void*)decl);
			//assert(decl.getName!="rrr");
		}

		void addDependency(Declaration decl, Dependency dep){
			addDependencies([q(decl,dep)]);
		}
		void removeDependency(Declaration decl){
			dependencies.dependencies.remove(decl);
		}
		void addDependencies(scope Q!(Declaration,Dependency)[] deps){
			//imported!"util.io".writeln("ADDING: ",this,"(",cast(void*)this,") ",deps);
			foreach(i,ref dep;deps){
				assert(!!dep[0]);
				if(dep[0] in dependencies.dependencies){
					//writeln(dep[0]," ",toRemove," ",dependencies)
					dep[1].joinWith(dependencies.dependencies[dep[0]]);
				}
			}
			foreach(decl,dep;deps.map!(x=>x)){
				foreach(odecl;dep.dependencies)
					assert(dependencyTracked(odecl)||odecl.isSemError(),text(dependencies," ",decl," ",dep," ",odecl));
				dependencies.dependencies[decl]=dep;
			}
		}

		final bool dependencyTracked(Declaration decl){
			return !!(decl in dependencies.dependencies);
		}
		final Dependency getDependency(Identifier id)in{
			assert(id.isSemCompleted()||id.isSemError());
			assert(!!id.meaning);
		}do{
			return getDependency(id.meaning);
		}
		final Dependency getDependency(Declaration decl,bool pushed=false)in{
			assert(decl.isSemCompleted()||decl.isSemError(),text(decl," ",decl.sstate));
		}do{
			if(!dependencyTracked(decl)) addDefaultDependency(decl); // TODO: ideally can be removed
			return dependencies.dependencies[decl];
		}
		final void replaceDependencies(Declaration decl,Declaration rhs){
			dependencies.replace(decl,rhs);
		}
		final void pushDependencies(Declaration decl,bool keep){
			dependencies.pushUp(decl,keep);
			this.pushUp(controlDependency,decl);
			foreach(ref tt;trackedTemporaries)
				this.pushUp(tt.dep,decl);
			if(keep) toRemove~=decl;
		}

		bool canForget(Declaration decl){
			if(decl.isSemError()) return true;
			assert(decl.isSemCompleted()||cast(FunctionDef)decl&&decl.isSemStarted(),text(decl," ",decl.sstate));
			import ast.semantic_:typeForDecl;
			auto type=typeForDecl(decl);
			if(type&&type.isClassical) return true; // TODO: ensure classical variables have dependency `{}` instead?
			if(!dependencyTracked(decl)) addDefaultDependency(decl); // TODO: ideally can be removed
			return dependencies.canForget(decl);
		}

		Declaration[] forgottenVars;
		final bool canForgetAppend(T)(T cause,Declaration decl)if(is(T==Scope)||is(T==ReturnExp))in{
			assert(decl.scope_ is this,text(decl," ",decl.scope_," ",typeid(decl)));
		}do{
			if(cast(DeadDecl)decl) return true;
			if(canForget(decl)){
				cause.forgottenVars~=decl;
				return true;
			}
			return false;
		}
		final bool canForgetAppend(Declaration decl){
			return canForgetAppend(this,decl);
		}
	}
	Declaration[] mergedVars;
	Declaration[] producedOuter;
	final void mergeVar(Declaration mergedFrom,Declaration mergedInto){
		mergedInto.mergedFrom~=mergedFrom;
		mergedFrom.mergedInto=mergedInto;
		mergedVars~=mergedFrom;
	}

	bool allowMerge=false;
	NestedScope[] activeNestedScopes;
	void nest(NestedScope r)in{
		static if(language==silq) assert(allowsLinear());
		assert(r.parent is this);
	}do{
		static if(language==silq){
			r.controlDependency.joinWith(controlDependency);
			r.dependencies=dependencies.dup;
		}
		r.symtab=symtab.dup;
		r.rnsymtab=rnsymtab.dup;
		allowMerge=true;
		activeNestedScopes~=r;
	}

	bool merge(bool quantumControl,NestedScope[] scopes...)in{
		assert(scopes.length);
		//debug assert(allowMerge);
	}do{
		// scope(exit) writeln("MERGING\n",this,"\n",scopes.map!(sc=>text("nested: ",sc,"\nconsumed: ",sc.consumedOuter,"\nsplit: ",sc.splitVars,"\nmergedVars: ",sc.mergedVars,"\nproducedOuter: ",producedOuter)).join("\n"),"\nEND MERGE\n");
		foreach(sc;scopes) sc.clearConsumed();
		static if(language==silq){
			clearConsumed();
		}
		assert(scopes==activeNestedScopes,text(scopes," ",activeNestedScopes));
		activeNestedScopes=[];
		allowMerge=false;
		symtab=scopes[0].symtab.dup;
		rnsymtab=scopes[0].rnsymtab.dup;
		dependencies=scopes[0].dependencies.dup;
		auto nestedControlDependency=scopes[0].controlDependency.dup;
		bool errors=false;
		DeadMerge[Id] deadMerges;
		DeadMerge addDeadMerge(Declaration sym){
			if(auto dm=sym.name.id in deadMerges)
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
		foreach(psym;rnsymtab.dup){
			auto sym=psym;
			import ast.semantic_: typeForDecl;
			bool symExists=true,needMerge=sym.scope_ is scopes[0];
			void removeOSym(Scope sc,Declaration osym){
				if(sc !is this)
					if(auto dm=osym.name.id in deadMerges)
						dm.mergedFrom~=osym;
				sc.symtabRemove(osym);
				static if(language==silq){
					if(sc.dependencyTracked(osym))
						sc.pushDependencies(osym,false);
				}
			}
			void splitSym(){
				auto nsym=scopes[0].split(sym,null);
				if(nsym is sym) return;
				symtabRemove(sym);
				symtabInsert(nsym);
				sym=nsym;
			}
			void removeSym(){
				addDeadMerge(sym);
				removeOSym(this,sym);
				removeOSym(scopes[0],psym);
				symExists=false;
			}
			void promoteSym(Expression ntype){
				symtabRemove(sym);
				auto var=addVariable(sym,ntype,true);
				if(!dependencyTracked(sym))
					addDefaultDependency(sym); // TODO: ideally can be removed
				//dependencies.replace(sym,var); // reverse-inherit dependencies
				auto dep=getDependency(sym);
				dep.joinWith(nestedControlDependency);
				addDependency(var,dep);
				pushDependencies(sym,false);
				sym=var;
				needMerge=true;
			}
			if(cast(DeadDecl)sym){
				removeOSym(this,sym);
				continue;
			}
			foreach(sc;scopes[1..$]){
				auto osym=sc.rnsymtab.get(sym.getId,null);
				if(!osym||cast(DeadDecl)osym){
					static if(language==silq){
						splitSym();
						if(!scopes[0].canForgetAppend(sym)){
							error(format("variable '%s' is not consumed", sym.getName), sym.loc);
							errors=true;
						}
					}
					removeSym();
				}else{
					if(sym!=osym){
						auto ot=typeForDecl(osym),st=typeForDecl(sym);
						if(!ot) ot=st;
						if(!st) st=ot;
						if(ot&&st){
							if(quantumControl){ // automatically promote to quantum if possible
								if(auto qt=ot.getQuantum)
									ot=qt;
							}
							auto nt=ot&&st?joinTypes(ot,st):null;
							if(!nt||quantumControl&&nt.hasClassicalComponent()){
								static if(language==silq){
									splitSym(), sc.split(osym,null);
									if(sym.isSemCompleted()&&osym.isSemCompleted()){
										if(!scopes[0].canForgetAppend(sym)|!sc.canForgetAppend(osym)){
											error(format("variable '%s' is not consumed", sym.getName), sym.loc);
											if(!nt) note(format("declared with incompatible types '%s' and '%s' in different branches",ot,st), osym.loc);
											errors=true;
										}
									}
								}
								removeSym();
								removeOSym(sc,osym);
							}else promoteSym(nt);
						}
					}
				}
			}
			if(symExists&&needMerge){
				if(auto ntype=typeForDecl(sym)){
					if(sym.scope_ is scopes[0]) promoteSym(ntype);
					foreach(sc;scopes){
						assert(sym.getId in sc.rnsymtab);
						auto osym=sc.rnsymtab[sym.getId];
						sc.mergeVar(osym,sym);
						static if(language==silq){
							if(!sc.dependencyTracked(osym))
								sc.addDefaultDependency(osym); // TODO: ideally can be removed
							//sc.dependencies.replace(osym,sym); // reverse-inherit dependencies
							auto dep=sc.getDependency(osym);
							// dep.joinWith(sc.controlDependency); // TODO
							dep.joinWith(nestedControlDependency);
							sc.addDependency(sym,dep);
							sc.pushDependencies(osym,false);
						}
					}
				}else sym.scope_=this;
				producedOuter~=sym;
			}
		}
		static if(language==silq){
			foreach(sc;scopes){
				foreach(sym;sc.rnsymtab.dup){
					if(sym.isSemError()&&(!sym.scope_||!isNestedIn(sym.scope_))) continue; // TODO: why needed?
					if(cast(DeadDecl)sym){
						addDeadMerge(sym).mergedFrom~=sym;
						assert(sym.getId !in rnsymtab||cast(DeadDecl)rnsymtab[sym.getId]);
						continue;
					}
					if(sym.getId !in rnsymtab){
						sym=sc.split(sym,null);
						if(!sc.canForgetAppend(sym)){
							error(format("variable '%s' is not consumed", sym.getName), sym.loc);
							errors=true;
						}
						static if(language==silq){
							if(sc.dependencyTracked(sym))
								sc.pushDependencies(sym,false);
						}
					}
				}
			}
			foreach(sc;scopes[1..$])
				dependencies.joinWith(sc.dependencies);
			foreach(k,v;dependencies.dependencies.dup){
				if(k.getId !in rnsymtab)
					if(dependencyTracked(k))
						removeDependency(k);
			}
			foreach(sc;scopes){
				mergeDeclProps(sc.declProps);
				sc.resetDeclProps();
			}
		}
		foreach(_,dm;deadMerges){
			symtabInsert(dm);
		}
		foreach(sc;scopes){
			static if(language==silq) sc.dependencies.clear();
			sc.symtab.clear();
			sc.rnsymtab.clear();
		}
		foreach(k,v;symtab) assert(this.isNestedIn(v.scope_),text(v));
		foreach(k,v;rnsymtab) assert(this.isNestedIn(v.scope_),text(v));
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
			if(isFirstDef) redefinitionError(d,var);
			else redefinitionError(var,d);
			return null;
		}
		symtabInsert(var);
		var.vtype=type;
		var.scope_=this;
		import ast.semantic_:varDeclSemantic;
		varDeclSemantic(var,this);
		return var;
	}

	Annotation restriction(ref FunctionDef reason){
		return Annotation.none;
	}

	private bool insertCapture(Identifier id,Declaration meaning,Scope outermost){
		if(!meaning) return false;
		if(!meaning.isLinear()&&!id.byRef) return true;
		auto type=id.typeFromMeaning(meaning);
		if(!type) return false;
		return insertCaptureImpl(id,meaning,type,outermost);
	}

	protected bool insertCaptureImpl(Identifier id,Declaration meaning,Expression type,Scope outermost){ return true; }

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

	struct ScopeState{
		bool opEquals(ref ScopeState rhs){
			static if(language==silq){
				if(!dependencies.matches(rhs.dependencies))
					return false;
			}
			import ast.semantic_: typeForDecl;
			bool checkDecl(Declaration decl,Declaration rdecl){
				if(!rdecl) return false;
				import ast.semantic_: typeForDecl;
				if(typeForDecl(decl)==typeForDecl(rdecl))
					return true;
				return false;
			}
			bool compareTables(Declaration[Id] symtab,Declaration[Id] rsymtab){
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
			static if(language==silq)
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
				return dprop.constBlock;
			return null;
		}
		private bool isNonConstVar(Declaration decl){ // TODO: get rid of code duplication?
			auto vd=cast(VarDecl)decl;
			if(!vd||vd.isConst||vd.typeConstBlocker||isConst(vd))
				return false;
			return true;
		}
		Q!(Id,Declaration,Expression,bool)[][2] loopParams(Scope loopScope){ // (name,decl,type,mayChange)
			typeof(return) r;
			foreach(id,decl;rnsymtab){
				import ast.semantic_: typeForDecl;
				auto type=typeForDecl(decl);
				if(!type) continue;
				bool mayChange=isNonConstVar(decl)||decl.isLinear();
				if(!mayChange){
					if(type.isClassical) continue;
				}
				if(mayChange&&loopScope)
					mayChange=decl.mergedFrom.any!(d=>d.scope_ is loopScope);
				bool isConstParamDecl=type.isClassical()||!mayChange||dependencies.canForget(decl);
				Expression.CopyArgs cargs;
				r[isConstParamDecl?0:1]~=q(id,decl,type.copy(cargs),mayChange);
			}
			foreach(i;0..2) sort!"a[0].str<b[0].str"(r[i]);
			return r;
		}
	private:
		static if(language==silq){
			Dependencies dependencies;
			DeclProps declProps;
			Declaration[] toRemove;
			TrackedTemporary[] trackedTemporaries;
		}
		Declaration[Id] symtab;
		Declaration[Id] rnsymtab;
		Declaration[] prevCapturedDecls; // TODO: only store how many there are?
		bool restoreable=false;
	}
	ScopeState getStateSnapshot(bool restoreable=false){
		Declaration[Id] nsymtab=symtab.dup;
		Declaration[Id] nrnsymtab=rnsymtab.dup;
		static if(language==silq){
			DeclProps declProps;
			TrackedTemporary[] trackedTemporaries;
		}
		Declaration[] prevCapturedDecls;
		if(restoreable){
			static if(language==silq){
				declProps=saveDeclProps();
				trackedTemporaries=trackedTemporaries.map!(x=>x.dup).array;
			}
			if(auto fd=getFunction())
				prevCapturedDecls=fd.capturedDecls;
		}
		static if(language==silq){
			return ScopeState(dependencies.dup,declProps,toRemove,trackedTemporaries,nsymtab,nrnsymtab,prevCapturedDecls,restoreable);
		}else{
			return ScopeState(nsymtab,nrnsymtab,prevCaptures,restoreable);
		}
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
			foreach(decl;fd.capturedDecls[state.prevCapturedDecls.length..$]){
				if(decl.getId !in state.rnsymtab||cast(DeadDecl)state.rnsymtab[decl.getId]){
					if(decl.name.id !in state.symtab||cast(DeadDecl)state.symtab[decl.name.id])
						state.symtab[decl.name.id]=decl;
					state.rnsymtab[decl.getId]=decl;
				}
			}
			state.prevCapturedDecls=fd.capturedDecls;
		}
	}

	Declaration updateDecl(Declaration decl){
		auto split=getSplit(decl,true);
		static if(language==silq){
			if(decl !is split)
				replaceDecl(decl,split);
		}
		return split;
	}

	void restoreStateSnapshot(ref ScopeState state)in{
		assert(state.restoreable);
	}do{
		updateStateSnapshot(state);
		static if(language==silq){
			dependencies=state.dependencies;
			resetDeclProps(state.declProps);
			toRemove=state.toRemove;
		}
		symtab.clear();
		foreach(_,decl;state.symtab) symtab[decl.name.id]=updateDecl(decl);
		rnsymtab.clear();
		foreach(_,decl;state.rnsymtab) rnsymtab[decl.getId]=updateDecl(decl);
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
			assert(!!nonZeroIters);
			assert(nonZeroIters.splitFrom is outer);
			assert(!nonZeroIters.scope_||nonZeroIters.scope_ is loopScope);
			auto zeroIters=outer.splitInto[0];
			assert(!!zeroIters);
			assert(zeroIters.splitFrom is outer);
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
			assert(outer.getId in prevStateSnapshot.rnsymtab);
			auto prevOuter=adaptOuter(prevStateSnapshot.rnsymtab[nonZeroIters.getId]);
			assert(prevOuter.splitInto.length==2);
			foreach(k;0..2){
				newOuter.splitInto[k]=prevOuter.splitInto[k];
				newOuter.splitInto[k].splitFrom=newOuter;
			}
			outer=newOuter;
		}
	}
//private: // !!!
	static if(language==silq){
		Dependencies dependencies;
		DeclProps declProps;
	}
	Declaration[Id] symtab;
	Declaration[Id] rnsymtab;
}

class TopScope: Scope{
	private ErrorHandler handler_;
	override @property ErrorHandler handler(){ return handler_; }
	this(ErrorHandler handler){ this.handler_=handler; }
	override bool allowsLinear(){
		return false;
	}
	final void import_(Scope sc){
		imports~=sc;
		// TODO: store a location for better error messages
		// TODO: allow symbol lookup by full path
	}
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
private:
	Scope[] imports; // TODO: local imports, import declarations
}

class NestedScope: Scope{
	Scope parent;
	override @property ErrorHandler handler(){ return parent.handler; }
	this(Scope parent){ this.parent=parent; }

	override Declaration consumeImpl(Declaration odecl,Declaration ndecl,ref Expression type,bool remove,Identifier use)in{
		assert(odecl is ndecl||!remove);
	}do{
		if(this is odecl.scope_) return super.consumeImpl(odecl,ndecl,type,remove,use);
		if(rnsymtab.get(odecl.getId,null) !is odecl) return null;
		import ast.semantic_: typeForDecl;
		if(!type) type=typeForDecl(ndecl);
		auto pdep=Dependency(true);
		if(remove){
			assert(odecl is ndecl);
			if(auto nndecl=parent.consumeImpl(odecl,ndecl,type,true,use)){
				pdep=parent.getDependency(nndecl,true);
				ndecl=nndecl;
				consumedOuter~=ndecl;
				foreach(sc;parent.activeNestedScopes){
					if(this is sc) continue;
					if(auto cdecl=sc.consumeImpl(odecl,ndecl,type,false,use)){
						static if(language==silq){
							if(parent.getFunction() is sc.getFunction()){
								if(sc.dependencyTracked(odecl)) // TODO: can we get rid of this?
									sc.removeDependency(odecl);
								sc.addDependency(odecl,pdep.dup);
							}
							if(odecl !is cdecl)
								sc.replaceDecl(odecl,cdecl);
						}
					}
				}
			}
		}else consumedOuter~=ndecl;
		Declaration result=ndecl;
		if(type){
			symtabRemove(odecl);
			if(dependencyTracked(odecl)){
				// if(odecl !is ndecl) dependencies.replace(odecl,ndecl); // reverse-inherit dependencies through split
				pushDependencies(odecl,true);
			}
			// TODO: backtrace forgets and last usages
			if(auto added=addVariable(ndecl,type,true)){
				result=added;
				splitVar(ndecl,result);
				static if(language==silq){
					if(remove){ // TODO: cen we get rid of this?
						if(parent.getFunction() is getFunction()){
							if(dependencyTracked(odecl))
								removeDependency(odecl);
							addDependency(odecl,pdep.dup);
						}
						assert(odecl !is result);
						replaceDecl(odecl,result);
					}
				}
			}
		}else if(remove){
			symtabRemove(odecl);
			static if(language==silq){
				if(dependencyTracked(odecl))
					pushDependencies(odecl,true);
			}
			if(odecl !is result)
				replaceDecl(odecl,result);
			return result;
		}
		return remove?consume(result,use):result;
	}

	override Declaration lookupImpl(Identifier ident,bool rnsym,bool lookupImports,Lookup kind,Scope origin,DeadDecl[]* failures){
		if(auto decl=lookupHereImpl(ident,rnsym,failures)) return decl;
		return parent.lookupImpl(ident,rnsym,lookupImports,kind,origin,failures);
	}

	override Annotation restriction(ref FunctionDef reason){ return parent.restriction(reason); }
	static if(language==silq){
		override int outerDeclProps(scope int delegate(ref DeclProps) dg){
			return parent.nestedDeclProps(dg);
		}
	}

	override bool isNestedIn(Scope rhs){ return rhs is this || parent.isNestedIn(rhs); }

	protected override bool insertCaptureImpl(Identifier id,Declaration meaning,Expression type,Scope outermost){
		if(this is outermost) return true;
		foreach(sc;parent.activeNestedScopes){
			if(meaning.getId in sc.rnsymtab) // TODO: make sure captures are inserted only once, remove this
				symtabRemove(sc.rnsymtab[meaning.getId]);
			sc.symtabInsert(meaning);
		}
		return parent.insertCaptureImpl(id,meaning,type,outermost);
	}

	override FunctionDef getFunction(){ return parent.getFunction(); }
	override DatDecl getDatDecl(){ return parent.getDatDecl(); }
}

class RawProductScope: NestedScope{
	Annotation annotation;
	this(Scope parent,Annotation annotation){
		super(parent);
		this.annotation=annotation;
	}
	override Annotation restriction(ref FunctionDef reason){
		return annotation;
	}
	void forceClose(){}
}

class CapturingScope(T): NestedScope{
	T decl;
	this(Scope parent,T decl){
		super(parent);
		this.decl=decl;
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
					bool isConsuming=decl.isConsumedCapture(capture);
					DeadDecl[] failures;
					recapture.meaning=origin.lookup(recapture,true,false,isConsuming?Lookup.consuming:Lookup.constant,&failures);
					bool callErrorShown=false;
					void callError(){
						if(callErrorShown) return;
						callErrorShown=true;
						origin.error(format("cannot recursively call function '%s' at this location",decl.name),id.loc);
						id.setSemError();
					}
					if(!recapture.meaning){
						callError();
						origin.note(format("capture '%s' is missing",capture),capture.loc);
						if(failures.length){
							if(auto cd=cast(ConsumedDecl)failures[0]) cd.explain("capture",origin);
							else origin.note("captures cannot be modified on a path leading to a recursive call",id.loc);
						}
						recapture.setSemError();
					}
					recapture.type=recapture.typeFromMeaning;
					assert(recapture.type||recapture.isSemError());
					if(!recapture.isSemError()){
						recapture.setSemCompleted();
						/+import ast.semantic_:typeForDecl;
						auto oldType=typeForDecl(capture);
						if(!isSubtype(recapture.type,oldType)){
							if(!recapture.isSemError()){
								callError();
								origin.note(format("capture '%s' changed type from '%s' to '%s'",capture.name,oldType,recapture.type),capture.loc);
								if(recapture.meaning)
									origin.note("capture is redeclared here",recapture.meaning.loc);
								recapture.setSemError();
							}
						}+/
						if(!recapture.meaning.isDerivedFrom(capture)){
							callError();
							origin.note(format("capture '%s' was modified",capture),capture.loc);
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
		auto vd=cast(VarDecl)meaning;
		bool isConstVar=meaning.isConst||(vd&&vd.typeConstBlocker)||origin.isConst(meaning);
		bool isConstLookup=kind==Lookup.constant||isConstVar;
		static if(language==silq)
		if(type.hasQuantumComponent()){
			if(origin.componentReplacements(meaning).length)
				return null; // not captured, will be replaced (TODO: ok?)
			if(isConstLookup&&!astopt.allowUnsafeCaptureConst){
				if(isConstVar){
					origin.error("cannot capture 'const' quantum variable", id.loc);
					if(vd&&vd.typeConstBlocker){
						import ast.semantic_:typeConstBlockNote;
						typeConstBlockNote(vd,this);
					}
					if(auto read=origin.isConst(meaning))
						origin.note("variable was made 'const' here", read.loc);
					id.setSemError();
					return null;
				}else{
					if(kind==Lookup.constant){
						origin.error("cannot capture quantum variable as constant", id.loc);
						id.setSemError();
					}
				}
			}
			static if(is(T==FunctionDef)){
				auto fd=decl;
				if(fd&&fd.context&&fd.context.vtype==contextTy(true)){
					if(fd.ftype&&fd.ftypeFinal){
						assert(fd.ftype.isClassical_);
						if(!id.isSemError()){
							origin.error("cannot capture quantum variable in classical function", id.loc);
							id.setSemError();
						}
					}else{
						if(fd.sealed) fd.unseal();
						fd.context.vtype=contextTy(false);
						fd.ftype=null;
						import ast.semantic_:setFtype;
						setFtype(fd,true);
					}
				}
			}
		}
		if(!id.lazyCapture){
			bool consumed=!isConstLookup&&(meaning.isLinear()||id.byRef);
			if(!id.isSemError){
				if(consumed) meaning=parent.split(meaning,id);
				decl.addCapture(meaning,id);
			}
			if(consumed){
				symtabInsert(meaning);
				meaning=consume(meaning,id);
				origin.insertCapture(id,meaning,this);
			}
			if(!id.isSemError()){
				if(!consumed) parent.recordAccess(id,meaning);
				parent.recordCapturer(decl,meaning);
			}
		}
		return meaning;
	}
	override Declaration lookupImpl(Identifier ident,bool rnsym,bool lookupImports,Lookup kind,Scope origin,DeadDecl[]* failures){
		if(auto decl=lookupHereImpl(ident,rnsym,failures)) return decl;
		if(auto pdecl=parent.lookupImpl(ident,rnsym,lookupImports,kind,origin,failures)){
			if(auto r=addCapture(ident,pdecl,kind,origin))
				return r;
			return pdecl;
		}
		return null;
	}
}

class FunctionScope: CapturingScope!FunctionDef{
	alias fd=decl;
	this(Scope parent,FunctionDef fd){
		super(parent,fd);
	}
	override Annotation restriction(ref FunctionDef reason){
		reason=fd;
		return fd.annotation;
	}
	void forceClose(){}
	// ~this(){ import std.stdio; writeln(fd.loc.rep); }
	override FunctionDef getFunction(){ return fd; }
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
	this(Scope parent,Annotation restriction_=Annotation.none){
		super(parent);
		if(parent.allowsLinear()) parent.nest(this);
		this.restriction_=restriction_;
	}
	Annotation restriction_;
	override Annotation restriction(ref FunctionDef reason){
		FunctionDef parentReason=null;
		auto parentRestriction=super.restriction(parentReason);
		if(restriction_<parentRestriction){
			reason=parentReason;
			return parentRestriction;
		}
		return restriction_;
	}
}
class AggregateScope: NestedScope{
	this(Scope parent){ super(parent); }
	override bool allowsLinear(){
		return false; // TODO!
	}
}
