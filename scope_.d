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
	void replace(Declaration decl, Dependency rhs, Dependency control){
		if(decl !in dependencies) return;
		dependencies.remove(decl);
		joinWith(rhs);
		joinWith(control);
	}
	void replace(Declaration decl,Declaration ndecl){
		if(decl in dependencies){
			dependencies.remove(decl);
			dependencies.insert(ndecl);
		}
	}
	void remove(Declaration decl,Dependency control)in{
		assert(decl !in control.dependencies);
	}do{
		if(decl in dependencies) joinWith(control);
		dependencies.remove(decl);
	}
	Dependency dup(){
		return Dependency(isTop, dependencies.dup);
	}
	SetX!Id getIds(){
		SetX!Id result;
		foreach(decl;dependencies) result.insert(decl.getId);
		return result;
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
	void pushUp(Declaration removed, Dependency control)in{
		assert(removed in dependencies,text(removed," ",removed.loc," ",dependencies));
	}do{
		Dependency x=dependencies[removed];
		dependencies.remove(removed);
		foreach(k,ref v;dependencies){
			v.replace(removed, x, control);
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
		assert(decl in dependencies||decl.sstate==SemState.error,text(decl," ",dependencies));
	}do{
		if(decl !in dependencies) return true;
		return !dependencies[decl].isTop;
	}
	void clear(){
		dependencies.clear();
	}
	HashMap!(Id,SetX!Id,(a,b)=>a is b,(a)=>a.toHash) getIds(){
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
}

abstract class Scope{
	abstract @property ErrorHandler handler();
	bool allowsLinear(){
		return true;
	}
	bool insert(Declaration decl,bool force=false)in{assert(!decl.scope_);}do{
		if(auto d=symtabLookup(decl.name,false)){
			if(decl.sstate!=SemState.error) redefinitionError(decl, d);
			decl.sstate=SemState.error;
			return false;
		}
		rename(decl);
		if(decl.rename) assert(decl.rename.id !in rnsymtab);
		symtabInsert(decl);
		decl.scope_=this;
		return true;
	}

	void symtabInsert(Declaration decl)in{
		assert(!toPush.canFind(decl));
	}do{
		symtab[decl.name.id]=decl;
		if(decl.rename) rnsymtab[decl.rename.id]=decl;
		/+static if(language==silq){
			if(decl !in dependencies.dependencies){
				addDependency(decl,Dependency(true));
				//imported!"util.io".writeln("!!! ",decl," ",decl.loc);
				//if(decl.loc.line==4&&decl.getName=="x"&&!cast(Parameter)decl) assert(0);
			}
		}+/
	}

	void redefinitionError(Declaration decl, Declaration prev) in{
		assert(decl);
	}do{
		error(format("redefinition of \"%s\"",decl.name), decl.name.loc);
		note("previous definition was here",prev.name.loc);
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
					if(index.sstate==SemState.error) swap(r.write,r.read);
					componentReplacements~=r;
				}
			}
			static DeclProp default_(){
				return DeclProp.init;
			}
			DeclProp dup(){
				return DeclProp(constBlock,componentReplacements.dup);
			}
			DeclProp inherit(){ return default_(); }
		}
		static struct DeclProps{
			private DeclProp[Declaration] props;
			DeclProps dup(){ return DeclProps(props.dup); }
			void clear(){ props.clear(); }
			DeclProp* tryGet(Declaration decl){ return decl in props; }
			ref DeclProp set(Declaration decl,DeclProp prop){
				return props[decl]=prop;
			}
		}
		final DeclProps saveDeclProps(){ return declProps.dup; }
		final void resetDeclProps(DeclProps previous){ declProps=previous; }
		final void resetDeclProps(){ declProps.clear(); }
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
		private final Identifier isConstHere(Declaration decl){
			if(auto r=declProps.tryGet(decl)) return r.constBlock;
			return null;
		}
		final void blockConst(Declaration decl,Identifier constBlock){
			updateDeclProps(decl).constBlock=constBlock;
		}
		final Identifier isConst(Declaration decl){
			foreach(ref prop;nestedDeclProp(decl))
				if(auto r=prop.constBlock)
					return r;
			return null;
		}
		static struct ConstBlockContext{
			private Identifier[Declaration] constBlock;
		}
		final ConstBlockContext saveConst(){
			Identifier[Declaration] constBlock;
			foreach(decl,ref prop;declProps.props) constBlock[decl]=prop.constBlock;
			return ConstBlockContext(constBlock);
		}
		final void resetConst(ConstBlockContext context){
			foreach(decl,constBlock;context.constBlock)
				updateDeclProps(decl).constBlock=constBlock;
			foreach(decl,ref prop;declProps.props)
				if(decl !in context.constBlock)
					prop.constBlock=null;
		}
		final void resetConst(){
			foreach(decl,ref prop;declProps.props)
				prop.constBlock=null;
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

	final Declaration consume(Declaration decl){
		if(decl.name.id !in symtab) return null;
		Expression type;
		if(auto r=consumeImpl(decl,decl,type,true)) // TODO: separate splitting and consuming
			return r;
		return null;
	}
	final void unconsume(Declaration decl){
		toPush=toPush.filter!(pdecl=>pdecl!is decl).array;
		insert(decl);
	}
	Declaration[] consumedOuter;
	Declaration[] splitVars;
	final void splitVar(Declaration splitFrom,Declaration splitInto){
		assert(splitFrom.scope_ !is splitInto.scope_);
		splitFrom.splitInto~=splitInto;
		splitInto.splitFrom=splitFrom;
		splitVars~=splitInto;
	}
	protected Declaration consumeImpl(Declaration odecl,Declaration ndecl,ref Expression type,bool remove)in{
		assert(odecl is ndecl||!remove);
	}do{
		assert(odecl.scope_ is this&&ndecl.scope_ is this);
		if(symtab.get(odecl.name.id,null) !is odecl) return null;
		if(remove){
			symtab.remove(odecl.name.id);
			if(odecl.rename) rnsymtab.remove(odecl.rename.id);
			static if(language==silq)
				toPush~=odecl;
		}else if(odecl !is ndecl){
			assert(odecl.name.id == ndecl.name.id);
			symtab[odecl.name.id]=ndecl;
		}
		return ndecl;
	}
	static if(language==silq){
		/+private+/ Declaration[] toPush;
		final void pushUp(ref Dependency dependency,Declaration removed){
			dependency.replace(removed,dependencies.dependencies[removed],controlDependency);
		}
		final void pushConsumed(){
			foreach(decl;toPush){
				if(!dependencyTracked(decl)) addDefaultDependency(decl); // TODO: ideally can be removed
				dependencies.pushUp(decl,controlDependency);
			}
			toPush=[];
		}
	}

	protected final Declaration symtabLookup(Identifier ident,bool rnsym){
		if(allowMerge) return null;
		auto r=symtab.get(ident.id, null);
		if(rnsym&&!r) r=rnsymtab.get(ident.id,null);
		return r;
	}
	final Declaration peekSymtab(Id name){
		return symtab.get(name,rnsymtab.get(name,null));
	}

	private Declaration postprocessLookup(Identifier id,Declaration meaning,Lookup kind){
		static if(language==silq) enum performConsume=true;
		else auto performConsume=id.byRef;
		if(performConsume){
			if(!meaning) return meaning;
			if(kind==Lookup.consuming){
				bool doConsume=true;
				if(auto vd=cast(VarDecl)meaning){
					if(vd.typeConstBlocker){
						error(format("cannot consume 'const' variable '%s'",id), id.loc);
						import ast.semantic_:typeConstBlockNote;
						typeConstBlockNote(vd,this);
						doConsume=false;
					}
				}
				if(doConsume){
					if(auto read=isConst(meaning)){
						error(format("cannot consume 'const' variable '%s'",id), id.loc);
						note("variable was made 'const' here", read.loc);
						id.sstate=SemState.error;
						doConsume=false;
					}
				}
				if(doConsume&&meaning.scope_){
					assert(!meaning.isConst);
					if(auto nmeaning=consume(meaning))
						meaning=nmeaning;
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

	final Declaration lookup(Identifier ident,bool rnsym,bool lookupImports,Lookup kind){
		auto meaning=lookupImpl(ident,rnsym,lookupImports,kind,this);
		return postprocessLookup(ident,meaning,kind);
	}
	Declaration lookupImpl(Identifier ident,bool rnsym,bool lookupImports,Lookup kind,Scope origin){
		return lookupHereImpl(ident,rnsym);
	}
	Identifier getRenamed(Identifier cname){
		for(;;){ // TODO: quite hacky
			auto d=lookup(cname,true,true,Lookup.probing);
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
	final Declaration lookupHere(Identifier ident,bool rnsym,Lookup kind){
		auto meaning=lookupHereImpl(ident,rnsym);
		return postprocessLookup(ident,meaning,kind);
	}
	final Declaration lookupHereImpl(Identifier ident,bool rnsym){
		auto r=symtabLookup(ident,rnsym);
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
		bool errors=false;
		static if(language==silq){
			foreach(n,d;symtab.dup){
				if(d.isLinear()||d.scope_ is this){
					if(auto p=cast(Parameter)d) if(p.isConst) continue;
					if(!canForgetAppend(loc,d)){
						errors=true;
						import ast.semantic_: unrealizable;
						if(d.sstate!=SemState.error){
							bool show=true;
							if(d.sstate==SemState.error) show=false;
							if(auto vd=cast(VarDecl)d) if(!vd.vtype||unrealizable(vd.vtype)) show=false;
							if(show){
								if(cast(Parameter)d) error(format("%s '%s' is not consumed (perhaps return it or annotate it 'const')",d.kind,d.getName),d.loc);
								else error(format("%s '%s' is not consumed (perhaps return it)",d.kind,d.getName),d.loc);
							}
						}
						d.sstate=SemState.error;
					}else{
						consume(d);
						pushConsumed();
					}
				}
			}
			foreach(n,d;rnsymtab) assert(!d.isLinear()||canForget(d));
		}
		return errors;
	}

	final bool close(){
		return Scope.close(this);
	}

	final bool closeUnreachable(){
		static if(language==silq){
			toPush=[];
		}
		activeNestedScopes=[];
		allowMerge=false;
		foreach(n,d;symtab.dup){
			if(d.isLinear()||d.scope_ is this){
				if(auto p=cast(Parameter)d) if(p.isConst) continue;
				consume(d);
				static if(language==silq){
					pushConsumed();
				}
			}
		}
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
			//imported!"util.io".writeln("ADDING DEFAULT: ",decl," ",Dependency(decl.sstate==SemState.completed&&decl.isLinear));
			addDependency(decl,Dependency(decl.sstate==SemState.completed&&decl.isLinear));
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
			foreach(i,ref dep;deps){
				if(dep[0] in dependencies.dependencies){
					//writeln(dep[0]," ",toPush," ",dependencies)
					dep[1].joinWith(dependencies.dependencies[dep[0]]);
				}
			}
			foreach(decl,dep;deps.map!(x=>x)){
				dep.joinWith(controlDependency);
				dependencies.dependencies[decl]=dep;
			}
		}

		final bool dependencyTracked(Declaration decl){
			return !!(decl in dependencies.dependencies);
		}
		final Dependency getDependency(Identifier id)in{
			assert(id.sstate==SemState.completed);
			assert(!!id.meaning);
		}do{
			return getDependency(id.meaning);
		}
		final Dependency getDependency(Declaration decl)in{
			assert(decl.sstate==SemState.completed,text(decl," ",decl.sstate));
		}do{
			if(!dependencyTracked(decl)) addDefaultDependency(decl); // TODO: ideally can be removed
			return dependencies.dependencies[decl];
		}

		bool canForget(Declaration decl)in{
			assert(toPush.length==0,text(toPush));
		}do{
			if(decl.sstate==SemState.error) return true;
			assert(decl.sstate==SemState.completed,text(decl," ",decl.sstate));
			import ast.semantic_:typeForDecl;
			auto type=typeForDecl(decl);
			if(type&&type.isClassical) return true; // TODO: ensure classical variables have dependency `{}` instead?
			return dependencies.canForget(decl);
		}

		Declaration[] forgottenVars;
		final bool canForgetAppend(T)(T cause,Declaration decl)if(is(T==Scope)||is(T==ReturnExp)){
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
		static if(language==silq){
			assert(scopes.all!(sc=>sc.toPush.length==0));
		}
		//debug assert(allowMerge);
	}do{
		// scope(exit) writeln("MERGING\n",this,"\n",scopes.map!(sc=>text("nested: ",sc,"\nconsumed: ",sc.consumedOuter,"\nsplit: ",sc.splitVars,"\nmergedVars: ",sc.mergedVars,"\nproducedOuter: ",producedOuter)).join("\n"),"\nEND MERGE\n");
		static if(language==silq){
			toPush=[];
		}
		assert(scopes==activeNestedScopes,text(scopes," ",activeNestedScopes));
		activeNestedScopes=[];
		allowMerge=false;
		symtab=scopes[0].symtab.dup;
		rnsymtab=scopes[0].rnsymtab.dup;
		bool errors=false;
		foreach(psym;symtab.dup){
			auto sym=psym;
			import ast.semantic_: typeForDecl;
			bool symExists=true,needMerge=sym.scope_ is scopes[0];
			void removeOSym(Scope sc,Declaration osym){
				sc.symtab.remove(osym.name.id);
				if(osym.rename) sc.rnsymtab.remove(osym.rename.id);
			}
			void removeSym(){
				removeOSym(this,sym);
				symExists=false;
			}
			void promoteSym(Expression ntype){
				symtab.remove(sym.name.id);
				if(sym.rename) rnsymtab.remove(sym.rename.id);
				addVariable(sym,ntype,true);
				sym=symtab[sym.name.id];
				needMerge=true;
			}
			foreach(sc;scopes[1..$]){
				if(sym.name.id !in sc.symtab){
					removeSym();
					static if(language==silq){
						if(!scopes[0].canForgetAppend(sym)){
							error(format("variable '%s' is not consumed", sym.getName), sym.loc);
							errors=true;
						}
					}
				}else{
					auto osym=sc.symtab[sym.name.id];
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
									if(!scopes[0].canForgetAppend(sym)|!sc.canForgetAppend(osym)){
										error(format("variable '%s' is not consumed", sym.getName), sym.loc);
										if(!nt) note(format("declared with incompatible types '%s' and '%s' in different branches",ot,st), osym.loc);
										errors=true;
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
					scopes[0].mergeVar(psym,sym);
					static if(language==silq)
						scopes[0].dependencies.replace(psym,sym);
					foreach(sc;scopes[1..$]){
						assert(sym.name.id in sc.symtab);
						auto osym=sc.symtab[sym.name.id];
						sc.mergeVar(osym,sym);
						static if(language==silq)
							sc.dependencies.replace(osym,sym);
					}
				}else sym.scope_=this;
				producedOuter~=sym;
			}
		}
		static if(language==silq){
			/+imported!"util.io".writeln("/---");
			scopes[].each!((sc){
				imported!"util.io".writeln(sc.dependencies);
				foreach(decl,ref dep;sc.dependencies.dependencies){ // !!!
					imported!"util.io".writeln(cast(void*)decl);
				}
			});+/
			dependencies=scopes[0].dependencies.dup;
			foreach(sc;scopes[1..$])
				dependencies.joinWith(sc.dependencies);
			/+imported!"util.io".writeln("----");
			imported!"util.io".writeln(dependencies);
			foreach(decl,ref dep;dependencies.dependencies){ // !!!
				imported!"util.io".writeln(cast(void*)decl);
				assert(decl.getId in rnsymtab);
				assert(rnsymtab[decl.getId] is decl);
			}
			imported!"util.io".writeln("---/");+/
		}
		static if(language==silq){
			foreach(sc;scopes[1..$]){
				foreach(sym;sc.symtab){
					if(sym.name.id !in symtab){
						if(!sc.canForgetAppend(sym)){
							error(format("variable '%s' is not consumed", sym.getName), sym.loc);
							errors=true;
						}
					}
				}
			}
		}
		foreach(sc;scopes){
			static if(language==silq) sc.dependencies.clear();
			sc.symtab.clear();
			sc.rnsymtab.clear();
		}
		static if(language==silq){
			foreach(k,v;dependencies.dependencies.dup){
				if(k.getId !in symtab && k.getId !in rnsymtab)
					dependencies.dependencies.remove(k);
			}
		}
		foreach(k,v;symtab) assert(this.isNestedIn(v.scope_),text(v));
		foreach(k,v;rnsymtab) assert(this.isNestedIn(v.scope_),text(v));
		return errors;
	}

	final Declaration addVariable(Declaration decl,Expression type,bool isFirstDef=false){
		auto id=new Identifier(decl.name.id);
		id.loc=decl.name.loc;
		auto var=new VarDecl(id);
		var.loc=decl.loc;
		if(decl.rename){
			var.rename=new Identifier(decl.rename.id);
			var.rename.loc=decl.rename.loc;
		}
		if(auto d=symtabLookup(var.name,false)){
			if(isFirstDef) redefinitionError(d,var);
			else redefinitionError(var,d);
			return null;
		}
		/+static if(language==silq){
			if(decl !in dependencies.dependencies||toPush.canFind(decl))
				addDefaultDependency(decl);
		}+/
		symtabInsert(var);
		var.vtype=type;
		var.scope_=this;
		import ast.semantic_:varDeclSemantic;
		varDeclSemantic(var,this);
		return var;
	}

	Annotation restriction(){
		return Annotation.none;
	}

	private bool insertCapture(Identifier id,Declaration meaning,Scope outermost){
		if(!meaning) return false;
		if(!meaning.isLinear()) return true;
		auto type=id.typeFromMeaning(meaning);
		if(!type) return false;
		return insertCaptureImpl(id,meaning,type,outermost);
	}

	protected bool insertCaptureImpl(Identifier id,Declaration meaning,Expression type,Scope outermost){ return true; }

	abstract FunctionDef getFunction();
	abstract DatDecl getDatDecl();
	final int all(T)(int delegate(T) dg){
		foreach(k,v;symtab){
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
			foreach(name,decl;rhs.symtab)
				if(name !in symtab)
					return false;
			foreach(name,decl;symtab){
				import ast.semantic_: typeForDecl;
				if(auto rdecl=name in rhs.symtab){
					if(typeForDecl(decl)!=typeForDecl(*rdecl))
						return false;
				}else return false;
			}
			return true;
		}
		string toString(){
			string r;
			static if(language==silq)
				r~=text("dependencies: ",dependencies,"\n");
			import ast.semantic_: typeForDecl;
			import std.array: join;
			r~=text("{",symtab.values.map!(decl=>text(decl.getName,": ",typeForDecl(decl))).join(", "),"}");
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
		Q!(Id,Expression,bool,Location)[] loopParams(bool constParams){ // (name,type,mayChange,loc)
			typeof(return) r;
			foreach(id,decl;symtab){
				import ast.semantic_: typeForDecl;
				auto type=typeForDecl(decl);
				if(!type) continue;
				bool mayChange=isNonConstVar(decl)||decl.isLinear();
				if(!mayChange){
					if(type.isClassical) continue;
				}
				bool isConstParamDecl=type.isClassical()||dependencies.canForget(decl)||!mayChange;
				if(constParams!=isConstParamDecl) continue;
				Expression.CopyArgs cargs;
				r~=q(id,type.copy(cargs),mayChange,decl.loc);
			}
			sort!"a[0].str<b[0].str"(r);
			return r;
		}
	private:
		static if(language==silq){
			Dependencies dependencies;
			DeclProps declProps;
		}
		Declaration[Id] symtab;
		bool restoreable=false;
	}
	ScopeState getStateSnapshot(bool restoreable=false)in{
		static if(language==silq)
			assert(!toPush.length);
	}do{
		Declaration[Id] nsymtab;
		foreach(_,decl;symtab) nsymtab[decl.name.id]=decl;
		static if(language==silq){
			return ScopeState(dependencies.dup,restoreable?saveDeclProps:DeclProps.init,nsymtab,restoreable);
		}else{
			return ScopeState(nsymtab,restoreable);
		}
	}
	private Declaration getSplit(Declaration decl,bool clearSplitInto=false){
		if(decl.scope_ is this){
			if(clearSplitInto)
				decl.splitInto=[];
			return decl;
		}
		if(decl.splitInto.length==0)
			return decl;
		foreach(ndecl;decl.splitInto){
			if(this.isNestedIn(ndecl.scope_))
					return getSplit(ndecl);
		}
		assert(0);
	}
	void restoreStateSnapshot(ref ScopeState state)in{
		static if(language==silq){
			assert(!toPush.length);
		}
		assert(state.restoreable);
	}do{
		static if(language==silq){
			dependencies=state.dependencies;
			resetDeclProps(state.declProps);
		}
		symtab.clear();
		foreach(_,decl;state.symtab) symtab[decl.name.id]=getSplit(decl,true);
		foreach(_,decl;symtab) if(decl.rename.id !in rnsymtab) rnsymtab[decl.rename.id]=decl; // TODO: ok?
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
			if(outer.sstate==SemState.error) continue;
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
			if(outer.name.id !in origStateSnapshot.symtab){
				// declaration captured from outer scope
				auto fd=getFunction();
				assert(!!fd);
				foreach(decl;fd.capturedDecls){
					if(decl.name.id == outer.name.id){
						newOuter=adaptOuter(decl);
						break;
					}
				}
			}else newOuter=adaptOuter(origStateSnapshot.symtab[outer.name.id]);
			assert(!!newOuter);
			assert(newOuter.splitInto.length==2);
			assert(!newOuter.scope_||newOuter.scope_ is this);
			assert(outer.name.id in prevStateSnapshot.symtab);
			auto prevOuter=adaptOuter(prevStateSnapshot.symtab[nonZeroIters.name.id]);
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
	override Declaration lookupImpl(Identifier ident,bool rnsym,bool lookupImports,Lookup kind,Scope origin){
		if(auto d=super.lookupImpl(ident,rnsym,lookupImports,kind,origin)) return d;
		if(lookupImports){
			Declaration[] ds;
			foreach(sc;imports) if(auto d=sc.lookupImpl(ident,rnsym,false,kind,origin)) ds~=d;
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

	override Declaration consumeImpl(Declaration odecl,Declaration ndecl,ref Expression type,bool remove)in{
		assert(odecl is ndecl||!remove);
	}do{
		if(this is odecl.scope_) return super.consumeImpl(odecl,ndecl,type,remove);
		if(symtab.get(odecl.name.id,null) !is odecl) return null;
		import ast.semantic_: typeForDecl;
		if(!type) type=typeForDecl(ndecl);
		if(remove){
			assert(odecl is ndecl);
			if(auto nndecl=parent.consumeImpl(odecl,ndecl,type,true)){
				ndecl=nndecl;
				consumedOuter~=ndecl;
				foreach(sc;parent.activeNestedScopes){
					if(this is sc) continue;
					if(sc.consumeImpl(odecl,ndecl,type,false)){
						static if(language==silq){
							sc.pushConsumed();
						}
					}
				}
			}
		}else consumedOuter~=ndecl;
		Declaration result=ndecl;
		if(remove||type){
			symtab.remove(odecl.name.id);
			if(odecl.rename) rnsymtab.remove(odecl.rename.id);
			static if(language==silq){
				if(type) removeDependency(odecl);
			}
		}
		if(type){
			static if(language==silq){
				if(parent.getFunction() is getFunction() && odecl in parent.dependencies.dependencies){
					auto parentDep=parent.dependencies.dependencies[odecl];
					addDependency(ndecl,parentDep.dup);
				}else addDefaultDependency(ndecl);
			}
			if(auto added=addVariable(ndecl,type,true))
				result=added;
			splitVar(ndecl,result);
			dependencies.replace(ndecl,result); // TODO: fix
			/+imported!"util.io".writeln("SPLITTING: ",ndecl," ",result," ",cast(void*)ndecl," ",cast(void*)result);
			foreach(decl,ref dep;dependencies.dependencies){ // !!!
				imported!"util.io".writeln(decl," ",cast(void*)decl);
				assert(decl.getId in rnsymtab);
				assert(rnsymtab[decl.getId] is decl);
			}
			imported!"util.io".writeln("=====");+/
		}
		if(!remove) return result;
		return type?consume(result):result;
	}

	override Declaration lookupImpl(Identifier ident,bool rnsym,bool lookupImports,Lookup kind,Scope origin){
		if(auto decl=lookupHereImpl(ident,rnsym)) return decl;
		return parent.lookupImpl(ident,rnsym,lookupImports,kind,origin);
	}

	override Annotation restriction(){ return parent.restriction(); }
	static if(language==silq){
		override int outerDeclProps(scope int delegate(ref DeclProps) dg){
			return parent.nestedDeclProps(dg);
		}
	}

	override bool isNestedIn(Scope rhs){ return rhs is this || parent.isNestedIn(rhs); }

	protected override bool insertCaptureImpl(Identifier id,Declaration meaning,Expression type,Scope outermost){
		if(this is outermost) return true;
		foreach(sc;parent.activeNestedScopes)
			sc.symtabInsert(meaning);
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
	override Annotation restriction(){
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
		if(type&&type.isClassical()&&id.byRef){
			origin.error("cannot consume classical variable from outer scope", id.loc);
			id.sstate=SemState.error;
		}
		if(!meaning.scope_||!meaning.scope_.getFunction()) return null; // no need to capture global declarations
		if(id.sstate==SemState.error) return null;
		//imported!"util.io".writeln("capturing ",meaning," into ",decl);
		static if(is(T==FunctionDef)){
			// for recursive nested closures
			//auto fd2=chain(meaning.derivedSequence.map!(x=>cast(FunctionDef)x).filter!(x=>!!x),only(null)).front;
			if(meaning.isSplitFrom(decl)/+||fd2&&!fd2.isLinear()+/){
				//if(fd2&&!fd2.isLinear()) meaning=fd2; // TODO: this is a bit hacky
				//if(fd2&&fd2.sstate!=SemState.completed) fd2.seal();
				if(meaning.isSplitFrom(decl)) decl.seal();
				id.lazyCapture=true;
				foreach(capture;decl.capturedDecls){
					if(capture.isSplitFrom(decl)) continue;
					auto recapture=new Identifier(capture.name.id);
					recapture.loc=id.loc;
					import ast.semantic_:lookupMeaning,typeForDecl;
					lookupMeaning(recapture,kind,origin);
					bool callErrorShown=false;
					void callError(){
						if(callErrorShown) return;
						callErrorShown=true;
						origin.error(format("cannot recursively call function '%s' at this location",decl.name),id.loc);
						id.sstate=SemState.error;
					}
					if(!recapture.meaning){
						callError();
						origin.note(format("capture '%s' is missing",capture.name),capture.loc);
						recapture.sstate=SemState.error;
					}
					recapture.type=recapture.typeFromMeaning;
					assert(recapture.type||recapture.sstate==SemState.error);
					if(recapture.sstate!=SemState.error){
						recapture.sstate=SemState.completed;
						auto oldType=typeForDecl(capture);
						/+if(!isSubtype(recapture.type,oldType)){
							if(recapture.sstate!=SemState.error){
								callError();
								origin.note(format("capture '%s' changed type from '%s' to '%s'",capture.name,oldType,recapture.type),capture.loc);
								if(recapture.meaning)
									origin.note("capture is redeclared here",recapture.meaning.loc);
								recapture.sstate=SemState.error;
							}
						}+/
						if(!recapture.meaning.isDerivedFrom(capture)){
							callError();
							origin.note(format("capture '%s' was modified",capture.name),capture.loc);
						}
					}
					if(recapture.sstate==SemState.error)
						id.sstate=SemState.error;
				}
			}else if(decl.sealed&&meaning.isLinear()&&meaning !in decl.captures){
				/+if(id.sstate!=SemState.error){
					origin.error("capturing additional quantum variables after a recursive call is not supported yet", id.loc);
					id.sstate=SemState.error;
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
					id.sstate=SemState.error;
					return null;
				}else{
					if(kind==Lookup.constant){
						origin.error("cannot capture quantum variable as constant", id.loc);
						id.sstate=SemState.error;
					}
				}
			}
			static if(is(T==FunctionDef)){
				auto fd=decl;
				if(fd&&fd.context&&fd.context.vtype==contextTy(true)){
					if(fd.ftype&&fd.ftypeFinal){
						assert(fd.ftype.isClassical_);
						if(id.sstate!=SemState.error){
							origin.error("cannot capture quantum variable in classical function", id.loc);
							id.sstate=SemState.error;
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
			if(!isConstLookup&&meaning.isLinear()){
				symtabInsert(meaning);
				meaning=consume(meaning);
				origin.insertCapture(id,meaning,this);
			}
			if(id.sstate!=SemState.error)
				decl.addCapture(meaning,id);
		}
		return meaning;
	}
	override Declaration lookupImpl(Identifier ident,bool rnsym,bool lookupImports,Lookup kind,Scope origin){
		if(auto decl=lookupHereImpl(ident,rnsym)) return decl;
		if(auto decl=parent.lookupImpl(ident,rnsym,lookupImports,kind,origin)){
			if(auto r=addCapture(ident,decl,kind,origin))
				return r;
			return decl;
		}
		return null;
	}
}

class FunctionScope: CapturingScope!FunctionDef{
	alias fd=decl;
	this(Scope parent,FunctionDef fd){
		super(parent,fd);
	}
	override Annotation restriction(){
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
	override Annotation restriction(){
		return max(restriction_,super.restriction());
	}
}
class AggregateScope: NestedScope{
	this(Scope parent){ super(parent); }
	override bool allowsLinear(){
		return false; // TODO!
	}
}
