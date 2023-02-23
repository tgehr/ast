// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.scope_;
import astopt;

import std.format, std.conv, std.algorithm, std.stdio;
import std.typecons:Q=Tuple,q=tuple;
import ast.lexer, ast.expression, ast.declaration, ast.type, ast.error;
import util, util.hashtable: HashMap;

static if(language==silq){
struct Dependency{
	bool isTop;
	SetX!string dependencies;
	void joinWith(Dependency rhs){
		if(isTop) return;
		if(rhs.isTop){
			this=rhs;
			return;
		}
		foreach(x;rhs.dependencies)
			dependencies.insert(x);
	}
	void replace(string name, Dependency rhs, Dependency control){
		if(name !in dependencies) return;
		dependencies.remove(name);
		joinWith(rhs);
		joinWith(control);
	}
	void rename(string decl,string ndecl){
		if(decl in dependencies){
			dependencies.remove(decl);
			dependencies.insert(ndecl);
		}
	}
	void remove(string decl,Dependency control){
		if(decl in dependencies) joinWith(control);
		dependencies.remove(decl);
	}
	Dependency dup(){
		return Dependency(isTop, dependencies.dup);
	}
}

struct Dependencies{
	HashMap!(string,Dependency,(a,b)=>a==b,(a)=>typeid(a).getHash(&a)) dependencies;
	void joinWith(Dependencies rhs){
		foreach(k,ref v;dependencies){
			if(k in rhs.dependencies){
				v.joinWith(rhs.dependencies[k]);
				if(k in v.dependencies)
					v=Dependency(true);
			}
		}
	}
	void pushUp(string removed, Dependency control)in{
		assert(removed in dependencies,removed);
	}do{
		Dependency x=dependencies[removed];
		dependencies.remove(removed);
		foreach(k,ref v;dependencies){
			v.replace(removed, x, control);
			if(k in v.dependencies)
				v=Dependency(true);
		}
	}
	void rename(string decl,string ndecl)in{
		assert(decl in dependencies);
		assert(ndecl !in dependencies);
	}do{
		foreach(k,ref v;dependencies) v.rename(decl,ndecl);
		dependencies[ndecl]=dependencies[decl];
		dependencies.remove(decl);
	}
	Dependencies dup(){
		typeof(Dependencies.dependencies) result;
		foreach(k,ref v;dependencies)
			result[k]=v.dup;
		return Dependencies(result);
	}
	bool canForget(string decl)in{
		assert(decl in dependencies,text(decl," ",dependencies));
	}do{
		return !dependencies[decl].isTop;
	}
	void clear(){
		dependencies.clear();
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
		if(auto d=symtabLookup(decl.name,false,Lookup.probing)){
			if(decl.sstate!=SemState.error) redefinitionError(decl, d);
			decl.sstate=SemState.error;
			return false;
		}
		rename(decl);
		symtab[decl.name.ptr]=decl;
		if(decl.rename){
			assert(decl.rename.ptr !in rnsymtab);
			rnsymtab[decl.rename.ptr]=decl;
		}
		static if(language==silq){
			if(decl.getName !in dependencies.dependencies||toPush.canFind(decl.getName))
				addDependency(decl,Dependency(true));
		}
		decl.scope_=this;
		return true;
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
			static struct ComponentReplacement{
				IndexExp write;
				string name;
				IndexExp read;
			}
			ComponentReplacement[] componentReplacements;
			void nameIndex(IndexExp index,string name){
				auto r=ComponentReplacement(index,name,IndexExp.init);
				if(index.sstate==SemState.error) swap(r.write,r.read);
				componentReplacements~=r;
			}
			static DeclProp default_(){
				return DeclProp.init;
			}
			DeclProp dup(){
				return DeclProp(constBlock,componentReplacements.dup);
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
		}
		final DeclProps saveDeclProps(){ return declProps.dup; }
		final void resetDeclProps(DeclProps previous){ declProps=previous; }
		final void resetDeclProps(){ declProps.clear(); }
		DeclProp* getDeclProp(Declaration decl,bool failed=false){
			if(failed) return null;
			return declProps.tryGet(decl);
		}
		final ref DeclProp updateDeclProps(Declaration decl){
			if(auto r=declProps.tryGet(decl)) return *r;
			if(auto r=getDeclProp(decl,true)) return declProps.set(decl,r.dup);
			return declProps.set(decl,DeclProp.default_());
		}
		private Identifier isConstHere(Declaration decl){
			if(auto r=declProps.tryGet(decl)) return r.constBlock;
			return null;
		}
		final void blockConst(Declaration decl,Identifier constBlock){
			updateDeclProps(decl).constBlock=constBlock;
		}
		final Identifier isConst(Declaration decl){
			if(auto props=getDeclProp(decl)) return props.constBlock;
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
		final void resetComponentReplacements(){
			foreach(decl,ref prop;declProps.props)
				prop.componentReplacements=[];
		}
		final DeclProp.ComponentReplacement[] allComponentReplacements(){ // TODO: get rid of this
			typeof(return) r;
			foreach(decl,ref prop;declProps.props)
				r~=prop.componentReplacements;
			return r;
		}
		static struct ComponentReplacementContext{
			private DeclProp.ComponentReplacement[][Declaration] componentReplacements;
		}
		final ComponentReplacementContext moveComponentReplacements(){ // TODO: get rid of this
			DeclProp.ComponentReplacement[][Declaration] r;
			foreach(decl,ref prop;declProps.props){
				r[decl]=prop.componentReplacements;
				prop.componentReplacements=[];
			}
			return typeof(return)(r);
		}
		final void restoreComponentReplacements(ComponentReplacementContext previous){ // TODO: get rid of this
			foreach(decl,crepls;previous.componentReplacements)
				updateDeclProps(decl).componentReplacements=crepls;
		}
		final DeclProp.ComponentReplacement[] componentReplacements(Declaration decl){
			if(auto r=declProps.tryGet(decl)) return r.componentReplacements;
			return [];
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

	final bool consume(Declaration decl){
		if(decl.name.ptr !in symtab) return false;
		symtab.remove(decl.name.ptr);
		if(decl.rename) rnsymtab.remove(decl.rename.ptr);
		static if(language==silq) toPush~=decl.getName;
		return true;
	}
	static if(language==silq){
		/+private+/ string[] toPush;
		final void pushUp(ref Dependency dependency,string removed){
			dependency.replace(removed,dependencies.dependencies[removed],controlDependency);
		}
		final void pushConsumed(){
			foreach(name;toPush)
				dependencies.pushUp(name,controlDependency);
			toPush=[];
		}
	}

	protected final Declaration symtabLookup(Identifier ident,bool rnsym,Lookup kind){
		if(allowMerge) return null;
		auto r=symtab.get(ident.ptr, null);
		if(rnsym&&!r) r=rnsymtab.get(ident.ptr,null);
		static if(language==silq){
			if(kind==Lookup.consuming&&r&&r.isLinear()){
				bool doConsume=true;
				if(auto vd=cast(VarDecl)r){
					import ast.semantic_:typeConstBlockNote;
					if(vd.typeConstBlocker){
						error(format("cannot consume 'const' variable '%s'",ident), ident.loc);
						typeConstBlockNote(vd,this);
						doConsume=false;
					}
				}
				if(doConsume){
					if(auto read=isConst(r)){
						error(format("cannot consume 'const' variable '%s'",ident), ident.loc);
						note("variable was made 'const' here", read.loc);
						ident.sstate=SemState.error;
						doConsume=false;
					}
				}
				if(doConsume){
					if(auto vd=cast(VarDecl)r) assert(!vd.isConst);
					consume(r);
				}
			}
			if(kind==Lookup.constant&&r&&r.isLinear()){
				if(!isConstHere(r))
					blockConst(r,ident);
			}
		}
		return r;
	}
	Declaration lookup(Identifier ident,bool rnsym,bool lookupImports,Lookup kind){
		return lookupHere(ident,rnsym,kind);
	}
	Identifier getRenamed(Identifier cname){
		for(;;){ // TODO: quite hacky
			auto d=lookup(cname,true,true,Lookup.probing);
			import ast.semantic_: isBuiltIn;
			if(!d&&!isBuiltIn(cname)) break;
			auto loc=cname.loc;
			cname=new Identifier(cname.name~"'");
			cname.loc=loc;
		}
		return cname;
	}
	protected final void rename(Declaration decl){
		auto cname=decl.rename?decl.rename:decl.name;
		decl.rename=getRenamed(cname);
	}
	final Declaration lookupHere(Identifier ident,bool rnsym,Lookup kind){
		auto r = symtabLookup(ident,rnsym,kind);
		return r;
	}

	bool isNestedIn(Scope rhs){ return rhs is this; }

	void error(lazy string err, Location loc){handler.error(err,loc);}
	void note(lazy string err, Location loc){handler.note(err,loc);}

	final bool close(){
		bool errors=false;
		static if(language==silq){
			foreach(n,d;symtab.dup){
				if(d.isLinear()){
					if(!canForgetAppend(d)){
						errors=true;
						import ast.semantic_: unrealizable;
						if(d.sstate!=SemState.error){
							bool show=true;
							if(auto vd=cast(VarDecl)d) if(!vd.vtype||unrealizable(vd.vtype)) show=false;
							if(show){
								if(cast(Parameter)d) error(format("%s '%s' is not consumed (perhaps return it or annotate it 'const')",d.kind,d.getName),d.loc);
								else error(format("%s '%s' is not consumed",d.kind,d.getName),d.loc);
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

	static if(language==silq){
		auto controlDependency=Dependency(false,SetX!string.init);
		void addControlDependency(Dependency dep){
			controlDependency.joinWith(dep);
		}

		void addDependency(Declaration decl, Dependency dep){
			addDependencies([q(decl.getName,dep)]);
		}
		void removeDependency(string name){
			dependencies.dependencies.remove(name);
		}
		void addDependencies(scope Q!(string,Dependency)[] deps){
			foreach(i,ref dep;deps){
				if(dep[0] in dependencies.dependencies){
					if(toPush.canFind(dep[0])){  // recently consumed
						auto ndecl="`renamed`"~dep[0];
						//assert(ndecl !in dependencies.dependencies);
						foreach(ref x;toPush) if(x == dep[0]) x=ndecl;
						dependencies.rename(dep[0],ndecl);
						controlDependency.rename(dep[0],ndecl);
						foreach(j,ref odep;deps){
							if(i==j) continue;
							odep[1].rename(dep[0],ndecl);
						}
					}else{
						//writeln(dep[0]," ",toPush," ",dependencies)
						dep[1].joinWith(dependencies.dependencies[dep[0]]);
					}
				}
			}
			foreach(rename,dep;deps.map!(x=>x)){
				dep.joinWith(controlDependency);
				if(rename in dep.dependencies) dependencies.dependencies[rename]=Dependency(true);
				else dependencies.dependencies[rename]=dep;
			}
		}

		final bool dependencyTracked(Identifier id){
			return !!(id.name in dependencies.dependencies);
		}
		final Dependency getDependency(Identifier id)in{
			assert(id.sstate==SemState.completed);
		}do{
			return dependencies.dependencies.get(id.name,Dependency(true));
		}
		final Dependency getDependency(Declaration decl)in{
			assert(decl.sstate==SemState.completed,text(decl," ",decl.sstate));
		}do{
			return dependencies.dependencies.get(decl.getName,Dependency(true));
		}

		bool canForget(Declaration decl)in{
			assert(toPush.length==0,text(toPush));
		}do{
			if(decl.sstate==SemState.error) return true;
			assert(decl.sstate==SemState.completed);
			return dependencies.canForget(decl.getName);
		}

		Declaration[] forgottenVars;
		final bool canForgetAppend(Declaration decl){
			if(canForget(decl)){
				forgottenVars~=decl;
				return true;
			}
			return false;
		}
	}
	Q!(Declaration,Expression)[] mergedVars;
	final void mergeVar(Declaration decl,Expression ntype){
		mergedVars~=q(decl,ntype);
	}

	bool allowMerge=false;
	SetX!NestedScope activeNestedScopes;
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
		activeNestedScopes.insert(r);
	}

	bool merge(bool quantumControl,NestedScope[] scopes...)in{
		assert(scopes.length);
		static if(language==silq){
			assert(toPush.length==0);
			assert(scopes.all!(sc=>sc.toPush.length==0));
		}
		//debug assert(allowMerge);
	}do{
		foreach(sc;scopes)
			activeNestedScopes.remove(sc);
		allowMerge=false;
		static if(language==silq){
			dependencies=scopes[0].dependencies.dup;
			foreach(sc;scopes[1..$])
				dependencies.joinWith(sc.dependencies);
		}
		symtab=scopes[0].symtab.dup;
		rnsymtab=scopes[0].rnsymtab.dup;
		bool errors=false;
		foreach(sym;symtab.dup){
			foreach(sc;scopes[1..$]){
				if(sym.name.ptr !in sc.symtab){
					symtab.remove(sym.name.ptr);
					if(sym.rename) rnsymtab.remove(sym.rename.ptr);
					static if(language==silq){
						if(sym.isLinear()&&!scopes[0].canForgetAppend(sym)){
							error(format("variable '%s' is not consumed", sym.getName), sym.loc);
							errors=true;
						}
					}
				}else{
					auto osym=sc.symtab[sym.name.ptr];
					if((sym.scope_ is scopes[0]||osym.scope_ is sc)){
						import ast.semantic_: typeForDecl;
						auto ot=typeForDecl(osym),st=typeForDecl(sym);
						if(!ot) ot=st;
						if(!st) st=ot;
						if(ot&&st){
							auto nt=ot&&st?joinTypes(ot,st):null;
							if(!nt||quantumControl&&nt.hasClassicalComponent()){
								symtab.remove(sym.name.ptr);
								if(sym.rename) rnsymtab.remove(sym.rename.ptr);
								static if(language==silq){
									if(sym.isLinear()&&!scopes[0].canForgetAppend(sym)||
									   osym.isLinear()&&!sc.canForgetAppend(osym)){
										error(format("variable '%s' is not consumed", sym.getName), sym.loc);
										if(!nt) note(format("declared with incompatible types '%s' and '%s' in different branches",ot,st), osym.loc);
										errors=true;
									}
								}
							}
							// TODO: automatically promote to quantum if possible
							if(st&&nt&&st!=nt){ // TODO: more efficient implementation for more than 2 scopes
								symtab.remove(sym.name.ptr);
								if(sym.rename) rnsymtab.remove(sym.rename.ptr);
								addVariable(sym,nt);
								scopes[0].mergeVar(sym,nt);
							}
							if(ot&&nt&&ot!=nt) sc.mergeVar(osym,nt);
						}
					}
				}
			}
		}
		static if(language==silq){
			foreach(sc;scopes[1..$]){
				foreach(sym;sc.symtab){
					if(sym.name.ptr !in symtab){
						if(sym.isLinear()&&!sc.canForgetAppend(sym)){
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
				if(k.ptr !in symtab && k.ptr !in rnsymtab)
					dependencies.dependencies.remove(k);
			}
		}
		foreach(k,v;symtab) if(!this.isNestedIn(v.scope_)) v.scope_=this;
		foreach(k,v;rnsymtab) if(!this.isNestedIn(v.scope_)) v.scope_=this;
		return errors;
	}

	final bool addVariable(Declaration decl,Expression type,bool isFirstDef=false){
		auto id=new Identifier(decl.name.name);
		id.loc=decl.name.loc;
		auto var=new VarDecl(id);
		var.loc=decl.loc;
		if(decl.rename){
			var.rename=new Identifier(decl.rename.name);
			var.rename.loc=decl.rename.loc;
		}
		if(auto d=symtabLookup(var.name,false,Lookup.probing)){
			if(isFirstDef) redefinitionError(d,var);
			else redefinitionError(var,d);
			return false;
		}
		static if(language==silq){
			if(decl.getName !in dependencies.dependencies||toPush.canFind(decl.getName))
				addDependency(decl,Dependency(true));
		}
		symtab[var.name.ptr]=var;
		if(var.rename) rnsymtab[var.rename.ptr]=var;
		var.vtype=type;
		var.scope_=this;
		import ast.semantic_:varDeclSemantic;
		varDeclSemantic(var,this);
		return var.sstate==SemState.completed;
	}

	Annotation restriction(){
		return Annotation.none;
	}

	private bool insertCapture(Identifier id,Scope outermost){
		if(!id.meaning) return false;
		if(!id.meaning.isLinear()) return true;
		import ast.semantic_: typeForDecl;
		auto type=typeForDecl(id.meaning);
		if(!type) return false;
		return insertCaptureImpl(id,type,outermost);
	}

	protected bool insertCaptureImpl(Identifier id,Expression type,Scope outermost){ return true; }

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

	void nameIndex(IndexExp index,string name){ // semantic checks that those do not alias
		import ast.semantic_:getIdFromIndex;
		auto id=getIdFromIndex(index);
		assert(id&&id.meaning);
		updateDeclProps(id.meaning).nameIndex(index,name);
	}

	struct ScopeState{
		bool opEquals(ref ScopeState rhs){
			static if(language==silq){
				if(dependencies!=rhs.dependencies)
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
	private:
		static if(language==silq){
			Dependencies dependencies;
			DeclProps declProps;
		}
		Declaration[string] symtab;
		bool restoreable=false;
	}
	ScopeState getStateSnapshot(bool restoreable=false)in{
		assert(!toPush.length);
	}do{
		Declaration[string] nsymtab;
		foreach(_,decl;symtab) nsymtab[decl.getName]=decl;
		static if(language==silq){
			return ScopeState(dependencies.dup,restoreable?saveDeclProps:DeclProps.init,nsymtab,restoreable);
		}else{
			return ScopeState(nsymtab,restoreable);
		}
	}
	void restoreStateSnapshot(ref ScopeState state)in{
		assert(!toPush.length);
		assert(state.restoreable);
	}do{
		dependencies=state.dependencies;
		resetDeclProps(state.declProps);
		symtab.clear();
		foreach(_,decl;state.symtab) symtab[decl.name.ptr]=decl;
		foreach(_,decl;symtab) if(decl.rename.ptr !in rnsymtab) rnsymtab[decl.rename.ptr]=decl; // TODO: ok?
		state=ScopeState.init;
	}
private:
	static if(language==silq){
		Dependencies dependencies;
		DeclProps declProps;
	}
	Declaration[const(char)*] symtab;
	Declaration[const(char)*] rnsymtab;
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
	override Declaration lookup(Identifier ident,bool rnsym,bool lookupImports,Lookup kind){
		if(auto d=super.lookup(ident,rnsym,lookupImports,kind)) return d;
		if(lookupImports){
			Declaration[] ds;
			foreach(sc;imports) if(auto d=sc.lookup(ident,rnsym,false,kind)) ds~=d;
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
	override Declaration lookup(Identifier ident,bool rnsym,bool lookupImports,Lookup kind){
		if(auto decl=lookupHere(ident,rnsym,kind)) return decl;
		return parent.lookup(ident,rnsym,lookupImports,kind);
	}

	override Annotation restriction(){ return parent.restriction(); }
	static if(language==silq){
		override DeclProp* getDeclProp(Declaration decl,bool failed=false){
			if(auto r=super.getDeclProp(decl,failed))
				return r;
			return parent.getDeclProp(decl);
		}
	}

	override bool isNestedIn(Scope rhs){ return rhs is this || parent.isNestedIn(rhs); }

	protected override bool insertCaptureImpl(Identifier id,Expression type,Scope outermost){
		if(this is outermost) return true;
		foreach(sc;parent.activeNestedScopes){
			if(this is sc) continue;
			if(!sc.addVariable(id.meaning,type,true))
				return false;
		}
		return parent.insertCaptureImpl(id,type,outermost);
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

class FunctionScope: NestedScope{
	FunctionDef fd;
	this(Scope parent,FunctionDef fd){
		super(parent);
		this.fd=fd;
	}
	final bool addCapture(Identifier id,Scope startScope){
		startScope.insertCapture(id,this);
		fd.addCapture(id);
		return true;
	}
	override Annotation restriction(){
		return fd.annotation;
	}
	void forceClose(){}
	// ~this(){ import std.stdio; writeln(fd.loc.rep); }
	override FunctionDef getFunction(){ return fd; }
}
class DataScope: NestedScope{
	DatDecl decl;
	override bool allowsLinear(){
		return false; // TODO!
	}
	this(Scope parent,DatDecl decl){
		super(parent);
		this.decl=decl;
	}
	final bool addCapture(Identifier id,Scope startScope){
		startScope.insertCapture(id,this);
		decl.addCapture(id);
		return true;
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
