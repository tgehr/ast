module ast.lowerings;

import std.algorithm, std.conv,std.exception;

import astopt;
import ast.lexer,ast.scope_,ast.error;
import ast.type,ast.expression,ast.semantic_;
import ast.declaration;

static if(language==silq):

Identifier getOperatorSymbol(string name,Location loc,Scope isc){
	import ast.modules: getOperatorScope;
	auto sc=getOperatorScope(isc.handler, loc);
	if(!sc) return null;
	auto res=new Identifier(name);
	res.loc=loc;
	res.scope_=isc;
	res.meaning=sc.lookup(res,false,false,Lookup.constant,null);
	if(!res.meaning){
		res.sstate=SemState.error;
	}else{
		res.type=res.typeFromMeaning;
		res.constLookup=false;
		res.sstate=SemState.completed;
	}
	return res;
}

string getSuffix(Expression type){
	if(cast(TupleTy)type) return "t";
	if(cast(VectorTy)type) return "v";
	if(cast(ArrayTy)type) return "a";
	if(auto intTy=isFixedIntTy(type)){
		return intTy.isSigned ? intTy.isClassical?"S":"s" : intTy.isClassical?"U":"u";
	}
	if(auto ℤmodTy=isℤmodTy(type)){
		return ℤmodTy.isStar ? ℤmodTy.isClassical?"X":"x" : ℤmodTy.isClassical?"M":"m";
	}
	final switch(isNumericTy(type))with(NumericType){
		case none: enforce(0, text("unsupported lowering type: ",type)); assert(0);
		case Bool: return type.isClassical()?"B":"b";
		case ℕt: return type.isClassical()?"N":"n";
		case ℤt: return type.isClassical()?"Z":"z";
		case ℚt: return type.isClassical()?"Q":"q";
		case ℝ: return type.isClassical()?"R":"r";
		case ℂ: return type.isClassical()?"C":"c";
	}
}

enum OperatorBehavior{
	default_,
	nsub,
	comparison,
	mul,
	div,
	mod,
	pow,
	cat,
	andb,
	generic,
	genericPrelude,
}

string getSuffix(R)(OperatorBehavior behavior,string name,R types){ // TODO: replace with some sort of language-level overloading support
	if(behavior==OB.generic||behavior==OB.genericPrelude) return "";
	if(types.length==1) return getSuffix(types[0].eval());
	if(types.length==2){
		auto t0=types[0].eval(),t1=types[1].eval();
		auto num0=isNumericTy(t0), num1=isNumericTy(t1);
		final switch(behavior)with(OperatorBehavior){
			case default_:
				if(num0 && num1 && !(num0 == NumericType.Bool && num1 == NumericType.Bool)){
					if(num0!=num1){
						if(num0==NumericType.ℂ) return "CR";
						if(num1==NumericType.ℂ) return "RC";
					}
					return getSuffix(num0>num1?t0:t1);
				}
				break;
			case comparison, mul, div:
				if(num0 && num1 && t0 != Bool(false) && t1 != Bool(false)){
					if(num0!=num1){
						if(num0==NumericType.ℂ) return "CR";
						if(num1==NumericType.ℂ) return "RC";
					}
					return getSuffix(num0>num1?t0:t1);
				}
				break;
			case nsub:
				if(isSubtype(t0,Bool(false))&&isSubtype(t1,ℕt(false)))
					break;
				goto case default_;
			case mod:
				if(isSubtype(t0,Bool(false))&&isSubtype(t1,ℕt(true)))
					break;
				if(isSubtype(t0,ℤt(true))&&isSubtype(t1,ℕt(false)))
					break;
				goto case div;
			case pow:
				break;
			case cat:
				if(t0.isTupleTy()&&t1.isTupleTy()) return "t";
				if(cast(VectorTy)t0&&cast(VectorTy)t1) return "v";
				if(cast(ArrayTy)t0||cast(ArrayTy)t1) return "a";
				if(cast(VectorTy)t0||cast(VectorTy)t1) return "v";
				return "t";
			case andb:
				break;
			case generic,genericPrelude:
				assert(0);
		}
		auto s0=getSuffix(t0);
		auto s1=getSuffix(t1);
		void unstar(){
			if(s0=="x") s0="m";
			if(s0=="X") s0="M";
			if(s1=="x") s1="m";
			if(s1=="X") s1="M";
		}
		final switch(behavior)with(OperatorBehavior){
			case default_,nsub,mul,andb:
				if(s0.among("s","S","u","U","m","M","x","X")&&s1=="N") s1="Z";
				if(s1.among("s","S","u","U","m","M","x","X")&&s0=="N") s0="Z";
				if(behavior!=mul||!!s0.among("x","X")!=!!s1.among("x","X")){
					unstar();
				}
				break;
			case comparison:
				unstar();
				break;
			case div,mod:
				break;
			case pow:
				if(s0=="B"&&!s1.among("b","B","N")) s0="N";
				break;
			case cat:
				break;
			case generic,genericPrelude:
				assert(0);
		}
		return s0==s1?s0:s0~s1;
	}
	enforce(0,text("unsupported lowering arity: ",types));
	assert(0);
}
Expression makeComparisonCall(string name,Expression original,Expression[] args,Location loc,ExpSemContext context)in{
	assert(args.length==2);
}do{
	Expression.CopyArgs cargs={ preserveMeanings: true };
	if(isEmpty(args[0].type)!=isEmpty(args[1].type)) // (compared at the type of the other operand, as in `cmpType`, e.g., `x==(1,)[2]`)
		args=annotateEmpty(args,(isEmpty(args[0].type)?args[1]:args[0]).type,context);
	auto e0=args[0],e1=args[1];
	auto ty0=unfoldTypeVariables(e0.type),ty1=unfoldTypeVariables(e1.type); // (see `shape`)
	if(!cast(TupleTy)ty0&&!cast(ArrayTy)ty0&&!cast(VectorTy)ty0){
		assert(!cast(TupleTy)ty1&&!cast(ArrayTy)ty1&&!cast(VectorTy)ty1);
		return makeFunctionCall(OB.comparison,name,original,args,loc,context);
	}
	Expression makeConst(bool b){
		auto r=LiteralExp.makeBoolean(b);
		r.loc=loc;
		return r;
	}
	Expression makeMismatch(Expression b0,Expression b1){
		if(cast(EqExp)original){
			if(!b0||!b1) return makeConst(true);
			return makeConst(false);
		}else if(cast(NeqExp)original){
			if(!b0||!b1) return makeConst(false);
			return makeConst(true);
		}else if(cast(LeExp)original){
			if(!b0||!b1) return makeConst(true);
			auto r=new LtExp(b0.copy(cargs),b1.copy(cargs));
			r.loc=loc;
			return r;
		}else if(cast(LtExp)original){
			if(!b0||!b1) return makeConst(false);
			auto r=new LtExp(b0.copy(cargs),b1.copy(cargs));
			r.loc=loc;
			return r;
		}else if(cast(GeExp)original){
			if(!b0||!b1) return makeConst(true);
			auto r=new GtExp(b0.copy(cargs),b1.copy(cargs));
			r.loc=loc;
			return r;
		}else if(cast(GtExp)original){
			if(!b0||!b1) return makeConst(false);
			auto r=new GtExp(b0.copy(cargs),b1.copy(cargs));
			r.loc=loc;
			return r;
		}else assert(0);
	}
	Declaration capturedVersion(Declaration cur){ // (the version of a variable that a type mentions at the comparison)
		if(cur.scope_.isNestedIn(context.sc)){
			while(cur.scope_ !is context.sc&&cur.splitFrom) // (e.g., the split of a parameter that is forgotten after its last use, in `vector(n,0:!𝔹)==vector(n,0:!𝔹)`)
				cur=cur.splitFrom;
			assert(cur.scope_ is context.sc);
		}else for(bool found=true;found;){ // TODO: get rid of this (the types that mention a variable are not updated when it is split, e.g., into the scope of a return that forgets it)
			found=false;
			foreach(d;cur.splitInto) if(context.sc.isNestedIn(d.scope_)){ cur=d; found=true; break; }
		}
		return cur;
	}
	// (the variables that the types of the operands mention are parameters of an enclosing closure: the closure is analyzed
	// after the analysis of the function, whose symbol tables then no longer have the versions at the comparison, e.g., of `n`
	// for `vector(n,0:!𝔹)==vector(n,0:!𝔹)` in a branch, so it must not look them up, e.g., in the lowering of its loop)
	Declaration[] mentioned;
	foreach(ty;[ty0,ty1]) foreach(id;ty.freeVars){
		auto decl=id.meaning;
		if(!decl||!decl.scope_||!decl.scope_.getFunction()||mentioned.canFind!(d=>d is decl)) continue;
		mentioned~=decl;
	}
	bool closed=mentioned.length&&mentioned.all!((decl){
		auto type=typeForDecl(decl);
		if(!type||!type.isClassical()||isTypeTy(type)) return false;
		foreach(id;type.freeVars) return false;
		return true;
	});
	Parameter[] outerParams;
	Expression[] outerArgs;
	import util: MapX;
	MapX!(Declaration,Id) outerNames;
	if(closed) foreach(decl;mentioned){
		auto pname=new Identifier(freshName());
		pname.loc=loc;
		auto ptype=typeForDecl(decl).copy(cargs);
		ptype.loc=loc;
		auto p=new Parameter(true,pname,ptype);
		p.loc=loc;
		outerParams~=p;
		outerNames[decl]=pname.id;
		auto version_=capturedVersion(decl);
		auto a=new Identifier(version_.getId);
		a.loc=loc;
		a.meaning=version_;
		outerArgs~=a;
	}
	Expression paramType(Expression type,Expression unfolded){
		if(!closed) return type.copy(cargs);
		Expression.CopyArgs pcargs={ preserveMeanings: true };
		pcargs.mapExp=(Expression e,ref Expression.CopyArgs args){
			auto id=cast(Identifier)e;
			if(!id||!id.meaning) return null;
			if(id.meaning in outerNames){
				auto r=new Identifier(outerNames[id.meaning]);
				r.loc=id.loc;
				return r;
			}
			return null;
		};
		return unfolded.copy(pcargs);
	}
	Parameter makeParam(Expression arg,Expression unfolded){
		auto name=new Identifier(freshName());
		name.loc=arg.loc;
		auto dtype=paramType(arg.type,unfolded);
		dtype.loc=arg.loc;
		auto r=new Parameter(true,name,dtype);
		r.loc=arg.loc;
		return r;
	}
	auto params=[makeParam(e0,ty0),makeParam(e1,ty1)];
	auto p0=params[0].name.copy(cargs),p1=params[1].name.copy(cargs);
	p0.type=e0.type,p1.type=e1.type;
	// (the classical components and the lengths are compared first, then only the quantum components that can still change the result)
	bool isEq=cast(EqExp)original||cast(NeqExp)original;
	bool less=cast(LtExp)original||cast(LeExp)original;
	Expression lit(size_t n){
		auto r=LiteralExp.makeInteger(n);
		r.loc=loc;
		return r;
	}
	Identifier fresh(Expression type=null){
		auto r=new Identifier(freshName());
		r.loc=loc;
		r.type=type;
		return r;
	}
	CompoundExp compound(Expression[] s){
		auto r=new CompoundExp(s);
		r.loc=loc;
		return r;
	}
	void ifThen(ref Expression[] s,Expression cond,Expression[] then){
		cond.loc=loc;
		auto r=new IteExp(cond,compound(then),null);
		r.loc=loc;
		s~=r;
	}
	void ret(ref Expression[] s,Expression e){
		auto r=new ReturnExp(e);
		r.loc=loc;
		s~=r;
	}
	Expression pair(Expression a,Expression b){
		auto r=new TupleExp([a,b]);
		r.loc=loc;
		return r;
	}
	Expression differ(Expression a,Expression b){
		auto r=new NeqExp(a.copy(cargs),b.copy(cargs));
		r.loc=loc;
		return r;
	}
	Expression length(Expression p){
		auto lenName=new Identifier(Id.s!"length");
		lenName.loc=loc;
		auto r=new FieldExp(p.copy(cargs),lenName);
		r.loc=loc;
		return r;
	}
	static Expression makeIndex(Expression p,Expression t,Expression i){
		auto r=new IndexExp(p,i);
		r.loc=p.loc;
		r.type=indexType(t,i);
		assert(!!r.type,text(p," ",t," ",i," ",r," ",r.type));
		return r;
	}
	static struct Shape{ // (of the comparison of values of two types: its kind and the types of the components)
		enum Kind{ leaf,tuple,loop,unrolled } // (`unrolled`: a tuple and a vector or array)
		Kind kind;
		Expression ty0,ty1; // (the structure of the values of type variables, e.g., `!V` after `V:=𝔹^2`)
		ITupleTy tt0,tt1;
		Expression next0,next1;
		Expression elem0(size_t i){ return tt0?tt0[i]:next0; }
		Expression elem1(size_t i){ return tt1?tt1[i]:next1; }
		bool classicalLeaf(){ return ty0.isClassical()&&ty1.isClassical(); }
	}
	static Shape shape(Expression t0,Expression t1){
		Shape r;
		r.ty0=unfoldTypeVariables(t0),r.ty1=unfoldTypeVariables(t1);
		r.tt0=r.ty0.isTupleTy(),r.tt1=r.ty1.isTupleTy();
		if(r.tt0&&r.tt1&&(cast(TupleTy)r.tt0||cast(TupleTy)r.tt1)){
			r.kind=Shape.Kind.tuple;
			return r;
		}
		if(auto vt=cast(VectorTy)r.ty0) r.next0=vt.next;
		else if(auto at=cast(ArrayTy)r.ty0) r.next0=at.next;
		if(auto vt=cast(VectorTy)r.ty1) r.next1=vt.next;
		else if(auto at=cast(ArrayTy)r.ty1) r.next1=at.next;
		if((r.next0||r.tt0)&&(r.next1||r.tt1)){
			r.kind=r.next0&&r.next1?Shape.Kind.loop:Shape.Kind.unrolled;
			if(r.kind==Shape.Kind.loop) r.tt0=r.tt1=null;
			return r;
		}
		r.kind=Shape.Kind.leaf;
		return r;
	}
	static struct Events{ bool quantum,classical,classicalFirst; } // (whether a comparison compares quantum components, and classical components or lengths, and whether one of the latter precedes one of the former)
	static Events then(Events a,Events b){ return Events(a.quantum||b.quantum,a.classical||b.classical,a.classicalFirst||b.classicalFirst||a.classical&&b.quantum); }
	enum lengths=Events(false,true,false);
	Events events(Expression t0,Expression t1){
		auto sh=shape(t0,t1);
		final switch(sh.kind){
			case Shape.Kind.leaf:{
				auto classical=sh.classicalLeaf();
				return Events(!classical,classical,false);
			}
			case Shape.Kind.tuple:{
				if(sh.tt0.length!=sh.tt1.length&&isEq) return lengths;
				Events r;
				foreach(i;0..min(sh.tt0.length,sh.tt1.length)) r=then(r,events(sh.tt0[i],sh.tt1[i]));
				if(sh.tt0.length!=sh.tt1.length) r=then(r,lengths);
				return r;
			}
			case Shape.Kind.loop,Shape.Kind.unrolled:{
				Events e;
				if(sh.kind==Shape.Kind.loop){
					e=events(sh.next0,sh.next1);
					e.classicalFirst|=e.classical&&e.quantum; // (in the next iteration)
				}else foreach(i;0..(sh.tt0?sh.tt0:sh.tt1).length) e=then(e,events(sh.elem0(i),sh.elem1(i)));
				auto r=then(isEq?lengths:Events.init,e);
				return isEq?r:then(r,lengths);
			}
		}
	}
	Events elementEvents(Shape sh){
		if(sh.kind==Shape.Kind.loop) return events(sh.next0,sh.next1);
		Events e;
		foreach(i;0..(sh.tt0?sh.tt0:sh.tt1).length) e=then(e,events(sh.elem0(i),sh.elem1(i)));
		return e;
	}
	enum dynamic=size_t.max;
	size_t quantumCount(Expression t0,Expression t1){ // (the number of quantum components, if it does not depend on lengths)
		auto sh=shape(t0,t1);
		final switch(sh.kind){
			case Shape.Kind.leaf: return !sh.classicalLeaf();
			case Shape.Kind.tuple:{
				size_t r=0;
				foreach(i;0..min(sh.tt0.length,sh.tt1.length)){
					auto c=quantumCount(sh.tt0[i],sh.tt1[i]);
					if(c==dynamic) return dynamic;
					r+=c;
				}
				return r;
			}
			case Shape.Kind.loop,Shape.Kind.unrolled:
				return elementEvents(sh).quantum?dynamic:0;
		}
	}
	size_t leadingQuantum(Expression t0,Expression t1,ref bool stop){ // (the number of quantum components before the first classical comparison or length, as far as it does not depend on lengths)
		auto sh=shape(t0,t1);
		final switch(sh.kind){
			case Shape.Kind.leaf:
				if(!sh.classicalLeaf()) return 1;
				stop=true;
				return 0;
			case Shape.Kind.tuple:{
				size_t r=0;
				foreach(i;0..min(sh.tt0.length,sh.tt1.length)){
					r+=leadingQuantum(sh.tt0[i],sh.tt1[i],stop);
					if(stop) return r;
				}
				if(sh.tt0.length!=sh.tt1.length) stop=true;
				return r;
			}
			case Shape.Kind.loop,Shape.Kind.unrolled:
				stop=true;
				return 0;
		}
	}
	size_t unguarded=0; // (pass `quantum` of an ordering: the quantum components before all classical differences)
	enum Pass{ all,classical,quantum }
	static struct Count{ Identifier var; size_t offset; bool live; } // (of the quantum components before the current position, `var+offset` (`var` is `0` until it is `live`), in the passes of an ordering)
	Expression countExp(Count cnt){
		if(!cnt.var||!cnt.live) return lit(cnt.offset);
		auto v=cnt.var.copy(cargs);
		if(!cnt.offset) return v;
		auto r=new AddExp(v,lit(cnt.offset));
		r.loc=loc;
		return r;
	}
	void add(ref Expression[] s,Identifier var,Expression n){
		auto r=new AddAssignExp(var.copy(cargs),n);
		r.loc=loc;
		s~=r;
	}
	void flush(ref Expression[] s,ref Count cnt){
		if(!cnt.offset||!cnt.var) return;
		add(s,cnt.var,lit(cnt.offset));
		cnt.offset=0;
		cnt.live=true;
	}
	Identifier bound; // (pass `quantum` of an ordering: the number of quantum components before the first classical difference)
	Expression mismatch(Expression b0,Expression b1,Pass pass,Count cnt){
		auto r=makeMismatch(b0,b1);
		return pass==Pass.classical&&!isEq?pair(countExp(cnt),r):r;
	}
	bool walk(ref Expression[] s,Expression x0,Expression x1,Pass pass,ref Count cnt){ // (whether `s` ends with a `return`)
		auto sh=shape(x0.type,x1.type);
		bool counted=!isEq&&pass!=Pass.all;
		final switch(sh.kind){
			case Shape.Kind.leaf:{
				auto quantum=!sh.classicalLeaf();
				if(pass==Pass.all||quantum==(pass==Pass.quantum)){
					Expression[] then;
					ret(then,mismatch(x0,x1,pass,cnt));
					if(counted&&pass==Pass.quantum&&(cnt.live||cnt.offset>=unguarded)){
						Expression[] check;
						ifThen(check,differ(x0,x1),then);
						auto cond=new LtExp(countExp(cnt),bound.copy(cargs));
						ifThen(s,cond,check);
					}else ifThen(s,differ(x0,x1),then);
				}
				if(quantum) cnt.offset++;
				return false;
			}
			case Shape.Kind.tuple:{
				auto l0=sh.tt0.length,l1=sh.tt1.length;
				if(l0!=l1&&isEq){
					if(pass!=Pass.classical) return false;
					ret(s,makeConst(!!cast(NeqExp)original));
					return true;
				}
				foreach(i;0..min(l0,l1)){
					auto np0=makeIndex(x0.copy(cargs),sh.ty0,lit(i)),np1=makeIndex(x1.copy(cargs),sh.ty1,lit(i));
					if(walk(s,np0,np1,pass,cnt)) return true;
				}
				if(l0==l1||pass==Pass.quantum) return false;
				auto r=makeConst(less?l0<l1:l0>l1);
				ret(s,pass==Pass.classical?pair(countExp(cnt),r):r);
				return true;
			}
			case Shape.Kind.loop,Shape.Kind.unrolled:{
				auto len0=length(x0),len1=length(x1);
				Expression len;
				if(isEq){
					if(pass==Pass.classical){
						Expression[] then;
						ret(then,makeConst(!!cast(NeqExp)original));
						ifThen(s,differ(len0,len1),then);
					}
					len=len0;
				}else if(sh.kind==Shape.Kind.loop){
					auto cond=new LeExp(len0.copy(cargs),len1.copy(cargs));
					cond.loc=loc;
					auto minExp=new IteExp(cond,compound([len0.copy(cargs)]),compound([len1.copy(cargs)]));
					minExp.loc=loc;
					len=minExp;
				}else len=sh.tt0?len1:len0;
				auto e=elementEvents(sh);
				bool visit;
				final switch(pass){
					case Pass.all: visit=e.quantum||e.classical; break;
					case Pass.classical: visit=e.classical||counted&&e.quantum; break;
					case Pass.quantum: visit=e.quantum; break;
				}
				if(visit&&counted&&e.quantum){
					assert(!!cnt.var);
					flush(s,cnt);
					if(pass==Pass.classical&&!e.classical&&sh.kind==Shape.Kind.loop){ // (only counted)
						auto m=quantumCount(sh.next0,sh.next1);
						if(m!=dynamic){
							Expression n=len;
							if(m!=1){
								n=new MulExp(lit(m),len);
								n.loc=loc;
							}
							add(s,cnt.var,n);
							cnt.live=true;
							visit=false;
						}
					}
				}
				Expression[] element(Expression i0,Expression i1){
					Expression[] r;
					auto inner=counted&&e.quantum?Count(cnt.var,0,true):cnt;
					if(!walk(r,makeIndex(x0.copy(cargs),sh.ty0,i0),makeIndex(x1.copy(cargs),sh.ty1,i1),pass,inner))
						flush(r,inner);
					return r;
				}
				if(visit&&counted&&e.quantum) cnt.live=true; // (the elements count)
				if(visit&&sh.kind==Shape.Kind.loop){
					auto i=fresh(ℤt(true));
					Expression index(){ auto r=new Identifier(i.id); r.loc=loc; r.type=ℤt(true); return r; }
					auto forBdy=compound(element(index(),index()));
					auto for_=new ForExp(i,null,ForAggregate(ForRange(false,lit(0),null,true,len)),forBdy);
					for_.loc=loc;
					s~=for_;
				}else if(visit){
					foreach(i;0..(sh.tt0?sh.tt0:sh.tt1).length){
						auto cond=new LtExp(lit(i),len.copy(cargs));
						ifThen(s,cond,element(lit(i),lit(i)));
					}
				}
				if(!isEq&&pass!=Pass.quantum){
					Expression[] then;
					ret(then,mismatch(len0,len1,pass,cnt));
					ifThen(s,differ(len0,len1),then);
				}
				return false;
			}
		}
	}
	auto ev=events(p0.type,p1.type);
	Expression[] body_;
	Count none;
	if(isEq){
		if(!ev.classical||!walk(body_,p0,p1,Pass.classical,none)){
			if(ev.quantum) walk(body_,p0,p1,Pass.quantum,none);
			ret(body_,makeMismatch(null,null));
		}
	}else if(!ev.quantum||!ev.classicalFirst){
		if(!walk(body_,p0,p1,Pass.all,none)) ret(body_,makeMismatch(null,null));
	}else{ // (the first classical difference, then the quantum components before it)
		bool dyn=quantumCount(p0.type,p1.type)==dynamic;
		Count counter(ref Expression[] s){
			Count r;
			if(!dyn) return r;
			r.var=fresh();
			auto def=new DefineExp(r.var.copy(cargs),lit(0));
			def.loc=loc;
			s~=def;
			return r;
		}
		Parameter[] cparams;
		Expression[] cargs_;
		foreach(i,p;params){
			auto pname=fresh();
			auto cp=new Parameter(true,pname,p.dtype.copy(cargs));
			cp.loc=p.loc;
			cparams~=cp;
			auto a=pname.copy(cargs);
			a.type=i?e1.type:e0.type;
			cargs_~=a;
		}
		Expression[] cbody;
		auto c1=counter(cbody);
		if(!walk(cbody,cargs_[0],cargs_[1],Pass.classical,c1)) ret(cbody,pair(countExp(c1),makeMismatch(null,null)));
		auto cfd=new FunctionDef(null,cparams,true,tupleTy([ℕt(true),Bool(true)]),compound(cbody));
		cfd.annotation=Annotation.qfree;
		cfd.loc=loc;
		auto first=new LambdaExp(cfd);
		first.loc=loc;
		auto call=new CallExp(first,pair(p0.copy(cargs),p1.copy(cargs)),false,false);
		call.loc=loc;
		bound=fresh();
		bool stop=false;
		unguarded=leadingQuantum(p0.type,p1.type,stop);
		auto result=fresh();
		auto def=new DefineExp(pair(bound.copy(cargs),result.copy(cargs)),call);
		def.loc=loc;
		body_~=def;
		auto c2=counter(body_);
		walk(body_,p0,p1,Pass.quantum,c2);
		ret(body_,result.copy(cargs));
	}
	auto fbdy=new CompoundExp(body_);
	fbdy.loc=loc;
	Expression rret=original.type&&isNumericTy(original.type)==NumericType.Bool?Bool(original.type.isClassical()):null; // (avoids analyzing the function again for the types of its `return`s)
	auto fd=new FunctionDef(null,params,true,rret,fbdy);
	fd.annotation=Annotation.qfree;
	fd.loc=loc;
	if(closed){
		auto inner=new LambdaExp(fd);
		inner.loc=loc;
		auto oret=new ReturnExp(inner);
		oret.loc=loc;
		auto obdy=new CompoundExp([cast(Expression)oret]);
		obdy.loc=loc;
		auto outer=new FunctionDef(null,outerParams,true,null,obdy);
		outer.annotation=Annotation.qfree;
		outer.loc=loc;
		auto olambda=new LambdaExp(outer);
		olambda.loc=loc;
		auto oarg=new TupleExp(outerArgs);
		oarg.loc=loc;
		auto oce=new CallExp(olambda,oarg,false,false);
		oce.loc=loc;
		auto arg=new TupleExp(args);
		arg.loc=loc;
		auto ce=new CallExp(oce,arg,false,false);
		ce.loc=loc;
		return expressionSemantic(ce,context);
	}
	void visId(Identifier id){
		auto cur=id.meaning;
		assert(!!cur);
		if(!cur.scope_.getFunction()) return; // no need to capture global declarations
		fd.addCapture(capturedVersion(cur),id);
	}
	foreach(arg;[e0,e1])
		foreach(id;arg.type.freeVars) // (of the analyzed type: e.g., a lambda within the copy is not analyzed yet)
			visId(id);
	Declaration[] inserted;
	foreach(capture;fd.capturedDecls){
		if(capture.scope_.canInsert(capture.name.id)){
			auto origCaptureScope=capture.scope_;
			capture.scope_=null;
			origCaptureScope.unconsume(capture);
			inserted~=capture;
		}
	}
	scope(success)
		foreach(capture;inserted)
			capture.scope_.consume(capture,null);
	auto ofd=fd.copy(cargs); // TODO: this is a hack
	auto lambda=new LambdaExp(ofd,fd);
	lambda.loc=loc;
	auto arg=new TupleExp(args);
	arg.loc=loc;
	auto ce=new CallExp(lambda,arg,false,false);
	ce.loc=loc;
	return expressionSemantic(ce,context);
}

Expression[] annotateEmpty(Expression[] args,Expression type,ExpSemContext context){ // (operands of type `⊥` are annotated, so that a lowering keeps all operands)
	auto r=args.dup;
	foreach(ref arg;r){
		if(!isEmpty(arg.type)) continue;
		auto tae=new TypeAnnotationExp(arg,type,isSubtype(arg.type,type)?TypeAnnotationType.annotation:TypeAnnotationType.coercion); // (an empty tuple has no value either, e.g., of type `⊥ × !ℕ` for `(!𝔹^2) × !𝔹`)
		tae.loc=arg.loc;
		arg=expressionSemantic(tae,context.nestConst);
	}
	return r;
}

Expression makeFunctionCall(OperatorBehavior behavior,string name,Expression original,Expression[] args,Location loc,ExpSemContext context){
	if(original&&original.type&&!isEmpty(original.type)&&args.any!(arg=>isEmpty(arg.type))){ // (the call aborts, but the other operands are evaluated as well, e.g., `x+(1,)[2]` for `x:!ℝ`)
		auto type=original.type;
		foreach(arg;args) if(!isEmpty(arg.type)){ type=arg.type; break; }
		args=annotateEmpty(args,type,context);
	}
	foreach(arg;args){
		if(isEmpty(arg.type)){
			arg.setConstLookup(context.constResult!=ConstResult.no); // (e.g., an operand that is read becomes an implicit `dup`)
			if(original&&original.type){
				arg=new TypeAnnotationExp(arg,original.type,TypeAnnotationType.annotation);
				arg=expressionSemantic(arg,context);
			}
			return arg;
		}
	}
	auto sc=context.sc;
	Expression arg;
	if(args.length!=1){
		arg=new TupleExp(args);
		arg.loc=loc;
	}else arg=args[0];
	Expression fun=null;
	string fullName="";
	if(!fun){
		auto suffix=getSuffix(behavior,name,args.map!(x=>x.type));
		fullName=name~(suffix!=""?"_"~suffix:"");
		if(behavior==OB.genericPrelude){
			fun=getPreludeSymbol(fullName,loc,sc);
		}else{
			fun=getOperatorSymbol(fullName,loc,sc);
		}
		enforce(!!fun,text("function prototype for lowering not found: ",fullName));
	}
	bool isSquare=false,isClassical=false;
	if(behavior==OB.cat){ // TODO: implicitly fill multiple square argument lists
		if(fullName=="__cat_t"){
			assert(args.length==2&&args[0].type&&args[1].type);
			auto tt0=args[0].type.eval().isTupleTy(),tt1=args[1].type.eval().isTupleTy();
			assert(tt0&&tt1);
			auto n0=LiteralExp.makeInteger(tt0.length),n1=LiteralExp.makeInteger(tt1.length);
			n0.loc=loc, n1.loc=loc;
			auto sqarg=new TupleExp([n0,n1]);
			sqarg.loc=loc;
			fun=new CallExp(fun,sqarg,true,isClassical);
			fun.loc=loc;
		}
		if(args[0].constLookup) args[0]=dupExp(args[0],args[0].loc,context);
		if(args[1].constLookup) args[1]=dupExp(args[1],args[1].loc,context);
	}
	auto ce=new CallExp(fun,arg,isSquare,isClassical);
	ce.loc=loc;
	return expressionSemantic(ce,context);
}

private alias OB=OperatorBehavior;
Expression getLowering(UPlusExp upe,ExpSemContext context){ return makeFunctionCall(OB.genericPrelude,"dup",upe,[upe.e],upe.loc,context); }
Expression getLowering(UMinusExp ume,ExpSemContext context){ return makeFunctionCall(OB.default_,"__uminus",ume,[ume.e],ume.loc,context); }
Expression getLowering(UNotExp une,ExpSemContext context){ return makeFunctionCall(OB.default_,"__not",une,[une.e],une.loc,context); }
Expression getLowering(UBitNotExp ubne,ExpSemContext context){ return makeFunctionCall(OB.default_,"__bitnot",ubne,[ubne.e],ubne.loc,context); }

Expression getLowering(AddExp ae,ExpSemContext context){ return makeFunctionCall(OB.default_,"__add",ae,[ae.e1,ae.e2],ae.loc,context); }
Expression getLowering(SubExp se,ExpSemContext context){ return makeFunctionCall(OB.default_,"__sub",se,[se.e1,se.e2],se.loc,context); }
Expression getLowering(NSubExp nse,ExpSemContext context){ return makeFunctionCall(OB.nsub,"__nsub",nse,[nse.e1,nse.e2],nse.loc,context); }

Expression getLowering(MulExp me,ExpSemContext context){ return makeFunctionCall(OB.mul,"__mul",me,[me.e1,me.e2],me.loc,context); }
Expression getLowering(DivExp de,ExpSemContext context){ return makeFunctionCall(OB.div,"__div",de,[de.e1,de.e2],de.loc,context); }
Expression getLowering(IDivExp de,ExpSemContext context){ return makeFunctionCall(OB.div,"__idiv",de,[de.e1,de.e2],de.loc,context); }
Expression getLowering(ModExp de,ExpSemContext context){ return makeFunctionCall(OB.mod,"__mod",de,[de.e1,de.e2],de.loc,context); }
Expression getLowering(PowExp pe,ExpSemContext context){ return makeFunctionCall(OB.pow,"__pow",pe,[pe.e1,pe.e2],pe.loc,context); }

Expression getLowering(CatExp ce,ExpSemContext context){ return makeFunctionCall(OB.cat,"__cat",ce,[ce.e1,ce.e2],ce.loc,context); }

Expression getLowering(LtExp lt,ExpSemContext context){ return makeComparisonCall("__lt",lt,[lt.e1,lt.e2],lt.loc,context); }
Expression getLowering(LeExp le,ExpSemContext context){ return makeComparisonCall("__le",le,[le.e1,le.e2],le.loc,context); }
Expression getLowering(GtExp gt,ExpSemContext context){ return makeComparisonCall("__gt",gt,[gt.e1,gt.e2],gt.loc,context); }
Expression getLowering(GeExp ge,ExpSemContext context){ return makeComparisonCall("__ge",ge,[ge.e1,ge.e2],ge.loc,context); }
Expression getLowering(EqExp eq,ExpSemContext context){ return makeComparisonCall("__eq",eq,[eq.e1,eq.e2],eq.loc,context); }
Expression getLowering(NeqExp neq,ExpSemContext context){ return makeComparisonCall("__neq",neq,[neq.e1,neq.e2],neq.loc,context); }

Expression getLowering(BitOrExp oe,ExpSemContext context){ return makeFunctionCall(OB.mul,"__orb",oe,[oe.e1,oe.e2],oe.loc,context); }
Expression getLowering(BitXorExp xe,ExpSemContext context){ return makeFunctionCall(OB.mul,"__xorb",xe,[xe.e1,xe.e2],xe.loc,context); }
Expression getLowering(BitAndExp ae,ExpSemContext context){ return makeFunctionCall(OB.andb,"__andb",ae,[ae.e1,ae.e2],ae.loc,context); }

private CompoundExp toCompound(Expression e){
	auto ce=new CompoundExp([e]);
	ce.loc=e.loc;
	ce.sstate=e.sstate;
	return ce;
}

Expression getLowering(VectorForExp vfe,ExpSemContext context){
	import ast.semantic_:freshName,typeForDecl;
	if(!vfe.fd||!vfe.type) return null;
	auto ft=cast(FunTy)typeForDecl(vfe.fd);
	if(!ft) return null;
	auto loc=vfe.loc;
	Parameter[] params;
	Expression[] args;
	Identifier addParam(bool isConst,Expression type,Expression arg,Location ploc){
		auto id=new Identifier(freshName());
		id.loc=ploc;
		auto p=new Parameter(isConst,id,type);
		p.loc=ploc;
		params~=p;
		args~=arg;
		auto use=new Identifier(id.name);
		use.loc=ploc;
		return use;
	}
	auto fle=new LambdaExp(vfe.fd,vfe.fd);
	fle.loc=loc;
	fle.type=ft;
	fle.setSemCompleted();
	auto fid=addParam(true,ft,fle,loc);
	ForAggregate naggr;
	if(auto range=vfe.fe.aggr.isRange){
		auto lid=addParam(true,range.left.type,range.left,range.left.loc);
		Identifier sid=null;
		if(range.step) sid=addParam(true,range.step.type,range.step,range.step.loc);
		auto rid=addParam(true,range.right.type,range.right,range.right.loc);
		naggr=ForAggregate(ForRange(range.leftExclusive,lid,sid,range.rightExclusive,rid));
	}else{
		auto cnt=vfe.fe.aggr.isContainer();
		assert(!!cnt);
		auto ety=vfe.fe.aggr.elementType();
		assert(!!ety);
		naggr=ForAggregate(ForContainer(addParam(false,arrayTy(ety),cnt.e,cnt.e.loc))); // (the loop checks at run time that no elements remain, e.g., if its body diverges for elements of an empty type)
	}
	auto rname=new Identifier(freshName());
	rname.loc=loc;
	auto empty=new VectorExp([]);
	empty.loc=loc;
	auto rde=new DefineExp(rname,empty);
	rde.loc=loc;
	auto xid=new Identifier(freshName());
	xid.loc=loc;
	auto fcall=new CallExp(fid.copy(),xid.copy(),false,false);
	fcall.loc=loc;
	auto vce=new VectorExp([cast(Expression)fcall]);
	vce.loc=loc;
	auto cae=new CatAssignExp(rname.copy(),vce);
	cae.loc=loc;
	auto lbdy=new CompoundExp([cast(Expression)cae]);
	lbdy.loc=loc;
	auto nfe=new ForExp(xid,null,naggr,lbdy);
	nfe.loc=loc;
	auto re=new ReturnExp(rname.copy());
	re.loc=loc;
	auto fbdy=new CompoundExp([rde,nfe,re]);
	fbdy.loc=loc;
	auto fd=new FunctionDef(null,params,true,null,fbdy);
	fd.annotation=pure_;
	fd.inferAnnotation=true;
	fd.loc=loc;
	auto le=new LambdaExp(fd);
	le.loc=loc;
	auto atpl=new TupleExp(args);
	atpl.loc=loc;
	auto lce=new CallExp(le,atpl,false,false);
	lce.loc=loc;
	auto tae=new TypeAnnotationExp(lce,vfe.type,TypeAnnotationType.coercion);
	tae.loc=loc;
	auto r=expressionSemantic(tae,context);
	return r;
}
private Expression logicLowering(ALogicExp e,bool isOr,ExpSemContext context){ // `a&&b` is `if a then b else false`, `a||b` is `if a then true else b`
	auto value=LiteralExp.makeBoolean(isOr);
	value.loc=e.loc;
	value.sstate=SemState.initial;
	auto ne2=e.e2;
	if(!cast(AssertExp)ne2) ne2=dupExp(ne2,ne2.loc,context);
	else ne2=ne2.copy();
	auto shortCircuit=toCompound(value),evaluated=toCompound(ne2);
	auto ite=isOr?new IteExp(e.e1,shortCircuit,evaluated):new IteExp(e.e1,evaluated,shortCircuit);
	ite.loc=e.loc;
	auto quantumControl=e.e1.type&&!e.e1.type.isClassical();
	if(e.blscope_&&e.forgetScope){ // (the branches are the scopes the right operand was analyzed in, e.g., it may consume variables)
		shortCircuit.blscope_=e.forgetScope;
		evaluated.blscope_=e.blscope_;
	} // (otherwise, e.g., within a type, the branches have no scopes of their own, like those of an `if` expression used outside of its scope)
	foreach(branch;[ite.then,ite.othw]){
		branch.s[0]=branchSemantic(branch.s[0],context.nestScope(branch.blscope_?branch.blscope_:context.sc,context.constResult),quantumControl);
		branch.type=branch.s[0].type;
		propErr(branch.s[0],branch);
		propErr(branch,ite);
		if(!branch.isSemError()) branch.setSemCompleted();
	}
	if(!ite.isSemError()){
		ite.type=e.e1.type&&isEmpty(e.e1.type)?bottom:joinTypes(ite.then.type,ite.othw.type);
		if(!ite.type) ite.setSemError();
	}
	ite.constLookup=context.constResult!=ConstResult.no;
	if(!ite.isSemError()) ite.setSemCompleted();
	return ite;
}
Expression getLowering(AndThenExp ae,ExpSemContext context){
	return logicLowering(ae,false,context);
}
Expression getLowering(OrElseExp oe,ExpSemContext context){
	return logicLowering(oe,true,context);
}

Expression getLowering(OrExp oe,ExpSemContext context){ return makeFunctionCall(OB.mul,"__or",oe,[oe.e1,oe.e2],oe.loc,context); }
Expression getLowering(XorExp xe,ExpSemContext context){ return makeFunctionCall(OB.mul,"__xor",xe,[xe.e1,xe.e2],xe.loc,context); }
Expression getLowering(AndExp ae,ExpSemContext context){ return makeFunctionCall(OB.andb,"__and",ae,[ae.e1,ae.e2],ae.loc,context); }


Expression getLowering(TokenType op)(BinaryExp!op e,Scope sc)if(is(BinaryExp!op:AAssignExp)){
	static if(op==Tok!"←"){
		return null; // no lowering
	}else{
		Expression toAssign(){
			auto id1=cast(Identifier)e.e1;
			if(!id1) return null; // TODO: lower via `with x:=a do x op= b`
			if(!e.operation) return null;
			auto ae=new AssignExp(id1,e.operation);
			ae.replacements=e.replacements;
			ae.loc=e.loc;
			ae.type=unit;
			ae.sstate=SemState.completed;
			return ae;
		}
		static if([Tok!"+←",Tok!"-←",Tok!"sub←",Tok!"⊕←",Tok!"⊻←",Tok!"~←",Tok!"·←",Tok!"/←"].canFind(op)){
			Expression toReversible(){
				auto id1=cast(Identifier)e.e1;
				if(!id1) return null; // TODO: lower via `with x:=a do x op= b`
				static if(op==Tok!"+←") enum name="__add_assign", ob=OB.default_;
				else static if(op==Tok!"-←") enum name="__sub_assign", ob=OB.default_;
				else static if(op==Tok!"sub←") enum name="__nsub_assign", ob=OB.nsub;
				else static if(op==Tok!"⊕←") enum name="__xorb_assign", ob=OB.mul;
				else static if(op==Tok!"⊻←") enum name="__xor_assign", ob=OB.mul;
				else static if(op==Tok!"~←") enum name="__cat", ob=OB.cat;
				else static if(op==Tok!"·←") enum name="__mul_assign", ob=OB.mul;
				else static if(op==Tok!"/←") enum name="__div_assign", ob=OB.mul;
				else static assert(0);
				auto fc=makeFunctionCall(ob,name,e,[id1,e.e2],e.loc,expSemContext(sc,ConstResult.no,InType.no));
				auto id2=new Identifier(id1.name);
				auto de=new DefineExp(id2,fc);
				assert(e.replacements.length==1 && e.replacements[0].previous==id1.meaning);
				id2.meaning=e.replacements[0].new_;
				id2.type=id2.typeFromMeaning;
				id2.constLookup=false;
				id2.sstate=SemState.completed;
				de.type=unit;
				de.sstate=SemState.completed;
				return de;
			}
			if(e.e1.type.isClassical()&&op!=Tok!"~←") return toAssign();
			static if(op==Tok!"·←"){
				assert(e.e2&&e.e2.type);
				auto zmod=isℤmodTy(e.e2.type);
				if(!zmod||!zmod.isStar) return toAssign();
			}
			return toReversible();
		}else return toAssign();
	}
}

// note: this does not generate a valid Silq AST, assumes specific backend semantics
Expression getSwapLowering(DefineExp de, Scope sc){
	if(!de.isSwap) return null;
	auto tpll=cast(TupleExp)de.e1;
	if(!tpll||tpll.e.length!=2) return null;
	auto tplr=cast(TupleExp)de.e2;
	if(!tplr||tplr.e.length!=2) return null;

	auto tmp0=new Identifier(freshName());
	tmp0.scope_=sc;
	auto tmp1=new Identifier(freshName());
	tmp1.scope_=sc;
	auto vd0=new VarDecl(tmp0.copy());
	vd0.scope_=sc;
	tmp0.meaning=vd0;
	auto vd1=new VarDecl(tmp1.copy());
	vd1.scope_=sc;
	tmp1.meaning=vd1;
	auto de0=new DefineExp(tmp0,tplr.e[0]);
	tmp0.type=tplr.e[0].type;
	vd0.vtype=tmp0.type;
	vd0.setSemCompleted();
	auto de1=new DefineExp(tmp1,tplr.e[1]);
	tmp1.type=tplr.e[1].type;
	vd1.vtype=tmp1.type;
	vd1.setSemCompleted();

	auto tmp0s=tmp0.copy();
	tmp0s.scope_=sc;
	auto vd0s=new VarDecl(tmp0s.copy());
	vd0s.scope_=sc;
	vd0s.vtype=tmp1.type;
	vd0s.setSemCompleted();
	tmp0s.meaning=vd0s;
	tmp0s.type=tmp1.type;

	auto tmp1s=tmp1.copy();
	tmp1s.scope_=sc;
	auto vd1s=new VarDecl(tmp1s.copy());
	vd1s.scope_=sc;
	vd1s.vtype=tmp0.type;
	vd1s.setSemCompleted();
	tmp1s.meaning=vd1s;
	tmp1s.type=tmp0.type;

	auto sl=new TupleExp([tmp1s,tmp0s]);
	sl.type=tupleTy([tmp1s.type,tmp0s.type]);
	auto sr=new TupleExp([tmp0,tmp1]);
	sr.type=tupleTy([tmp0.type,tmp1.type]);
	tmp0.constLookup=false;
	tmp1.constLookup=false;
	sr.constLookup=false;
	auto sde=new DefineExp(sl,sr);

	auto tmp2=tmp1s.copy();
	tmp2.scope_=sc;
	tmp2.meaning=tmp1s.meaning;
	tmp2.type=tmp1s.type;
	auto de2=new DefineExp(tpll.e[0],tmp2);
	auto tmp3=tmp0s.copy();
	tmp3.scope_=sc;
	tmp3.meaning=tmp0s.meaning;
	tmp3.type=tmp0s.type;
	auto de3=new DefineExp(tpll.e[1],tmp3);
	auto fwd=new CompoundExp([de0,de1]);
	auto bdy=new CompoundExp([sde]);
	auto bwd=new CompoundExp([de3,de2]); // (reordering handles case where aliased)
	auto we=new WithExp(fwd,bdy);
	we.itrans=bwd;
	//return statementSemantic(we,sc); // TODO?
	return we;
}
