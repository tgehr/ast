// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.reverse;
import astopt;

import std.conv,std.format,std.algorithm,std.range,std.exception;
import ast.lexer,ast.scope_,ast.expression,ast.type,ast.declaration,ast.semantic_,ast.error,util;
import ast.callfailure: explainArgumentCount;
import ast.conversion: typeExplicitConversion;
import util.tuple:Q=Tuple,q=tuple;
import util: SetX;

bool isEmptyTupleTy(Expression ty){
	return isSubtype(ty,unit)&&isSubtype(unit,ty); // TODO: improve?
}

Expression constantExp(size_t l){
	Token tok;
	tok.type=Tok!"0";
	tok.str=to!string(l);
	auto r=new LiteralExp(tok);
	r.type=l<=1?Bool(true):ℕt(true);
	r.setSemCompleted();
	return r;
}

static if(language==silq)
Identifier getDup(Location loc,Scope isc){
	return getPreludeSymbol("dup",loc,isc);
}

bool isClassicalExp(Expression e){
	static if(language==silq) return e.type&&e.subexpressions.all!(x=>!x.type||x.type.isClassical())&&e.isQfree()&&!e.consumes;
	else return true;
}

bool isForgettableCallLhs(CallExp ce){
	if(auto ft=cast(FunTy)ce.e.type){
		bool base=ft.isSquare==ce.isSquare&&ft.annotation>=Annotation.qfree&&(ft.nargs||isEmptyTuple(ce.arg));
		static if(language==silq) return base&&(ft.isConstForReverse.all||isClassicalExp(ce));
		else return base&&ft.isConstForReverse.all;
	}
	return false;
}

enum LowerDefineFlags{
	none=0,
	createFresh=1,
	reverseMode=2,
}

Expression knownLength(Expression e,bool ignoreType){ // TODO: version that returns bool
	Expression res;
	scope(exit) if(res) res.loc=e.loc;
	if(auto let=cast(LetExp)e) if(auto fwd=let.isForward(false)) return knownLength(fwd,ignoreType);
	if(auto vec=cast(VectorExp)e) return res=constantExp(vec.e.length);
	if(auto tpl=cast(TupleExp)e) return res=constantExp(tpl.e.length);
	if(auto cat=cast(CatExp)e){
		auto a=cat.e1.knownLength(ignoreType);
		auto b=cat.e2.knownLength(ignoreType);
		if(a&&b){
			res=new AddExp(a,b);
			propErr(a,res);
			propErr(b,res);
			if(a.type&&b.type){
				res.type=arithmeticType!false(a.type,b.type);
				if(!res.type) res.setSemError();
			}
			if(res.type&&a.isSemCompleted()&&b.isSemCompleted())
				res.setSemCompleted();
			return res;
		}
	}
	if(auto tae=cast(TypeAnnotationExp)e){
		Expression knownLengthType(Expression t){
			if(auto une=cast(UNotExp)t)
				return knownLengthType(une.e);
			if(auto vec=cast(VectorTy)t)
				return vec.num;
			if(auto tt=t.isTupleTy())
				return res=constantExp(tt.length);
			if(auto pow=cast(PowExp)t)
				return pow.e2;
			if(auto ty=cast(TypeofExp)t){
				if(auto sl=cast(SliceExp)ty.e){
					res=new NSubExp(sl.r,sl.l);
					propErr(sl.r,res);
					propErr(sl.l,res);
					if(sl.r.type&&sl.l.type){
						res.type=nSubType(sl.r,sl.l);
						if(!res.type) res.setSemError();
					}
					if(res.type&&sl.r.isSemCompleted()&&sl.l.isSemCompleted())
						res.setSemCompleted();
					return res;
				}
			}
			return null;
		}
		if(auto l=knownLengthType(tae.t))
			return l;
		return knownLength(tae.e,ignoreType);
	}
	if(!ignoreType&&e.type){
		if(auto vec=cast(VectorTy)e.type)
			return vec.num;
		if(auto tt=e.type.isTupleTy())
			return res=constantExp(tt.length);
	}
	return null;
}

bool isEmptyTuple(Expression e){
	auto tpl=cast(TupleExp)e;
	return tpl&&tpl.length==0;
}

bool validDefLhs(LowerDefineFlags flags)(Expression olhs,Scope sc,bool unchecked,bool noImplicitDup){
	bool validDefEntry(Expression e){
		if(e.implicitDup){
			if(noImplicitDup){
				if(auto id=cast(Identifier)olhs)
					if(id.meaning&&id.meaning.isConst) // (a copy is analyzed again)
						return false;
			}else return false;
		}
		return cast(Identifier)e||cast(IndexExp)e||cast(SliceExp)e;
	}
	if(auto tpl=cast(TupleExp)olhs){
		if(noImplicitDup){
			static bool writesBack(Expression e){
				auto id=cast(Identifier)unwrap(e);
				return id&&id.meaning;
			}
			if(tpl.e.any!writesBack) return false;
		}
		return tpl.e.all!validDefEntry;
	}
	if(auto cat=cast(CatExp)olhs) return validDefEntry(unwrap(cat.e1))&&validDefEntry(unwrap(cat.e2))
		                              &&(knownLength(cat.e1,true)||knownLength(cat.e2,true));
	if(auto ce=cast(CallExp)olhs){
		static if(language==silq){
			if(isPrimitiveCall(ce))
				return false;
			if(isBuiltInCall(cast(CallExp)unwrap(ce.e)))
				return false;
		}
		auto f=ce.e, ft=cast(ProductTy)f.type;
		if(!ft) return false;
		if(ce.isSquare!=ft.isSquare) return false;
		static if(language==silq){
			if(ce.checkReverse&&!unchecked){
				auto r=reverseCallRewriter(ft,ce.loc);
				if(r.movedType.hasClassicalComponent()){
					return false;
				}
			}
		}
		// if(!equal(ft.isConst,ft.isConstForReverse)) return false; // TODO: can we completely rewrite away isConstForReverse?
		if((ft.nargs||isEmptyTuple(ce.arg))&&iota(ft.nargs).all!(i=>ft.isConstForReverse[i])){
			auto tpl=cast(TupleExp)ce.arg;
			auto tt=ft.dom.isTupleTy;
			return !tpl||tt&&tpl.length==tt.length;
		}
		if(iota(ft.nargs).all!(i=>!ft.isConstForReverse[i]))
			return validDefEntry(ce.arg);
		assert(ft.isTuple);
		auto tpl=cast(TupleExp)ce.arg;
		if(!tpl||ft.nargs!=tpl.length) return false;
		return iota(ft.nargs).all!(i=>ft.isConstForReverse[i]||validDefEntry(tpl.e[i]));
	}
	if(auto tae=cast(TypeAnnotationExp)olhs){
		if(tae.annotationType==TypeAnnotationType.coercion&&cast(CallExp)tae.e
		   &&validDefLhs!flags(tae.e,sc,unchecked,noImplicitDup))
			return true;
	}
	return validDefEntry(olhs);
}

static if(language==silq)
ReverseCallRewriter reverseCallRewriter(FunTy ft_,Location loc){
	auto r=ReverseCallRewriter(ft_,loc);
	with(r){
		constTuple=constIndices.walkLength!=1||movedIndices.empty&&ft.isTuple;
		movedTuple=movedIndices.walkLength!=1||constIndices.empty&&ft.isTuple;
		constType=constTuple?tupleTy(constIndices.map!(i=>ft.argTy(i)).array):ft.argTy(constIndices.front);
		movedType=movedTuple?tupleTy(movedIndices.map!(i=>ft.argTy(i)).array):ft.argTy(movedIndices.front);
		returnType=ft.cod;
		returnTuple=isEmptyTupleTy(returnType);
		return r;
	}
}

struct ReverseCallRewriter{
static if(language==silq):
	ProductTy ft;
	Location loc;
	bool constTuple,movedTuple,returnTuple;
	Expression constType,movedType,returnType;
	@property constIndices()return scope{ return iota(ft.nargs).filter!(i=>ft.isConstForReverse[i]); }
	@property movedIndices()return scope{ return iota(ft.nargs).filter!(i=>!ft.isConstForReverse[i]); }
	@property bool constLast(){
		static bool constLastImpl(FunTy ft){
			return ft.nargs&&!ft.isConstForReverse[0]&&ft.isConstForReverse[$-1];
		}
		if(ft.isSquare){
			if(auto ft2=cast(FunTy)ft.cod){
				return constLastImpl(ft2);
			}else return false;
		}
		return constLastImpl(ft);
	}
	@property bool innerNeeded(){
		return !(equal(ft.isConst,ft.isConstForReverse)&&equal(constIndices,only(0))&&equal(movedIndices,only(1))&&ft.annotation==Annotation.mfree);
	}
	Q!(Expression,Expression) reorderArguments(TupleExp tpl)in{
		assert(ft.isTuple&&ft.nargs==tpl.length);
	}do{
		auto loc=tpl.loc;
		auto constArgs=constIndices.map!(i=>tpl.e[i]);
		auto movedArgs=movedIndices.map!(i=>tpl.e[i]);
		Expression constArg,movedArg;
		if(constTuple){
			constArg=new TupleExp(constArgs.array);
			constArg.loc=loc;
		}else constArg=constArgs.front;
		if(movedTuple){
			movedArg=new TupleExp(movedArgs.array);
			movedArg.loc=loc;
		}else movedArg=movedArgs.front;
		return q(constArg,movedArg);
	}
	Expression wrapInner(Expression f){
		auto loc=this.loc;
		auto names=only(freshName,freshName);
		auto params=makeParams(only(true,false),names,only(constType,movedType),loc);
		Expression unpackExp=null;
		Expression[] movedArgs;
		Expression[] constArgs;
		if(constTuple){
			constArgs=makeIndexLookups(names[0],iota(constIndices.walkLength),loc);
		}else{
			auto id=new Identifier(names[0]);
			id.loc=loc;
			constArgs=[id];
		}
		if(movedTuple){
			auto unpackNames=movedIndices.map!((i)=>Id.intern("`arg_"~(ft.names[i]?ft.names[i].str:text(i))));
			auto unpackLhs=new TupleExp(makeIdentifiers(unpackNames,loc));
			unpackLhs.loc=loc;
			auto unpackRhs=new Identifier(names[1]);
			unpackRhs.loc=loc;
			if(!movedIndices.empty){ // TODO: get rid of this branch
				unpackExp=new BinaryExp!(Tok!":=")(unpackLhs,unpackRhs);
				unpackExp.loc=loc;
				movedArgs=makeIdentifiers(unpackNames,loc);
			}else{
				// TODO: remove this once classical move semantics is implemented
				unpackExp=new ForgetExp(unpackRhs,unpackLhs);
				unpackExp.loc=loc;
				movedArgs=[];
			}
		}else movedArgs=makeIdentifiers(only(names[1]),loc);
		auto nargs=new Expression[](ft.nargs);
		foreach(i,carg;zip(constIndices,constArgs)){
			assert(!nargs[i]);
			nargs[i]=carg;
		}
		foreach(i,marg;zip(movedIndices,movedArgs)){
			assert(!nargs[i]);
			nargs[i]=marg;
		}
		assert(nargs.all!(x=>!!x));
		Expression narg;
		bool isTuple=(constArgs.length!=0||movedTuple)&&(movedArgs.length!=0||constTuple);
		if(isTuple){
			narg=new TupleExp(nargs);
			narg.loc=loc;
		}else{
			assert(nargs.length==1);
			narg=nargs[0];
		}
		auto ce1=new CallExp(f.copy,narg,ft.isSquare,false);
		ce1.loc=loc;
		Expression ret=new ReturnExp(ce1);
		ret.loc=loc;
		auto body_=new CompoundExp((unpackExp?[unpackExp]:[])~[ret]);
		body_.loc=loc;
		auto le=makeLambda(params,true,false,ft.annotation,body_,loc);
		return le;
	}
	@property bool outerNeeded(bool simplify=true){
		return simplify&&(constTuple||returnTuple)||ft.isSquare||constLast;
	}
	Expression wrapOuter(Expression rev,bool simplify){
		if(!outerNeeded(simplify)) return rev;
		auto loc=this.loc;
		if(simplify&&(constTuple||returnTuple)){
			auto isConst=(bool[]).init;
			auto names=(Id[]).init;
			auto types=(Expression[]).init;
			void add(bool isConst_)(){
				static if(isConst_){
					alias isTuple=constTuple;
					alias type=constType;
					alias indices=constIndices;
				}else{
					alias isTuple=returnTuple;
					alias type=returnType;
				}
				if(isTuple){
					if(auto tpl=type.isTupleTy()){
						static if(isConst_){
							foreach(i,j;enumerate(indices)){
								isConst~=isConst_;
								names~=Id.intern("`arg_"~(ft.names[j]?ft.names[j].str:text(j)));
								types~=tpl[i];
							}
						}else{
							foreach(i;0..tpl.length){
								isConst~=isConst_;
								names~=freshName();
								types~=tpl[i];
							}
						}
						return;
					}
				}
				isConst~=isConst_;
				static if(isConst_){
					auto j=constIndices.front;
					names~=Id.intern("`arg_"~(ft.names[j]?ft.names[j].str:text(j)));
				}else names~=freshName();
				types~=type;
			}
			if(constLast){
				add!false();
				add!true();
			}else{
				add!true();
				add!false();
			}
			auto nparams=makeParams(isConst,names,types,loc);
			auto constArgs=makeIdentifiers(iota(isConst.length).filter!(i=>isConst[i]).map!(i=>names[i]),loc);
			auto constArg=constTuple?new TupleExp(constArgs):constArgs.front;
			constArg.loc=loc;
			auto movedArgs=makeIdentifiers(iota(isConst.length).filter!(i=>!isConst[i]).map!(i=>names[i]),loc);
			auto movedArg=returnTuple?new TupleExp(movedArgs):movedArgs.front;
			auto nnarg=new TupleExp([constArg,movedArg]);
			nnarg.loc=loc;
			auto ce2=new CallExp(rev,nnarg,false,false);
			ce2.loc=loc;
			auto body2=makeLambdaBody(ce2,loc);
			bool isTuple=(constArgs.length!=0||returnTuple)&&(movedArgs.length!=0||constTuple);
			auto le2=makeLambda(nparams,isTuple,ft.isSquare,ft.annotation,body2,loc);
			return le2;
		}else{
			auto names=only(freshName,freshName);
			auto nparams=constLast ? makeParams(only(true,false).retro,names.retro,only(constType,returnType).retro,loc)
				: makeParams(only(true,false),names,only(constType,returnType),loc);
			auto nnargs=makeIdentifiers(names,loc);
			auto nnarg=new TupleExp(nnargs);
			nnarg.loc=loc;
			auto ce2=new CallExp(rev,nnarg,false,false);
			ce2.loc=loc;
			auto body2=makeLambdaBody(ce2,loc);
			auto le2=makeLambda(nparams,true,ft.isSquare,ft.annotation,body2,loc);
			return le2;
		}
	}
}

Expression lowerDefine(LowerDefineFlags flags)(Expression olhs,Expression orhs,Location loc,Scope sc,bool unchecked,bool noImplicitDup,bool defer=false,Id[2][] old=null,NeedOld* needOld=null)in{
	assert(loc.line);
}do{
	if(auto le=cast(LetExp)olhs){
		if(auto fwd=le.isForward(false))
			return lowerDefine!flags(fwd,orhs,loc,sc,unchecked,noImplicitDup,defer);
		static if(language==silq&&(flags&LowerDefineFlags.reverseMode)) if(auto fwd=le.isForward(true)){ // (`let{ x:=e; forget(…); } in x`: recomputes the forgotten variables, then reverses `e`, see `resolveForgets`)
			Expression[] r;
			auto tpl=new TupleExp([]);
			tpl.type=unit;
			tpl.loc=loc;
			foreach_reverse(t;le.s.s[1..$]) foreach_reverse(u;uncomputed(t)) r~=lowerDefine!flags(u,tpl,loc,sc,unchecked,noImplicitDup,defer);
			r~=lowerDefine!flags(fwd,orhs,loc,sc,unchecked,noImplicitDup,defer,old,needOld);
			auto res=new CompoundExp(r);
			res.loc=loc;
			return res;
		}
	}
	if(auto le=cast(LetExp)orhs){
		if(auto fwd=le.isForward(false))
			return lowerDefine!flags(olhs,fwd,loc,sc,unchecked,noImplicitDup,defer);
	}
	enum createFresh=!!(flags&LowerDefineFlags.createFresh); // TODO: can we get rid of this?
	enum reverseMode=!!(flags&LowerDefineFlags.reverseMode);
	Expression res;
	scope(success) if(res){ res.loc=loc; }
	static if(createFresh) Expression nlhs;
	Expression lhs(){ // TODO: solve better
		static if(createFresh){
			if(nlhs) return nlhs;
			static if(language==silq) nlhs=reevaluationCopy(olhs); // (see `embeddedForgets`)
			else nlhs=olhs.copy();
			if(noImplicitDup){ // TODO: this is a hack
				void removeImplicitDup(Expression e,Expression o,bool inCall){ // (`o`: the original of `e`)
					if(cast(Identifier)e)
						if(!inCall||!o.type||!o.type.isClassical()) // (a classical argument of a reversed call is an input of the reversal, it is checked)
							e.implicitDup=false;
					if(auto tae=cast(TypeAnnotationExp)e){
						removeImplicitDup(tae.e,(cast(TypeAnnotationExp)o).e,inCall);
					}else if(auto tpl=cast(TupleExp)e){
						foreach(i,ne;tpl.e)
							removeImplicitDup(ne,(cast(TupleExp)o).e[i],inCall);
					}else if(auto let=cast(LetExp)e){
						if(auto fwd=let.isForward(false))
							if(auto ofwd=(cast(LetExp)o).isForward(false))
								removeImplicitDup(fwd,ofwd,inCall);
					}else if(auto ce=cast(CallExp)e){
						removeImplicitDup(ce.arg,(cast(CallExp)o).arg,true);
					}
				}
				removeImplicitDup(nlhs,olhs,false);
			}
			return nlhs;
		}else return olhs;
	}
	static if(createFresh) Expression nrhs;
	Expression rhs(){ // TODO: solve better
		static if(createFresh){
			if(!nrhs) nrhs=orhs.copy();
			return nrhs;
		}else return orhs;
	}
	Expression error(){
		res=new DefineExp(lhs,rhs);
		res.setSemError();
		return res;
	}
	static if(language==silq&&reverseMode) if(auto le=cast(LambdaExp)olhs){ // (uncomputes the copies of the quantum values that it captures, as for a local function)
		auto captureAnnotation=le.fd.ftype?le.fd.ftype.captureAnnotation:le.fd.getCaptureAnnotation();
		if(captureAnnotation==CaptureAnnotation.const_) return res=new ForgetExp(rhs,olhs.copy());
	}
	static if(reverseMode){
		if(!noImplicitDup&&cast(Identifier)olhs&&olhs.type&&olhs.type.isClassical()){
			lhs.implicitDup=true;
			(cast(Identifier)lhs).moved=false; // (the classical value is checked, it remains available)
		}
	}
	static if(language==silq){
		if(auto le=cast(LetExp)olhs){
			if(!le.isForward(true)){
				static if(reverseMode) if(recomputable(le)) return res=new ForgetExp(rhs,lhs); // (e.g., for a conditional in it whose branches forget its locals)
				return res=lowerLetDefine(le,rhs,loc,sc,old,needOld);
			}
		}
	}
	static if(language==silq&&reverseMode){
		auto bare=olhs;
		for(auto tae=cast(TypeAnnotationExp)bare;tae;tae=cast(TypeAnnotationExp)bare) bare=tae.e;
		bool lowered=cast(LetExp)bare||cast(IteExp)bare&&olhs.isSemCompleted(); // (a `let` expression, as above, or an analyzed conditional, also with type annotations: their blocks may forget variables that the reversal recomputes, see below)
	}else enum lowered=false;
	if(defer&&!cast(ForgetExp)olhs&&!lowered){
		static if(language==silq) return res=new DefineExp(reevaluationCopy(olhs),rhs); // (keeps implicit duplications of analyzed statements)
		else return res=new DefineExp(olhs.copy(),rhs); // (keeps implicit duplications of analyzed statements)
	}
	bool classicalReverse=false;
	static if(language==silq&&!(flags&LowerDefineFlags.reverseMode)) classicalReverse=isClassicalReverseCall(olhs,orhs);
	if(!classicalReverse&&validDefLhs!flags(olhs,sc,unchecked,noImplicitDup)){
		if(auto tpl=cast(TupleExp)olhs) if(!tpl.e.length&&(cast(CallExp)orhs||cast(ForgetExp)orhs)) return rhs;
		if(auto ce=cast(CallExp)lhs) ce.checkReverse&=!unchecked;
		return res=new DefineExp(lhs,rhs);
	}
	Expression forget(){ return res=new ForgetExp(rhs,lhs); }
	if(auto vec=cast(VectorExp)olhs){
		static if(language==silq) auto newLhs=new TupleExp((cast(VectorExp)reevaluationCopy(vec)).e);
		else auto newLhs=new TupleExp(vec.copy().e);
		newLhs.loc=olhs.loc;
		auto newRhs=orhs;
		if(auto aty=cast(ArrayTy)orhs.type){
			auto tty=tupleTy(aty.next.repeat(vec.e.length).array); // TODO: use vectorTy?
			newRhs=new TypeAnnotationExp(orhs,tty,TypeAnnotationType.coercion);
			newRhs.type=tty;
			newRhs.loc=orhs.loc;
		}
		return lowerDefine!flags(newLhs,newRhs,loc,sc,unchecked,noImplicitDup);
	}
	if(auto tpll=cast(TupleExp)olhs){
		auto tplr=new TupleExp(iota(tpll.e.length).map!(delegate Expression(i)=>temporaryIdentifier(orhs.loc)).array);
		tplr.loc=orhs.loc;
		auto d1=lowerDefine!(flags&~LowerDefineFlags.createFresh)(tplr,rhs,loc,sc,unchecked,noImplicitDup);
		enforce(tpll.e.length==tplr.e.length);
		Expression[] es;
		foreach_reverse(i;0..tpll.e.length){
			es~=lowerDefine!flags(tpll.e[i],moveExp(tplr.e[i]),loc,sc,unchecked,noImplicitDup); // TODO: evaluation order of rhs okay?
		}
		if(es.any!(x=>!x)) return null;
		auto d2=new CompoundExp(es);
		d2.loc=loc;
		return res=new CompoundExp([d1,d2]);
	}
	if(cast(Identifier)olhs?isLiftedBuiltIn(olhs):isLiftedBuiltIn(lhs)){
		static if(createFresh){ // (`dup(e):=x` forgets `x` with the value of `e`, which the forget only reads, e.g., `forget(x=v[0])` for an implicit duplication of a component in a branch of a `with` transformation: a copy would remain)
			for(auto e=lhs;;){
				e.implicitDup=false;
				auto tae=cast(TypeAnnotationExp)e;
				if(!tae) break;
				e=tae.e;
			}
		}
		return forget();
	}
	static if(reverseMode) if(auto fe=cast(FieldExp)olhs) if(fe.type&&fe.type.isClassical()) return forget(); // (e.g., the reversal of `t:=f(x).length`, which checks the value)
	if(auto ce=cast(CallExp)olhs){
		if(isForgettableCallLhs(ce))
			return forget();
	}
	if(auto tae=cast(TypeAnnotationExp)olhs){
		if(auto ce=cast(CallExp)tae.e) if(tae.type&&ce.type&&!typeExplicitConversion(tae.type,ce.type,TypeAnnotationType.coercion)){ // (only the reversed call classicalizes: moved non-entry arguments are defined through temporaries)
			Expression[] unpacks;
			Expression entry(Expression arg){
				if(cast(Identifier)arg||cast(IndexExp)arg||cast(SliceExp)arg) return arg;
				auto tmp=new Identifier(freshName);
				tmp.loc=arg.loc;
				auto use=tmp.copy();
				use.moved=true;
				unpacks~=lowerDefine!flags(arg,use,loc,sc,unchecked,noImplicitDup);
				return tmp;
			}
			Expression nce=ce;
			auto ft=cast(FunTy)ce.e.type, tpl=cast(TupleExp)ce.arg;
			if(ft&&ft.isSquare==ce.isSquare){
				Expression narg=ce.arg;
				if(!ft.isConstForReverse.any) narg=entry(ce.arg);
				else if(tpl&&!ft.isConstForReverse.all&&tpl.length==ft.nargs){
					narg=new TupleExp(iota(tpl.length).map!(i=>ft.isConstForReverse[i]?tpl.e[i]:entry(tpl.e[i])).array);
					narg.loc=tpl.loc;
				}
				if(unpacks.length){
					nce=new CallExp(ce.e,narg,ce.isSquare,ce.isClassical_);
					nce.loc=ce.loc;
				}
			}
			auto def=lowerDefine!flags(nce,orhs,loc,sc,unchecked,noImplicitDup);
			if(!unpacks.length) return def;
			return res=new CompoundExp([def]~unpacks);
		}
		static if(reverseMode){
			if(olhs.type){
				if(!orhs.type||orhs.type!=tae.e.type){
					auto newRhs=new TypeAnnotationExp(rhs,tae.e.type,TypeAnnotationType.coercion);
					newRhs.loc=orhs.loc;
					return lowerDefine!flags(tae.e,newRhs,loc,sc,unchecked,noImplicitDup,defer,old,needOld);
				}else return lowerDefine!flags(tae.e,orhs,loc,sc,unchecked,noImplicitDup,defer,old,needOld);
			}
		}
		Expression newRhs;
		if(tae.annotationType==TypeAnnotationType.coercion&&tae.e.type){
			newRhs=new TypeAnnotationExp(orhs,tae.e.type,tae.annotationType);
		}else{
			// TOOD: only do this if lhs is variable
			newRhs=new TypeAnnotationExp(orhs,tae.t,tae.annotationType);
		}
		newRhs.loc=orhs.loc;
		return lowerDefine!flags(tae.e,newRhs,loc,sc,unchecked,noImplicitDup,defer,old,needOld);
	}
	if(auto ce=cast(CatExp)olhs){
		//scope(exit) imported!"util.io".writeln(olhs," := ",orhs," → ",res);
		auto l1=knownLength(ce.e1,false),l2=knownLength(ce.e2,false);
		if(!l1&&!l2){
			sc.error("concatenation of arrays of unknown length not supported as definition left-hand side",ce.loc);
			return error();
		}
		if(l1) l1=l1.copy();
		if(l2) l2=l2.copy();
		auto known1=knownLength(ce.e1,true),known2=knownLength(ce.e2,true);
		Expression[] stmts=[];
		auto ne1=ce.e1,ne2=ce.e2;
		auto ue1=unwrap(ne1),ue2=unwrap(ne2);
		auto valid1=cast(Identifier)ue1&&(noImplicitDup||!ue1.implicitDup),valid2=cast(Identifier)ue2&&(noImplicitDup||!ue2.implicitDup); // (consistent with `validDefLhs`)
		if(!valid1){
			auto tmpe1=new Identifier(freshName);
			tmpe1.loc=ce.e1.loc;
			auto use1=tmpe1.copy();
			use1.moved=true;
			stmts~=lowerDefine!flags(ne1,use1,loc,sc,unchecked,noImplicitDup);
			ne1=tmpe1.copy();
			ne1.loc=ce.e1.loc;
		}
		if(!valid2){
			auto tmpe2=new Identifier(freshName);
			tmpe2.loc=ce.e2.loc;
			auto use2=tmpe2.copy();
			use2.moved=true;
			stmts~=lowerDefine!flags(ne2,use2,loc,sc,unchecked,noImplicitDup);
			ne2=tmpe2.copy();
			ne2.loc=ce.e2.loc;
		}
		assert(l1||l2);
		if(!(known1&&valid1)&&l1){
			static if(reverseMode) ne1=unwrap(ne1); // TODO: ok?
			auto w1=new WildcardExp();
			w1.loc=ce.e1.loc;
			auto ty1=new PowExp(w1,l1);
			ty1.loc=ce.e1.loc;
			auto tae1=new TypeAnnotationExp(ne1,ty1,TypeAnnotationType.coercion);
			tae1.fromElaboration=true;
			ne1=tae1;
			ne1.loc=ce.e1.loc;
		}
		if(!(known2&&valid2)&&l2){
			static if(reverseMode) ne2=unwrap(ne2); // TODO: ok?
			auto w2=new WildcardExp();
			w2.loc=ce.e2.loc;
			auto ty2=new PowExp(w2,l2);
			ty2.loc=ce.e2.loc;
			auto tae2=new TypeAnnotationExp(ne2,ty2,TypeAnnotationType.coercion);
			tae2.fromElaboration=true;
			ne2=tae2;
			ne2.loc=ce.e2.loc;
		}
		auto nce=new CatExp(ne1,ne2);
		nce.loc=ce.loc;
		auto d=lowerDefine!flags(nce,orhs,loc,sc,unchecked,noImplicitDup);
		return res=new CompoundExp([d]~stmts);
	}
	if(auto fe=cast(ForgetExp)olhs){
		if(!fe.val){
			if(fe.var.type&&fe.var.type.isClassical()){
				return res=new CompoundExp([]); // TODO: this is a hack
			}
			sc.error("reversal of implicit forget not supported",fe.loc);
			return error();
		}
		auto tpl=cast(TupleExp)rhs;
		enforce(!tpl||tpl.length==0);
		static if(language==silq){
			auto dup=getDup(fe.val.loc,sc);
			Expression nval=new CallExp(dup,reevaluationCopy(fe.val),false,false);
		}else{
			Expression nval=fe.val.copy();
		}
		nval.type=fe.val.type;
		nval.loc=fe.val.loc;
		if(nval.type!=fe.var.type){
			nval=new TypeAnnotationExp(nval,fe.var.type,TypeAnnotationType.coercion);
			nval.type=fe.var.type;
			nval.loc=fe.val.loc;
		}
		auto def=lowerDefine!(flags&~LowerDefineFlags.reverseMode)(fe.var,nval,loc,sc,unchecked,noImplicitDup,defer);
		auto arhs=rhs;
		if(orhs.type!=unit){
			arhs=new TypeAnnotationExp(arhs,unit,TypeAnnotationType.annotation);
			arhs.type=unit;
			arhs.loc=orhs.loc;
		}
		if(!tpl) return res=new CompoundExp([arhs,def]);
		return def;
	}
	static if(language==silq)
	if(string prim=isPrimitiveCall(olhs)) {
		auto oce=cast(CallExp)olhs;
		assert(!!oce);
		Expression newlhs, newrhs;
		switch(prim) {
			case null:
				break;
			case "dup":
				//dup(arg) := orhs
				//forget(orhs=arg);
				auto ce=cast(CallExp)lhs;
				assert(!!ce);
				return new ForgetExp(rhs, ce.arg);
			case "H", "X", "Y", "Z":
				//gate(arg) := orhs
				//arg := gate(orhs)
				newlhs=oce.arg;
				newrhs=new CallExp(oce.e, orhs, false, false);
				newrhs.loc=olhs.loc;
				break;
			case "P":
				//P(arg) := orhs
				//orhs; P(-arg)
				auto ce=cast(CallExp)lhs;
				assert(!!ce);
				auto negated=new UMinusExp(ce.arg);
				negated.loc=olhs.loc;
				auto reversed=new CallExp(ce.e, negated, false, false);
				reversed.loc=olhs.loc;
				//return new CompoundExp([orhs, reversed]);
				return reversed;
			case "rZ":
				//rZ(arg[0], arg[1]) := orhs
				//orhs; rZ(-args[0], args[1])
				auto ce=cast(CallExp)lhs;
				assert(!!ce);
				auto argt = cast(TupleExp)ce.arg;
				if(!argt) {
					// TODO unpack?
					sc.error(format("cannot reverse primitive `%s`",prim),oce.e.loc);
					return error();
				}
				auto args = argt.e;
				assert(args.length==2);
				auto negated=new UMinusExp(args[0]);
				negated.loc=olhs.loc;
				auto reversed=new CallExp(ce.e, new TupleExp([negated, args[1]]), false, false);
				reversed.loc=olhs.loc;
				//return new CompoundExp([orhs, reversed]);
				return reversed;
			case "rX","rY":
				//rX(args[0], args[1]) := orhs
				//args[1] := rX(-args[0], orhs)
				auto argt = cast(TupleExp)oce.arg;
				if(!argt) {
					// TODO unpack?
					sc.error(format("cannot reverse primitive `%s`",prim),oce.e.loc);
					return error();
				}
				auto args = argt.e;
				assert(args.length==2);
				newlhs=args[1];
				auto negated=new UMinusExp(args[0]);
				negated.loc=olhs.loc;
				newrhs=new CallExp(oce.e, new TupleExp([negated, orhs]), false, false);
				newrhs.loc=olhs.loc;
				break; // DMD bug: does not detect if this is missing
			default:
				sc.error(format("cannot reverse primitive `%s`",prim),oce.e.loc);
				return error();
		}
		return lowerDefine!flags(newlhs,newrhs,loc,sc,unchecked,noImplicitDup);
	}
	static if(language==silq)
	if(auto ce=cast(CallExp)olhs){
		if(!ce.e.type){
			ce.e=expressionSemantic(ce.e,expSemContext(sc,ConstResult.yes,InType.no));
		}
		auto ft=cast(FunTy)ce.e.type;
		assert(!!ce);
		if(!ft) {
			sc.error("call to non-function not supported as definition left-hand side", ce.e.loc);
			return error();
		}
		bool needWrapper=false;
		if(ft.isSquare&&!ce.isSquare){
			if(auto ft2=cast(FunTy)ft.cod){
				ft=ft2;
				needWrapper=true;
			}else{
				sc.error("implicit function call not supported as definition left-hand side",ce.loc); // TODO?
				return error();
			}
		}
		if(!unchecked&&!needWrapper&&ft.annotation<Annotation.mfree){
			sc.error("reversed function must be `mfree`",ce.e.loc);
			explainAnnotation(sc,ce.e,Annotation.mfree);
			return error();
		}
		if(!unchecked&&!needWrapper&&!ft.isClassical){
			sc.error("quantum function call not supported as definition left-hand side",ce.loc); // TODO: support within reversed functions
			return error();
		}
		auto f=ce.e;
		auto r=reverseCallRewriter(ft,f.loc);
		if(!unchecked&&!needWrapper&&r.movedType.hasClassicalComponent()){
			sc.error("reversed function cannot have classical components in `moved` arguments", f.loc);
			return error();
		}
		Expression newlhs;
		Expression newarg;
		if(ft.isConstForReverse.all!(x=>x==ft.isConstForReverse[0])){
			if(!ft.isConstForReverse.any){
				if(cast(TupleExp)ce.arg){
					auto tmp=new Identifier(freshName);
					newlhs=new CallExp(ce.e,tmp,ce.isSquare,ce.isClassical_);
					newlhs.loc=loc;
					auto def=lowerDefine!flags(newlhs,rhs,loc,sc,unchecked,noImplicitDup);
					auto argUnpack=lowerDefine!flags(ce.arg,tmp,loc,sc,unchecked,noImplicitDup);
					return res=new CompoundExp([def,argUnpack]);
				}else{
					newlhs=ce.arg;
					auto constArg=new TupleExp([]);
					constArg.loc=orhs.loc;
					newarg=new TupleExp([constArg,orhs]);
					newarg.loc=orhs.loc;
				}
			}else{
				newlhs=new TupleExp([]);
				newlhs.loc=ce.arg.loc;
				newarg=new TupleExp([ce.arg,orhs]);
				newarg.loc=ce.arg.loc.to(orhs.loc);
			}
		}else if(auto tpl=cast(TupleExp)ce.arg){
			assert(ft.isTuple);
			if(ft.nargs==tpl.length){
				auto constMovedArgs=r.reorderArguments(tpl); // note: this changes order of assertion failures. ok?
				newlhs=constMovedArgs[1];
				newarg=new TupleExp([constMovedArgs[0],orhs]);
				newarg.loc=constMovedArgs[0].loc.to(orhs.loc);
			}else{
				explainArgumentCount(ce,ft,tpl.length,sc);
				return error();
			}
		}else{
			sc.error("cannot match single tuple to function with mixed `const` and consumed parameters",ce.loc);
			return error();
		}
		auto checked=!unchecked;
		enum simplify=false, outerWanted=false;
		auto rev=getReverse(ce.e.loc,sc,Annotation.mfree,outerWanted);
		auto reversed=tryReverse(rev,ce.e,false,false,sc,checked,simplify);
		if(ce.e.isSemError()) return error();
		if(!reversed){
			auto ce2=new CallExp(rev,ce.e,false,false);
			ce2.loc=ce.e.loc;
			ce2.checkReverse=checked;
			reversed=ce2;
		}
		auto newrhs=new CallExp(reversed,newarg,ce.isSquare,ce.isClassical_);
		newrhs.loc=newarg.loc;
		return lowerDefine!flags(newlhs,newrhs,loc,sc,unchecked,noImplicitDup);
	}
	static if(language==silq)
	if(auto vfe=cast(VectorForExp)olhs){
		static Expression dupVariableUses(Expression e,SetX!Id names,Scope sc){ // TODO: this is a hack
			Expression dupWrap(Expression e){
				auto ce=new CallExp(getDup(e.loc,sc),e,false,false);
				ce.loc=e.loc;
				return ce;
			}
			Expression rec(Expression e,out bool known){
				known=false;
				if(!e) return e;
				Expression recWrap(Expression e){
					bool k;
					auto r=rec(e,k);
					return k?dupWrap(r):r;
				}
				if(auto id=cast(Identifier)e){
					known=!!(id.id in names);
					return e;
				}
				if(cast(LiteralExp)e){
					known=true;
					return e;
				}
				if(auto tpl=cast(TupleExp)e){
					auto ks=new bool[](tpl.e.length);
					foreach(i,ref x;tpl.e) x=rec(x,ks[i]);
					if(tpl.e.length&&ks.all){ known=true; return e; }
					foreach(i,ref x;tpl.e) if(ks[i]) x=dupWrap(x);
					return e;
				}
				if(auto vec=cast(VectorExp)e){
					auto ks=new bool[](vec.e.length);
					foreach(i,ref x;vec.e) x=rec(x,ks[i]);
					if(vec.e.length&&ks.all){ known=true; return e; }
					foreach(i,ref x;vec.e) if(ks[i]) x=dupWrap(x);
					return e;
				}
				if(auto ce=cast(CallExp)e){
					ce.e=recWrap(ce.e);
					if(!ce.isSquare){
						if(auto tpl=cast(TupleExp)ce.arg){
							foreach(ref x;tpl.e) x=recWrap(x);
						}else ce.arg=recWrap(ce.arg);
					}
					return e;
				}
				if(auto tae=cast(TypeAnnotationExp)e){
					tae.e=rec(tae.e,known);
					return e;
				}
				if(auto idx=cast(IndexExp)e){
					bool ke,ka;
					idx.e=rec(idx.e,ke);
					idx.a=rec(idx.a,ka);
					known=ke&&ka;
					if(!known&&ke) idx.e=dupWrap(idx.e);
					return e;
				}
				if(auto sl=cast(SliceExp)e){
					bool ke;
					sl.e=rec(sl.e,ke);
					known=ke;
					return e;
				}
				if(auto ue=cast(AUnaryExp)e){
					ue.e=rec(ue.e,known);
					return e;
				}
				if(auto be=cast(ABinaryExp)e){
					bool k1,k2;
					be.e1=rec(be.e1,k1);
					be.e2=rec(be.e2,k2);
					known=k1&&k2;
					if(!known){
						if(k1) be.e1=dupWrap(be.e1);
						if(k2) be.e2=dupWrap(be.e2);
					}
					return e;
				}
				if(auto nvfe=cast(VectorForExp)e){
					bool shadowed=nvfe.fe.var&&nvfe.fe.var.id in names;
					if(nvfe.fe.pattern) nvfe.fe.pattern.freeVarsImpl((id){ if(id.id in names) shadowed=true; return 0; });
					if(auto nrange=nvfe.fe.aggr.isRange){
						nrange.left=recWrap(nrange.left);
						if(nrange.step) nrange.step=recWrap(nrange.step);
						nrange.right=recWrap(nrange.right);
					}else if(auto ncnt=nvfe.fe.aggr.isContainer())
						ncnt.e=recWrap(ncnt.e);
					if(!shadowed){
						bool kb;
						nvfe.fe.bdy.s[0]=rec(nvfe.fe.bdy.s[0],kb);
					}
					return e;
				}
				return e;
			}
			bool k;
			auto r=rec(e,k);
			return k?dupWrap(r):r;
		}
		if(auto range=vfe.fe.aggr.isRange){
			auto restId=new Identifier(freshName());
			restId.loc=orhs.loc;
			auto restDef=new DefineExp(restId,rhs);
			restDef.loc=loc;
			auto xId=new Identifier(freshName());
			xId.loc=vfe.fe.bdy.s[0].loc;
			auto xTpl=new TupleExp([cast(Expression)xId]);
			xTpl.loc=xId.loc;
			auto peelLhs=new CatExp(xTpl,restId.copy());
			peelLhs.loc=xId.loc;
			auto restUse=restId.copy();
			restUse.moved=true;
			auto peel=new DefineExp(peelLhs,restUse);
			peel.loc=xId.loc;
			auto bodyLhs=vfe.fe.bdy.s[0].copy();
			SetX!Id loopVarNames;
			if(vfe.fe.var) loopVarNames[vfe.fe.var.id]=[];
			if(vfe.fe.pattern) vfe.fe.pattern.freeVarsImpl((id){ loopVarNames[id.id]=[]; return 0; });
			bodyLhs=dupVariableUses(bodyLhs,loopVarNames,sc);
			auto xUse=xId.copy();
			xUse.moved=true;
			auto bodyDef=new DefineExp(bodyLhs,xUse);
			bodyDef.loc=bodyLhs.loc;
			auto lbdy=new CompoundExp([cast(Expression)peel,bodyDef]);
			lbdy.loc=vfe.fe.bdy.loc;
			auto nrange=ForRange(range.leftExclusive,range.left.copy(),range.step?range.step.copy():null,range.rightExclusive,range.right.copy());
			auto nvar=vfe.fe.var?vfe.fe.var.copy():null;
			auto npat=vfe.fe.pattern?vfe.fe.pattern.copy():null;
			auto nfe=new ForExp(nvar,npat,ForAggregate(nrange),lbdy);
			nfe.loc=vfe.fe.loc;
			auto unit=new TupleExp([]);
			unit.loc=loc;
			auto restFin=restId.copy();
			restFin.moved=true;
			auto fin=new DefineExp(unit,restFin);
			fin.loc=loc;
			return res=new CompoundExp([restDef,cast(Expression)nfe,fin]);
		}else if(auto cnt=vfe.fe.aggr.isContainer()){
			auto yid=new Identifier(freshName());
			yid.loc=orhs.loc;
			auto bodyLhs=vfe.fe.bdy.s[0].copy();
			auto yuse=yid.copy();
			yuse.loc=orhs.loc;
			yuse.moved=true;
			auto inner=new DefineExp(bodyLhs,yuse);
			inner.loc=vfe.fe.bdy.s[0].loc;
			Expression result;
			if(vfe.fe.pattern) result=vfe.fe.pattern.copy();
			else{
				assert(!!vfe.fe.var);
				result=vfe.fe.var.copy();
			}
			result.loc=vfe.fe.pattern?vfe.fe.pattern.loc:vfe.fe.var.loc;
			auto lstm=new CompoundExp([cast(Expression)inner]);
			lstm.loc=inner.loc;
			auto letExp=new LetExp(lstm,result);
			letExp.loc=inner.loc;
			auto nbdy=new CompoundExp([cast(Expression)letExp]);
			nbdy.loc=vfe.fe.bdy.loc;
			auto nfe=new ForExp(yid,null,ForAggregate(ForContainer(rhs)),nbdy);
			nfe.loc=vfe.fe.loc;
			auto nvfe=new VectorForExp(nfe);
			nvfe.loc=loc;
			return lowerDefine!flags(cnt.e,nvfe,loc,sc,unchecked,noImplicitDup);
		}else{
			sc.error("aggregate not supported in vector comprehension on definition left-hand side",vfe.fe.aggr.loc);
			return error();
		}
	}
	if(auto we=cast(WildcardExp)olhs){
		auto tmp=temporaryIdentifier(orhs.loc);
		auto de=new DefineExp(tmp,rhs);
		de.loc=rhs.loc;
		auto fe=new ForgetExp(tmp.copy(),null);
		fe.loc=loc;
		return res=new CompoundExp([de,fe]);
	}
	if(auto ite=cast(IteExp)olhs){
		if(ite.then.s.length==1&&ite.othw&&ite.othw.s.length==1){
			auto tmp=temporaryIdentifier(orhs.loc);
			auto d1=lowerDefine!flags(tmp,orhs,orhs.loc,sc,unchecked,noImplicitDup);
			auto tpl=new TupleExp([]);
			tpl.type=unit;
			tpl.loc=ite.loc;
			Expression branch(CompoundExp b,bool noImplicitDup){
				auto d=lowerDefine!(flags|LowerDefineFlags.createFresh)(b.s[0],tmp,b.s[0].loc,sc,unchecked,noImplicitDup);
				static if(language==silq&&(flags&LowerDefineFlags.reverseMode)) if(b.blscope_){ // (recomputes the variables that the branch forgets at its end, then those that it forgets on entry, see `resolveForgets`)
					Expression[] r;
					foreach_reverse(u;uncomputationOf(b.exitUncomputation,b.blscope_.forgottenVars,b.loc)) r~=lowerDefine!flags(u,tpl,b.loc,sc,unchecked,noImplicitDup);
					r~=d;
					foreach_reverse(u;uncomputationOf(b.entryUncomputation,b.blscope_.forgottenVarsOnEntry,b.loc)) r~=lowerDefine!flags(u,tpl,b.loc,sc,unchecked,noImplicitDup);
					if(r.length>1){
						auto res=new CompoundExp(mergeCompound(r));
						res.loc=b.loc;
						return res;
					}
				}
				return d;
			}
			auto nerrors=sc.handler.nerrors;
			auto dthen=branch(ite.then,noImplicitDup);
			auto dothw=branch(ite.othw,noImplicitDup);
			if(noImplicitDup&&sc.handler.nerrors==nerrors){ // (a branch cannot restore a variable that the other one does not restore: then both forget the copies of their implicit duplications instead, e.g., of `w` in `if c then w else e`)
				bool[Id] outer;
				foreach(id;ite.freeIdentifiers) outer[nameOf(id)]=true;
				auto rthen=definedNames(dthen).filter!(n=>n in outer).array,rothw=definedNames(dothw).filter!(n=>n in outer).array;
				if(!rthen.all!(n=>rothw.canFind(n))||!rothw.all!(n=>rthen.canFind(n))){
					dthen=branch(ite.then,false);
					dothw=branch(ite.othw,false);
				}
			}
			static if(language==silq) auto cond=createFresh?reevaluationCopy(ite.cond):ite.cond;
			else auto cond=createFresh?ite.cond.copy():ite.cond;
			auto blthen=cast(CompoundExp)dthen;
			if(!blthen) blthen=new CompoundExp([dthen]);
			auto blothw=cast(CompoundExp)dothw;
			if(!blothw) blothw=new CompoundExp([dothw]);
			auto nite=new IteExp(cond,blthen,blothw);
			nite.loc=ite.loc;
			Expression[] hoisted;
			static if(language==silq&&(flags&LowerDefineFlags.reverseMode)) foreach_reverse(u;ite.uncomputation) hoisted~=lowerDefine!flags(u,tpl,ite.loc,sc,unchecked,noImplicitDup); // (the variables that both branches forget, see `resolveForgets`)
			return res=new CompoundExp([d1]~hoisted~[cast(Expression)nite]);
		}
	}
	sc.error("not supported as definition left-hand side",olhs.loc);
	return error();
}
// rev(x:=y;) ⇒ y:=x;
// rev(x:=H(y);) ⇒ H(y):=x; ⇒ y:=reverse(H)(x);
// rev(x:=dup(y);) ⇒ dup(y):=x; ⇒ ():=reverse(dup)(x,y) ⇒ ():=forget(x=dup(y));
// rev(x:=CNOT(a,b);) ⇒ CNOT(a,b):=x; ⇒ a:=reverse(CNOT)(x,b);

Expression lowerDefine(LowerDefineFlags flags)(DefineExp e,Scope sc,bool unchecked,bool noImplicitDup){
	if(e.isSemError()) return e;
	if(validDefLhs!flags(e.e1,sc,unchecked,noImplicitDup)){
		static if(language==silq&&!(flags&LowerDefineFlags.reverseMode)){
			if(!isClassicalReverseCall(e.e1,e.e2)) return null;
		}else return null;
	}
	return lowerDefine!flags(e.e1,e.e2,e.loc,sc,unchecked,noImplicitDup);
}

static if(language==silq)
bool isClassicalReverseCall(Expression lhs,Expression rhs){
	auto ce=cast(CallExp)lhs;
	if(!ce||ce.isSquare||!rhs||!rhs.type||!rhs.type.isClassical()) return false;
	if(!ce.e.type) return false;
	if(!ce.checkReverse) return false;
	if(auto tpl=cast(TupleExp)ce.arg) if(!tpl.length) return false;
	auto ft=cast(FunTy)ce.e.type;
	if(!ft||ft.isSquare||ft.annotation<Annotation.qfree||!ce.e.type.isClassical()) return false;
	if(!ft.isConstForReverse.any) return true;
	if(ft.isConstForReverse.all) return false;
	auto tpl=cast(TupleExp)ce.arg;
	if(!tpl||tpl.length!=ft.nargs) return false;
	foreach(i,arg;tpl.e)
		if(ft.isConstForReverse[i]&&!(arg.type&&arg.type.isClassical()))
			return false;
	return true;
}

static if(language==silq)
Expression lowerLetDefine(LetExp le,Expression orhs,Location loc,Scope sc,Id[2][] old=null,NeedOld* needOld=null,ABinaryExp update=null)in{ // (`update`: an update whose right-hand side is the `let` expression, e.g., `y⊕=(let{ a:=t; } in a⊕x)`, instead of a definition from `orhs`)
	assert(!le.isForward(true));
}do{
	enum unchecked=false,noImplicitDup=true;
	// let-pattern bodies are not analyzed; defer lowering of flipped defines to semantic analysis
	auto hoist=le.s.isSemCompleted(); // (the classical locals of an analyzed `let` are recomputed, as for a nested block, and the received values are checked against them)
	auto value=le.e;
	Expression[] tail;
	static if(language==silq){
		TypeAnnotationExp[] annotations;
		auto inner=le.e;
		for(auto tae=cast(TypeAnnotationExp)inner;tae;tae=cast(TypeAnnotationExp)inner){
			annotations~=tae;
			inner=tae.e;
		}
		if(auto fle=continuedLet(le)){ // (`let{ … } in let{ x:=e; forget(…); } in x`, also with a type annotation, e.g., for the result `s⊕0:𝔹`: its statements continue with those of the inner `let`, see `resolveForgets`)
			value=fle.e;
			foreach_reverse(tae;annotations){
				auto nv=new TypeAnnotationExp(value,tae.t.copy(),tae.annotationType);
				nv.loc=tae.loc;
				value=nv;
			}
			tail=fle.s.s;
		}
	}
	Id[] kept; // (the variables of the block that the result forgets, which the reversal of an update recomputes before it, see `resultForgets`)
	static if(language==silq) if(update) foreach(u;le.resultUncomputation) if(auto fe=cast(ForgetExp)u) foreach(v;forgottenVariables(fe)) if(auto id=cast(Identifier)unwrap(v)) kept~=nameOf(id);
	Expression mlhs=reevaluationCopy(value,null,kept),mrhs=orhs; // (see `embeddedForgets`)
	if(hoist) if(auto lt=cast(TupleExp)unwrap(value)) if(auto rt=cast(TupleExp)orhs) if(lt.length==rt.length){ // (without the classical variables of the enclosing block that it returns, e.g., `k` in `(y,k):=let { k+=1; … } in (z,k)`: the received version is the current one, which the reversal changes in place)
		Expression[] ls,rs;
		foreach(i;0..lt.length){
			auto li=cast(Identifier)lt.e[i],ri=cast(Identifier)rt.e[i];
			if(li&&ri&&li.type&&li.type.isClassical()&&nameOf(li)==nameOf(ri)&&!chain(le.s.s,tail).map!definedNames.joiner.canFind(nameOf(li))) continue;
			ls~=reevaluationCopy(lt.e[i]);
			rs~=rt.e[i];
		}
		if(ls.length&&ls.length<lt.length){
			Expression tuple(Expression[] es,Location l){
				if(es.length==1) return es[0];
				auto tpl=new TupleExp(es);
				tpl.loc=l;
				return tpl;
			}
			mlhs=tuple(ls,value.loc);
			mrhs=tuple(rs,orhs.loc);
		}
	}
	Expression def,received=mrhs; // (the definition of the result, and the received value, which the renamings below leave alone)
	Expression[] pre;
	static if(language==silq) if(hoist&&mrhs is orhs&&!update){
		auto v=unwrap(value),nested=cast(LetExp)v;
		if(v.isSemCompleted()&&(cast(IteExp)v||nested&&!nested.isForward(true))){ // (an analyzed conditional or `let` expression, whose blocks may forget variables that its reversal recomputes, see `lowerDefine`)
			auto tmp=temporaryIdentifier(loc);
			auto bind=new DefineExp(tmp,mrhs);
			bind.loc=loc;
			pre=[bind];
			def=lowerDefine!(LowerDefineFlags.createFresh|LowerDefineFlags.reverseMode)(value,tmp.copy(),loc,sc,unchecked,noImplicitDup,true);
			received=null;
		}
	}
	if(!def){
		if(update) def=reevaluationCopy(update,(Expression x)=>x is le?mlhs:null); // (evaluated again, between the reversal of the block and the recomputation of its forgets, see below)
		else{
			def=new DefineExp(mlhs,mrhs);
			def.loc=loc;
		}
	}
	Id[] copied,excludedCopied; // (the classical variables of the enclosing block that the `let` expression changes and consumes: the reversal recomputes the changes on copies, as the enclosing block recomputes the versions before them)
	if(hoist){
		Id[] result,local;
		foreach(e;[value,update?update.e1:orhs]) foreach(x;e.subexpressions) if(auto id=cast(Identifier)x) result~=nameOf(id); // (also a new version that the definition defines, e.g., `(y,k):=let { k+=1; … } in (z,0)`, which the enclosing block may recompute)
		foreach(s;mergeCompound(le.s.s~tail)){
			foreach(n;changedNames(s)) if(!copied.canFind(n)&&!local.canFind(n)&&!result.canFind(n)) copied~=n;
			local~=definedNames(s);
		}
		foreach(o;old) if(!copied.canFind(o[0])) copied~=o[0]; // (e.g., a variable of the enclosing block that it returns, see `NeedOld`)
	}
	Expression[] middle=[def];
	static if(language==silq){
		if(update) foreach(u;le.resultUncomputation) middle=reverseStatement(u,sc,unchecked,noImplicitDup,false,true)~middle;
		auto stmts=le.s.blscope_?uncomputationOf(le.s.entryUncomputation,le.s.blscope_.forgottenVarsOnEntry,le.s.loc)~le.s.s~tail:le.s.s~tail;
		if(le.s.blscope_) foreach(u;uncomputationOf(le.s.exitUncomputation,le.s.blscope_.forgottenVars,le.s.loc)){ // (the forgets after the result: the reversal recomputes their quantum variables before it uncomputes the result, as for the branches of a conditional, see `lowerDefine`)
			auto fe=cast(ForgetExp)u;
			if(fe&&forgottenVariables(fe).all!(v=>v.type&&v.type.isClassical())) stmts~=u;
			else middle=reverseStatement(u,sc,unchecked,noImplicitDup,false,true)~middle;
		}
	}else auto stmts=le.s.s;
	auto r=new CompoundExp(reverseStatements(stmts,middle,sc,unchecked,noImplicitDup,hoist,true,hoist?middle.map!definedNames.joiner.array:null,null,copied,&excludedCopied,forgottenNames(le.s),needOld));
	r.loc=loc;
	static if(language==silq) if(hoist){
		renameLocals(le,r,received);
		if(copied.length){
			MapSX!(Id,Id) renames;
			Expression[] copies;
			foreach(n;copied){
				renames[n]=freshName();
				if(excludedCopied.canFind(n)) continue; // (its changes are reversed in place, but its current version is the one before them)
				auto src=old.find!(o=>o[0]==n);
				auto lhs=new Identifier(renames[n]),var=new Identifier(src.empty?n:src.front[1]);
				lhs.loc=var.loc=loc;
				auto rhs=new CallExp(getDup(loc,sc),var,false,false);
				rhs.loc=loc;
				auto cpy=new DefineExp(lhs,rhs);
				cpy.loc=loc;
				copies~=cpy;
			}
			walkIdentifiers(r,(Identifier id){ if(!id.meaning) if(auto p=renames.getPtr(id.id)) id.id=*p; },true,received);
			r.s=copies~r.s;
		}
	}
	r.s=pre~r.s;
	return r;
}

static if(language==silq)
Expression[] copiesOf(Expression r,Id[2][] old,Id[] excluded,Location loc,Scope sc){ // (renames the variables in `old` within the reversal `r` of a block to copies of their versions before it, except for the excluded ones, as in `lowerLetDefine`)
	MapSX!(Id,Id) renames;
	Expression[] copies;
	foreach(o;old){
		renames[o[0]]=freshName();
		if(excluded.canFind(o[0])) continue;
		auto lhs=new Identifier(renames[o[0]]),var=new Identifier(o[1]);
		lhs.loc=var.loc=loc;
		auto rhs=new CallExp(getDup(loc,sc),var,false,false);
		rhs.loc=loc;
		auto cpy=new DefineExp(lhs,rhs);
		cpy.loc=loc;
		copies~=cpy;
	}
	walkIdentifiers(r,(Identifier id){ if(!id.meaning) if(auto p=renames.getPtr(id.id)) id.id=*p; },true);
	return copies;
}

static if(language==silq)
void renameLocals(LetExp le,Expression r,Expression skip){ // (the reversal of a `let` expression is not scoped like it, e.g., two `let` expressions with locals of the same name)
	import ast.substitute: collectBoundNamesImpl;
	auto src=le.copy();
	SetX!Id bound,free;
	foreach(stmt;src.s.s) collectBoundNamesImpl(stmt,bound);
	src.freeVarsImpl((Identifier id){ free.insert(id.id); return 0; });
	MapSX!(Id,Id) renames;
	foreach(b;bound) if(b !in free) renames[b]=freshName();
	if(renames.length) walkIdentifiers(r,(Identifier id){ if(!id.meaning) if(auto p=renames.getPtr(id.id)) id.id=*p; },true,skip);
}

static if(language==silq)
Expression renamedLocals(Expression r,Id[] names){ // (the variables of its own of a recomputed statement whose names have versions that the recomputation of the block keeps, e.g., `v` for `if c { v:=1; … }` after `w:=move(v)`: later statements do not see them)
	MapSX!(Id,Id) renames;
	foreach(n;names) renames[n]=freshName();
	if(renames.length) walkIdentifiers(r,(Identifier id){ if(!id.meaning) if(auto p=renames.getPtr(id.id)) id.id=*p; },true);
	return r;
}

private bool copyAttr(Id name) {
	switch(name.str) {
		case "artificial":
		case "inline":
			return true;
		default:
			return false;
	}
}

private bool hasLoop(Expression e){
	foreach(x;e.subexpressions)
		if(isLoopStatement(x))
			return true;
	return false;
}

static if(language==silq)
FunctionDef reverseFunction(FunctionDef fd)in{
	assert(fd.scope_&&fd.ftype&&fd.ftype.captureAnnotation<=CaptureAnnotation.const_&&fd.ftype.annotation>=Annotation.mfree);
}do{
	enum flags=LowerDefineFlags.createFresh|LowerDefineFlags.reverseMode;
	enum unchecked=true; // TODO: ok?
	enum noImplicitDup=false;
	if(fd.reversed) return fd.reversed;
	auto sc=fd.scope_, ft=fd.ftype;
	auto asc=sc;
	foreach(meaning;fd.capturedDecls){ // TODO: this is a bit hacky
		if(meaning&&meaning.scope_&&meaning.scope_.canInsert(meaning.name.id)){
			auto scope_=meaning.scope_;
			meaning.scope_=null;
			meaning.rename=null;
			scope_.clearConsumed(); // TODO: get rid of this
			if(!scope_.insert(meaning,true))
				fd.setSemError();
		}
	}
	void resurrect(Declaration decl){ // TODO: this is a bit hacky
		if(!decl||!decl.name||!decl.name.id) return;
		auto scope_=decl.scope_;
		if(!scope_||!scope_.canInsert(decl.name.id)) return;
		decl.scope_=null;
		decl.rename=null;
		scope_.clearConsumed(); // TODO: get rid of this
		if(!scope_.insert(decl,true))
			fd.setSemError();
	}
	resurrect(fd);
	for(auto c=sc;c;c=c.parentScope())
		if(auto fsc=cast(FunctionScope)c)
			resurrect(fsc.fd);
	auto r=reverseCallRewriter(fd.ftype,fd.loc);
	auto bfd=fd;
	if(astopt.removeLoops&&fd.body_&&fd.origBody_&&hasLoop(fd.origBody_)){
		auto src=new FunctionDef(null,fd.params.map!(p=>p.copy()).array,fd.isTuple,fd.rret?fd.rret.copy():null,fd.origBody_.copy());
		src.copyIntrinsicFieldsFrom(fd);
		src.keepLoops=true;
		src.loc=fd.loc;
		src.scope_=sc;
		src=cast(FunctionDef)presemantic(src,sc);
		if(src) src=functionDefSemantic(src,sc);
		if(src&&(src.isSemCompleted()||src.sstate==SemState.passive)) bfd=src;
		foreach(meaning;fd.capturedDecls) resurrect(meaning); // (the analysis of `src` consumes the captures that it moves, as the definition of `fd` did)
	}
	// enforce(!argTypes.any!(t=>t.hasClassicalComponent()),"reversed function cannot have classical components in consumed arguments"); // lack of classical components may not be statically known at the point of function definition due to generic parameters
	auto fbody_=bfd.body_;
	if(!fbody_){
		if(isPrimitive(fd)){
			if(fd.name){
				auto id=new Identifier(fd.name.id);
				id.loc=fd.loc;
				id.meaning=fd;
				id.type=fd.ftype;
				id.sstate=SemState.completed;
				auto ids=fd.params.map!(delegate Expression(p){
					auto id=new Identifier(p.name.id);
					id.constLookup=p.isConst;
					id.meaning=p;
					id.type=p.vtype;
					id.sstate=SemState.completed;
					id.loc=p.loc;
					return id;
				}).array;
				Expression arg;
				if(fd.isTuple){
					arg=new TupleExp(ids);
					arg.loc=fd.loc;
					arg.type=tupleTy(ids.map!(id=>id.type).array);
					arg.sstate=SemState.completed;
				}else{
					assert(ids.length==1);
					arg=ids[0];
				}
				auto ce=new CallExp(id,arg,fd.isSquare,false);
				ce.loc=fd.loc;
				ce.type=fd.ftype.tryApply(arg,fd.isSquare);
				ce.sstate=SemState.completed;
				auto ret=new ReturnExp(ce);
				ret.loc=fd.loc;
				ret.type=bottom;
				ret.sstate=SemState.completed;
				auto cmp=new CompoundExp([ret]);
				cmp.loc=fd.loc;
				cmp.type=bottom;
				fbody_=cmp;
			}else{
				sc.error("cannot reverse nested function",fd.loc);
				enforce(0,text("errors while reversing function"));
			}
		}else{
			sc.error("cannot reverse function without body",fd.loc);
			enforce(0,text("errors while reversing function"));
		}
	}

	bool simplify=r.innerNeeded;
	ReturnExp getRet(CompoundExp bdy){
		if(!bdy||!bdy.s.length) return null;
		if(auto ret=cast(ReturnExp)bdy.s[$-1]) return ret;
		if(auto ce=cast(CompoundExp)bdy.s[$-1]) return getRet(ce);
		return null;
	}
	auto ret=getRet(fbody_);
	if(!ret){
		sc.error("reversing early returns not supported yet",fd.loc);
		enforce(0,text("errors while reversing function"));
	}
	static if(language==silq) resolveForgets(fbody_);
	Id cpname,rpname;
	bool retDefReplaced=false;
	if(auto id=cast(Identifier)ret.e){
		if(!id.implicitDup&&validDefLhs!flags(id,sc,unchecked,noImplicitDup)){
			auto name=(id.meaning&&id.meaning.name?id.meaning.name:id).id;
			if(!r.constIndices.any!(i=>fd.params[i].name&&fd.params[i].name.id==name)){
				retDefReplaced=true;
				rpname=name;
			}
		}
	}
	if(!retDefReplaced) rpname=freshName();
	Expression dom, cod;
	bool isTuple;
	bool[] isConst;
	Id[] pnames;
	Expression constUnpack=null;
	foreach(id;r.returnType.freeIdentifiers){
		if(!id.meaning){
			sc.error("reversing functions whose domain depends on codomain not supported yet",fd.loc);
			enforce(0,text("errors while reversing function"));
		}
	}
	if(simplify&&r.constIndices.empty){
		dom=r.returnType;
		cod=r.movedType;
		isTuple=false;
		isConst=[false];
		pnames=[rpname];
	}else if(simplify&&isEmptyTupleTy(r.returnType)){
		dom=r.constType;
		cod=r.movedType;
		isTuple=r.constTuple;
		isConst=r.constIndices.map!(_=>true).array;
		pnames=r.constIndices.map!(i=>fd.params[i].name.id).array;
	}else{
		dom=tupleTy(r.constLast?[r.returnType,r.constType]:[r.constType,r.returnType]);
		cod=r.movedType;
		isTuple=true;
		isConst=r.constLast?[false,true]:[true,false];
		auto cids=r.constIndices.map!((i){
			auto name=fd.params[i].name.name;
			Expression id=new Identifier(name);
			id.loc=fd.params[i].loc;
			return id;
		}).array;
		assert(r.constTuple||cids.length==1);
		if(r.constTuple){
			cpname=freshName();
			auto clhs=new TupleExp(cids);
			auto cloc=cids.length?cids[0].loc.to(cids[$-1].loc):fd.loc;
			clhs.loc=cloc;
			auto crhs=new Identifier(cpname);
			crhs.loc=cloc;
			constUnpack=new DefineExp(clhs,crhs);
			// TODO: unpacked variables will not be const declarations, maybe conflicts with implicit dup?
		}else{
			assert(cids.length==1);
			auto id=cast(Identifier)cids[0];
			assert(!!id);
			cpname=id.id;
		}
		pnames=r.constLast?[rpname,cpname]:[cpname,rpname];
	}
	assert(pnames.length==isConst.length);
	auto params=iota(pnames.length).map!((i){
		auto pname=new Identifier(pnames[i]);
		pname.loc=fd.loc;
		Expression type;
		if(!isTuple){
			assert(i==0);
			type=dom;
		}else{
			auto tt=dom.isTupleTy;
			assert(!!tt&&tt.length==pnames.length);
			type=tt[i];
		}
		auto param=new Parameter(isConst[i],pname,type);
		param.loc=pname.loc;
		return param;
	}).array;
	Expression retRhs;
	if(simplify&&isEmptyTupleTy(r.returnType)) retRhs=new TupleExp([]);
	else retRhs=new Identifier(rpname);
	retRhs.loc=ret.loc;
	retRhs.type=r.returnType;
	retRhs.loc=ret.loc;
	auto body_=new CompoundExp([]);
	body_.loc=fbody_.loc;
	auto result=new FunctionDef(null,params,isTuple,cod,body_);
	foreach(name, val; fd.attributes) {
		if(copyAttr(name)) result.attributes[name] = val;
	}
	result.isSquare=fd.isSquare;
	result.annotation=fd.annotation;
	result.scope_=sc;
	result=cast(FunctionDef)presemantic(result,sc);
	assert(!!result);
	if(fd.annotation>=Annotation.qfree && r.movedIndices.empty){
		Expression argExp;
		if(isEmptyTupleTy(r.constType)) argExp=new TupleExp([]);
		else if(cpname){ // TODO: would probably be better to not create the temporary at all in this case
			argExp=new Identifier(cpname);
		}else{
			argExp=isTuple?new TupleExp(fd.params.map!(p=>cast(Expression)p.name.copy()).array):fd.params[0].name.copy();
		}
		Expression call=null;
		argExp.loc=fd.loc; // TODO: use precise parameter locations
		argExp.type=r.constType;
		auto nfd=fd.copy();
		auto fun=new LambdaExp(nfd);
		fun.loc=fd.loc;
		call=new CallExp(fun,argExp,fd.isSquare,false);
		call.loc=fd.loc;
		auto fe=New!ForgetExp(retRhs,call);
		fe.loc=fd.loc;
		body_.s=[fe];
	}else{
		bool retDefNecessary=!(isEmptyTupleTy(r.returnType)&&cast(TupleExp)ret.e||retDefReplaced);
		static if(language==silq) auto retForgets=uncomputationOf(ret.uncomputation,ret.forgottenVars,ret.loc); // (forgotten after the return value)
		else Expression[] retForgets=[];
		auto retDef=retDefNecessary?lowerDefine!flags(ret.e,retRhs,ret.loc,result.fscope_,unchecked,noImplicitDup):null;
		auto movedNames=r.movedIndices.map!(i=>fd.params[i].name.name).array;
		Expression[] movedTypes;
		if(r.movedTuple){
			auto tt=r.movedType.isTupleTy();
			assert(!!tt);
			movedTypes=iota(tt.length).map!(i=>tt[i]).array;
		}else movedTypes=[r.movedType];
		auto makeMoved(size_t i){
			Expression r;
			if(isEmptyTupleTy(movedTypes[i])) r=new TupleExp([]); // TODO: use last-use analysis instead
			else r=new Identifier(movedNames[i]);
			r.loc=ret.loc;
			r.type=movedTypes[i];
			return r;
		}
		auto argExp=r.movedTuple?new TupleExp(iota(movedTypes.length).map!makeMoved.array):makeMoved(0);
		argExp.loc=fd.loc; // TODO: use precise parameter locations
		argExp=new TypeAnnotationExp(argExp,cod,TypeAnnotationType.coercion);
		argExp.loc=fd.loc; // TODO: use precise parameter locations
		Expression argRet=new ReturnExp(argExp);
		argRet.loc=argExp.loc;
		auto given=(retDef?definedNames(retDef):[])~(retDefReplaced?[rpname]:[]);
		auto received=r.constIndices.filter!(i=>!!fd.params[i].name).map!(i=>fd.params[i].name.id).array; // (parameters of the reversed function as well)
		Id[] copied,excludedCopied; // (classical parameters that the function changes or returns: the reversal recomputes them on copies, as the variables of an enclosing block in `lowerLetDefine`)
		static if(language==silq) foreach(i;r.constIndices) if(auto p=fd.params[i].name) if(!fd.params[i].isConst){
			auto stmts=fbody_.s[0..$-1];
			if(stmts.any!(s=>s.subexpressions.any!(x=>cast(DefineExp)x&&definedNames(x).canFind(p.id)&&!changedNames(x).canFind(p.id)))) continue; // (another variable of the same name)
			if(given.canFind(p.id)||stmts.any!(s=>changedNames(s).canFind(p.id))) copied~=p.id;
		}
		auto nerrors=sc.handler.nerrors;
		auto rev=new CompoundExp(reverseStatements(fbody_.s[0..$-1]~retForgets,retDef?[retDef]:[],bfd.fscope_,unchecked,noImplicitDup,true,false,given,received.filter!(n=>!copied.canFind(n)).array,copied,&excludedCopied));
		rev.loc=fbody_.loc;
		if(sc.handler.nerrors==nerrors) foreach(n;excludedCopied) if(!given.canFind(n)){ // (its changes are reversed in place, but the reversal does not receive the version at the end, e.g., if the classical part of a `with` statement reads a variable that the reversal changes in place, see `projection`)
			auto changing=mergeCompound(fbody_.s[0..$-1]).map!uncomputed.joiner.filter!(s=>changedNames(s).canFind(n)&&classifyStatement(s)!=ComputationClass.classical).array; // (as in `reverseStatements`)
			auto s=changing.find!(s=>!projection(s,bfd.fscope_));
			if(s.empty) s=changing;
			sc.error(format("reversal of change of classical parameter `%s` that is not returned not supported yet",n),s.empty?fd.loc:s.front.loc);
			enforce(0,text("errors while reversing function"));
		}
		static if(language==silq) auto copies=copiesOf(rev,copied.map!(n=>cast(Id[2])[n,n]).array,excludedCopied,fd.loc,result.fscope_); // (an excluded one is reversed in place from the version that the reversal receives)
		else Expression[] copies=[];
		body_.s=mergeCompound((constUnpack?[constUnpack]:[])~copies~rev.s)~[argRet];
	}
	static if(__traits(hasMember,astopt,"dumpReverse")) if(astopt.dumpReverse){
		import util.io:stderr;
		stderr.writeln(fd);
		stderr.writeln("-reverse→");
		stderr.writeln(result);
	}
	result=functionDefSemantic(result,sc);
	if(result.sstate==SemState.passive) result.setSemCompleted(); // TODO: ok?
	enforce(result.isSemCompleted(),text("semantic errors while reversing function"));
	if(equal(fd.ftype.isConst,only(true,false))) result.reversed=fd; // TODO: fix condition
	fd.reversed=result;
	return result;
}

enum ComputationClass{
	bottom,
	classical,
	quantum,
	mixed,
	unsupported
}

ComputationClass join(ComputationClass a,ComputationClass b){
	with(ComputationClass){
		if(a==bottom) return b;
		if(b==bottom) return a;
		if(a==unsupported) return a;
		if(b==unsupported) return b;
		if(a==b) return a;
		return mixed;
	}
}

ComputationClass classifyExpression(Expression e){
	with(ComputationClass){
		if(isClassicalExp(e)) return classical;
		if(e.type.hasClassicalComponent()) return mixed;
		return quantum;
	}
}

ComputationClass classifyStatement(Expression e){
	with(ComputationClass){
		if(auto ce=cast(CallExp)e) return ComputationClass.quantum; // ok?
		if(auto ce=cast(CompoundExp)e){
			static if(language==silq) if(ce.loweredFrom) return classifyStatement(ce.loweredFrom);
			assert(0);
		}
		if(auto ite=cast(IteExp)e){
			if(!ite.cond.type.isClassical()) return ComputationClass.quantum;
			//return chain(ite.then.s,ite.othw?ite.othw.s:[]).map!classifyStatement.reduce!join(classical); // ???
			auto r=bottom;
			foreach(s;chain(ite.then.s,ite.othw?ite.othw.s:[])){
				static if(language==silq) if(auto fe=cast(ForgetExp)s) if(!fe.val&&fe.var.type&&fe.var.type.isClassical()) continue; // (a forget of classical variables, e.g., of a variable that a branch defines for itself, `v` in `if c { w:=move(v); v:=w+1; } else { w:=move(v); }`: the recomputation renames it, see `recomputation`)
				r=join(r,classifyStatement(s));
			}
			return r==bottom?classical:r; // (e.g., `if t>1 { }`, as for `classicalUpToForgets`)
		}
		if(auto we=cast(WithExp)e){
			//return join(classifyExpression(we.trans,we.bdy));
			static if(language==silq) if(we.subexpressions.all!(x=>(!x.type||x.type.isClassical())&&!cast(LambdaExp)x&&!cast(FunctionDef)x&&!cast(ReturnExp)x)) return classical; // (e.g., an update or a swap of components of a classical vector, which is recomputed like `t+=c`, see `changedNames` and `recomputation`)
			return ComputationClass.quantum; // ok?
		}
		if(auto ret=cast(ReturnExp)e){
			if(ret.e.type.isClassical()) return classical;
			if(!ret.e.type.hasClassicalComponent()) return quantum;
			return mixed;
		}
		if(auto fd=cast(FunctionDef)e){
			if(fd.ftype.isClassical()) return classical;
			return mixed;
		}
		// TODO: DatDecl?
		if(auto ce=cast(CommaExp)e) assert(0);
		if(auto de=cast(DefineExp)e){
			assert(!!de.e2.type);
			if(auto tpl=cast(TupleExp)unwrap(de.e2))
				if(tpl.length==0) // TODO: this is a hack, support properly
					return ComputationClass.quantum;
			if(auto tpl=cast(TupleExp)unwrap(de.e1))
				if(tpl.length==0) // TODO: this is a hack, support properly
					return ComputationClass.quantum;
			static if(language==silq) if(isClassicalMove(de)) return classical; // (recomputed, see `recomputation`)
			return classifyExpression(de.e2);
		}
		if(auto ae=cast(AssignExp)e) return unsupported;
		if(isOpAssignExp(e)){
			auto be=cast(ABinaryExp)e;
			assert(!!be);
			assert(!!be.e2.type);
			static if(language==silq) if(be.e1.type&&be.e1.type.isClassical()) return classical; // (recomputed, see `changedNames`)
			if(be.e2.type.isClassical()) return unsupported;
			if(!be.e2.type.hasClassicalComponent())
				return isInvertibleOpAssignExp(e)?quantum:unsupported;
			return mixed;
		}
		auto classifyBody(CompoundExp e){
			static if(language==silq)
				if(e.blscope_&&e.blscope_.forgottenVars.any!(d=>d.isLinear())) return unsupported;
			bool anyQuantum=false;
			bool anyMixed=false;
			bool anyUnsupported=false;
			foreach(c;e.s.map!classifyStatement){
				final switch(c){
					case bottom: assert(0);
					case classical: break;
					case quantum: anyQuantum=true; break;
					case mixed: anyMixed=true; break;
					case unsupported: anyUnsupported=true; break;
				}
			}
			if(anyUnsupported) return unsupported;
			if(anyMixed) return mixed;
			if(anyQuantum) return quantum;
			return classical;
		}
		if(auto fe=cast(ForExp)e) return classifyBody(fe.bdy);
		if(auto we=cast(WhileExp)e) return unsupported;
		static if(language==silq) if(auto dw=cast(DoWhileExp)e) return unsupported;
		if(auto re=cast(RepeatExp)e) return classifyBody(re.bdy);
		if(auto oe=cast(ObserveExp)e) enforce(0);
		if(auto oe=cast(CObserveExp)e) enforce(0);
		if(auto ae=cast(AssertExp)e){
			assert(!!ae.e.type);
			if(ae.e.type.isClassical()) return classical;
			if(!ae.e.type.hasClassicalComponent) return quantum;
			enforce(0);
		}
		if(auto fe=cast(ForgetExp)e) return quantum;
	}
	enforce(0,text("unsupported: ",e));
	assert(0);
}
Expression[] mergeCompound(Expression[] s){
	Expression[] r;
	foreach(e;s){
		if(auto ce=cast(CompoundExp)e){
			static if(language==silq) if(ce.loweredFrom){ // (a lowered loop is reversed as the loop)
				mergeCompound([ce.loweredFrom]);
				r~=ce;
				continue;
			}
			assert(!ce.blscope_);
			r~=mergeCompound(ce.s);
			continue;
		}
		if(auto ce=cast(CommaExp)e){
			r~=mergeCompound([ce.e1]);
			r~=mergeCompound([ce.e2]);
			continue;
		}
		if(auto ite=cast(IteExp)e){
			assert(!!ite.then);
			ite.then.s=mergeCompound(ite.then.s);
			if(ite.othw) ite.othw.s=mergeCompound(ite.othw.s);
		}
		if(auto fe=cast(ForExp)e) fe.bdy.s=mergeCompound(fe.bdy.s);
		if(auto we=cast(WhileExp)e) we.bdy.s=mergeCompound(we.bdy.s);
		if(auto re=cast(RepeatExp)e) re.bdy.s=mergeCompound(re.bdy.s);
		static if(language==silq) if(auto dw=cast(DoWhileExp)e){
			dw.bdy.s=mergeCompound(dw.bdy.s);
			if(dw.reset) dw.reset.s=mergeCompound(dw.reset.s);
		}
		r~=e;
	}
	return r;
}

static if(language==silq)
bool isClassicalMove(Expression e){ // (a classical definition that moves classical variables, e.g., at their last use, also into a new version of a moved variable, e.g., `v:=v coerce !uint[2]`, whose recomputation keeps the version before it for the reversals of earlier statements, see `oldVersions`)
	auto de=cast(DefineExp)e;
	if(!de||de.isSwap||!de.e2.type) return false;
	return de.e2.subexpressions.all!(x=>!x.type||x.type.isClassical())&&de.e2.isQfree()&&de.e2.consumes;
}

Identifier[] definedIdentifiers(Expression e){ // (the variables that a definition introduces)
	Identifier[] r;
	void rec(Expression e){
		e=unwrap(e);
		if(auto id=cast(Identifier)e){
			if(!id.implicitDup) r~=id;
		}else if(auto tpl=cast(TupleExp)e) foreach(x;tpl.e) rec(x);
		else if(auto vec=cast(VectorExp)e) foreach(x;vec.e) rec(x);
		else if(auto ce=cast(CatExp)e){ rec(ce.e1); rec(ce.e2); }
	}
	if(auto de=cast(DefineExp)e) rec(de.e1);
	else if(auto ce=cast(CompoundExp)e) foreach(s;ce.s) r~=definedIdentifiers(s);
	return r;
}
Id nameOf(Identifier id){ return (id.meaning&&id.meaning.name?id.meaning.name:id).id; }
static if(language==silq)
bool consumesBeforeDefining(Expression s,Id name,bool* survives=null){ // (on each path on which a statement defines a variable called `name`, it first forgets or moves the version before it, e.g., for `with { … } do { forget(v); with { … } do { v:=2; } }`; `survives`: whether that version is available after it on some path, e.g., for `if c { forget(v); v:=2; }`)
	bool ok=true;
	bool rec(Expression e,bool alive){ // (`alive`: the version before the statement)
		if(!ok||cast(FunctionDef)e||cast(LambdaExp)e) return alive;
		if(auto fe=cast(ForgetExp)e){
			foreach(v;forgottenVariables(fe)) if(auto id=cast(Identifier)unwrap(v)) if(nameOf(id)==name) alive=false;
			return alive;
		}
		if(auto id=cast(Identifier)e) return alive&&!(nameOf(id)==name&&(id.moved||!id.constLookup&&!id.implicitDup));
		if(auto de=cast(DefineExp)e){
			alive=rec(de.e2,alive);
			if(definedNames(de).canFind(name)){
				if(alive) ok=false;
				return false;
			}
			return alive;
		}
		if(auto ite=cast(IteExp)e){
			alive=rec(ite.cond,alive);
			auto a=rec(ite.then,alive),b=ite.othw?rec(ite.othw,alive):alive;
			return a||b;
		}
		if(cast(ForExp)e||cast(RepeatExp)e||cast(WhileExp)e){ // (the body may not run)
			foreach(c;e.components) rec(c,alive);
			return alive;
		}
		if(auto ce=cast(CompoundExp)e) if(ce.blscope_){ // (also the forgets that the analysis adds, e.g., of `v` on entry to the `else` branch of `if c { w:=move(v); }`)
			bool forgets(Declaration[] ds){ return ds.any!(d=>d.name&&d.name.id==name); }
			if(forgets(ce.blscope_.forgottenVarsOnEntry)) alive=false;
			foreach(c;ce.s) alive=rec(c,alive);
			if(forgets(ce.blscope_.forgottenVars)) alive=false;
			return alive;
		}
		foreach(c;e.components) alive=rec(c,alive);
		return alive;
	}
	auto alive=rec(s,true);
	if(survives) *survives=alive;
	return ok;
}
static if(language==silq)
bool definesForItself(Expression s,Id name){ // (whether no version of a variable called `name` that a statement defines is available after it, e.g., for `w:=move(v); if c { v:=w+1; … }`, but not for `if c { forget(v); v:=1; }`, after which the new version is available if `c` holds)
	auto own=declaredWithin(s);
	bool isOwn(Identifier id){ return id.meaning&&isVersionOf(id.meaning,own); }
	static struct State{ bool available,own; } // (the variable is available, and it may be a version that the statement defines)
	State merge(State a,State b){ auto available=a.available&&b.available; return State(available,available&&(a.own||b.own)); }
	State rec(Expression e,State st){ // (also for lowered statements, whose copies it renames, e.g., not `t` for the lowering of `for i in 0..2 { t+=c; }` with `--remove-loops`, which defines `t` again)
		if(cast(FunctionDef)e||cast(LambdaExp)e) return st;
		if(auto fe=cast(ForgetExp)e){
			if(fe.val) st=rec(fe.val,st);
			if(forgottenVariables(fe).any!(v=>cast(Identifier)unwrap(v)&&nameOf(cast(Identifier)unwrap(v))==name)) return State(false,false);
			return st;
		}
		if(auto id=cast(Identifier)e) return id.moved&&nameOf(id)==name?State(false,false):st;
		if(auto de=cast(DefineExp)e){
			st=rec(de.e2,st);
			return definedNames(de).canFind(name)?State(true,true):st;
		}
		if(auto ite=cast(IteExp)e){
			st=rec(ite.cond,st);
			return merge(rec(ite.then,st),ite.othw?rec(ite.othw,st):st);
		}
		if(cast(ForExp)e||cast(RepeatExp)e||cast(WhileExp)e){ // (the body may not run)
			auto r=st;
			foreach(c;e.components) r=rec(c,r);
			return merge(st,r);
		}
		foreach(c;e.components) st=rec(c,st);
		return st;
	}
	auto before=s.subexpressions.any!(x=>cast(Identifier)x&&nameOf(cast(Identifier)x)==name&&!isOwn(cast(Identifier)x)); // (it mentions the version before it, which is then available before it)
	return !rec(s,State(before,false)).own;
}
static if(language==silq)
bool readsBeforeDefining(Expression s,Id name,bool forgets=false){ // (whether a statement reads the version before it of a variable called `name` before it defines the variable, other than to forget it unless `forgets`, e.g., `j` for `(xs,j):=let{ j-=1; … } in (xs,j);`, but not `w` for `w:=dup(u); if c { w+=u; forget(w); }`)
	bool reads=false;
	bool rec(Expression e,bool defined){ // (returns whether the statement has defined the variable after `e`)
		if(reads||cast(FunctionDef)e||cast(LambdaExp)e) return defined;
		if(auto fe=cast(ForgetExp)e) if(!forgets) return fe.val?rec(fe.val,defined):defined;
		if(auto id=cast(Identifier)e){
			if(!defined&&nameOf(id)==name) reads=true;
			return defined;
		}
		if(auto de=cast(DefineExp)e){
			defined=rec(de.e2,defined);
			auto targets=definedIdentifiers(de);
			foreach(x;de.e1.subexpressions) if(auto id=cast(Identifier)x) if(!targets.canFind!(t=>t is id)&&!defined&&nameOf(id)==name) reads=true;
			return defined||targets.any!(id=>nameOf(id)==name);
		}
		if(auto ite=cast(IteExp)e){
			defined=rec(ite.cond,defined);
			auto then=rec(ite.then,defined),othw=ite.othw?rec(ite.othw,defined):defined;
			return then&&othw;
		}
		if(cast(ForExp)e||cast(RepeatExp)e||cast(WhileExp)e){ // (the body may not run)
			foreach(c;e.components) rec(c,defined);
			return defined;
		}
		foreach(c;e.components) defined=rec(c,defined);
		return defined;
	}
	rec(s,false);
	return reads;
}
static if(language==silq)
bool definedInBlocks(CompoundExp b,Id name){ // (whether a block defines a variable called `name` only in nested blocks whose reversals receive the versions that it defines, e.g., not in a loop, in a `let` expression or in a transformation, see `reverseStatement`)
	bool rec(Expression e){
		if(auto ce=cast(CompoundExp)e) return ce.loweredFrom?rec(ce.loweredFrom):ce.s.all!rec;
		if(auto ite=cast(IteExp)e) return !definedWithin(ite.cond).canFind(name)&&rec(ite.then)&&(!ite.othw||rec(ite.othw));
		if(auto we=cast(WithExp)e) return !definedWithin(we.trans).canFind(name)&&rec(we.bdy);
		if(auto de=cast(DefineExp)e) return !definedWithin(de.e2).canFind(name);
		return !definedWithin(e).canFind(name);
	}
	return rec(b);
}
static if(language==silq)
private bool consumesVariable(Expression e,Id name){ // (whether an expression forgets or moves a variable called `name`, e.g., `w:=move(v)` in the classical part of `if c { w:=move(v); v:=w+1; xs[v]:=X(xs[v]); } else { w:=move(v); }`)
	foreach(x;e.subexpressions){
		if(auto fe=cast(ForgetExp)x) if(forgottenVariables(fe).any!(v=>cast(Identifier)unwrap(v)&&nameOf(cast(Identifier)unwrap(v))==name)) return true;
		if(auto id=cast(Identifier)x) if(id.moved&&nameOf(id)==name) return true;
	}
	return false;
}
private bool consumesOuterVersion(Expression e,Id name){ // (as `consumesVariable`, but not where it only forgets or moves a version of its own, e.g., not `v` for `with { … } do { v:=u*2; w:=move(v); }`)
	bool rec(Expression e,ref bool own){
		if(cast(FunctionDef)e||cast(LambdaExp)e) return false;
		if(auto fe=cast(ForgetExp)e) if(!own&&forgottenVariables(fe).any!(v=>cast(Identifier)unwrap(v)&&nameOf(cast(Identifier)unwrap(v))==name)) return true;
		if(auto id=cast(Identifier)e) return !own&&id.moved&&nameOf(id)==name;
		if(auto de=cast(DefineExp)e){
			if(rec(de.e2,own)) return true;
			if(definedNames(de).canFind(name)) own=true;
			return false;
		}
		if(auto ite=cast(IteExp)e){
			if(rec(ite.cond,own)) return true;
			bool inThen=own,inOthw=own;
			if(rec(ite.then,inThen)||ite.othw&&rec(ite.othw,inOthw)) return true;
			own=inThen&&inOthw;
			return false;
		}
		foreach(x;e.components) if(rec(x,own)) return true;
		return false;
	}
	bool own=false;
	return rec(e,own);
}
static if(language==silq)
bool readsBefore(Expression s,Id name){ // (whether a statement reads the version before it of a variable called `name` other than to forget it, e.g., not for `v` in `with { … } do { with { … } do { forget(v); } v:=2; }`)
	auto own=declaredWithin(s);
	bool rec(Expression e){
		if(auto fe=cast(ForgetExp)e) return fe.val&&rec(fe.val);
		if(auto id=cast(Identifier)e) return nameOf(id)==name&&!(id.meaning&&isVersionOf(id.meaning,own));
		return e.components.any!rec;
	}
	return rec(s);
}
bool readsOther(Expression s,Id name){ // (whether a statement mentions a variable called `name` other than one of its own, e.g., not for `v` in `with { … } do { v:=j+3; w:=move(v); }`)
	SetX!Declaration own;
	foreach(x;s.subexpressions) if(auto de=cast(DefineExp)x) foreach(id;definedIdentifiers(de)) if(id.meaning) own.insert(id.meaning);
	foreach(x;s.subexpressions) if(auto id=cast(Identifier)x) if(nameOf(id)==name&&!(id.meaning&&id.meaning in own)) return true;
	return false;
}
bool readsBesidesMove(Expression s,Id name){ // (as `readsOther`, but not where the statement moves the variable into its own new version, e.g., not for `v` in `(w,v):=(2,v)`, but for `(w,v):=(v*2,v)`, see `movedIntoItself`)
	SetX!Declaration own;
	Identifier[] moved;
	void pairs(Expression l,Expression r){
		l=unwrap(l);
		r=unwrap(r);
		if(auto lid=cast(Identifier)l){
			auto rid=cast(Identifier)r;
			if(rid&&nameOf(lid)==name&&nameOf(rid)==name&&(rid.moved||!rid.constLookup&&!rid.implicitDup)) moved~=rid;
			return;
		}
		auto lt=cast(TupleExp)l,rt=cast(TupleExp)r;
		if(lt&&rt&&lt.length==rt.length) foreach(i;0..lt.length) pairs(lt.e[i],rt.e[i]);
	}
	foreach(x;s.subexpressions) if(auto de=cast(DefineExp)x){
		foreach(id;definedIdentifiers(de)) if(id.meaning) own.insert(id.meaning);
		if(!de.isSwap) pairs(de.e1,de.e2);
	}
	foreach(x;s.subexpressions) if(auto id=cast(Identifier)x) if(nameOf(id)==name&&!(id.meaning&&id.meaning in own)&&!moved.any!(m=>m is id)) return true;
	return false;
}
Id[] forgottenNames(CompoundExp ce){ // (the variables that a block forgets at its end)
	Id[] r;
	static if(language==silq) if(ce.blscope_) foreach(d;ce.blscope_.forgottenVars) if(d.name) r~=d.name.id;
	return r;
}
Id[] definedNames(Expression e){
	bool available(CompoundExp b,Id n){ // (e.g., not `v` for `v:=u+1; w:=dup(v); forget(v);`)
		static if(language==silq) return availableAfter(b,n);
		else return true;
	}
	if(auto we=cast(WithExp)e){ // (the variables that the body defines, other than those of the transformation, which the inverse restores)
		auto trans=definedNames(we.trans);
		return definedNames(we.bdy).filter!(n=>!trans.canFind(n)&&available(we.bdy,n)).array;
	}
	if(auto ite=cast(IteExp)e){ // (the variables that both branches define)
		auto othw=ite.othw?definedNames(ite.othw):[];
		return definedNames(ite.then).filter!(n=>othw.canFind(n)&&available(ite.then,n)&&available(ite.othw,n)).array;
	}
	if(auto ce=cast(CompoundExp)e){ // (not lazily: `joiner` evaluates the elements of `map` more than once, which is exponential for nested blocks, e.g., chains of `else if`)
		Id[] r;
		foreach(s;ce.s) r~=definedNames(s);
		return r;
	}
	return definedIdentifiers(e).map!nameOf.array;
}
static if(language==silq){
Identifier[] escapingIdentifiers(Expression e){ // (as for `definedNames`, also the variables that the body of a `with` statement defines)
	if(auto we=cast(WithExp)e) return escapingIdentifiers(we.bdy);
	if(auto ite=cast(IteExp)e){
		auto othw=ite.othw?escapingIdentifiers(ite.othw):[];
		return escapingIdentifiers(ite.then).filter!(id=>othw.any!(jd=>nameOf(jd)==nameOf(id))).array;
	}
	if(auto ce=cast(CompoundExp)e){
		if(ce.loweredFrom) return escapingIdentifiers(ce.loweredFrom);
		Identifier[] r;
		foreach(s;ce.s) r~=escapingIdentifiers(s);
		return r;
	}
	return definedIdentifiers(e);
}
bool availableAfter(Expression e,Id n,bool avail=true){ // (whether a classical variable is available after a statement, e.g., not after `with { … } do { forget(v); if c { v:=1; } }`)
	if(cast(FunctionDef)e||cast(LambdaExp)e) return avail;
	if(auto ce=cast(CompoundExp)e){
		if(ce.loweredFrom) return availableAfter(ce.loweredFrom,n,avail);
		foreach(s;ce.s) avail=availableAfter(s,n,avail);
		return avail;
	}
	if(auto ite=cast(IteExp)e){
		avail=availableAfter(ite.cond,n,avail);
		auto then=availableAfter(ite.then,n,avail);
		return then&&(ite.othw?availableAfter(ite.othw,n,avail):avail);
	}
	if(auto we=cast(WithExp)e) return availableAfter(we.bdy,n,availableAfter(we.trans,n,avail));
	if(auto fe=cast(ForExp)e) return avail&&availableAfter(fe.bdy,n,avail); // (an iteration starts with the versions after the previous one; the variables of the body of its own are not available after the loop)
	if(auto re=cast(RepeatExp)e) return avail&&availableAfter(re.bdy,n,avail);
	if(auto fe=cast(ForgetExp)e){
		if(fe.val) avail=availableAfter(fe.val,n,avail);
		return avail&&!forgottenVariables(fe).any!(v=>cast(Identifier)unwrap(v)&&nameOf(cast(Identifier)unwrap(v))==n);
	}
	if(auto de=cast(DefineExp)e) return availableAfter(de.e2,n,avail)||definedNames(de).canFind(n);
	foreach(x;e.subexpressions) if(auto id=cast(Identifier)x) if(id.moved&&nameOf(id)==n) return false;
	return avail;
}
Id[] classicalEscapingNames(Expression e){ return escapingIdentifiers(e).filter!(id=>id.type&&id.type.isClassical()).map!nameOf.array; }
}

Expression[] transStatements(WithExp we){ // (also those of nested blocks, e.g., `a:=t` for the component `t` that an enclosing `with` statement borrows in `with { a:=v[0]; } do { … }`)
	Expression[] r;
	void rec(Expression[] ss){
		foreach(s;ss){
			auto ce=cast(CompoundExp)s;
			static if(language==silq) if(ce&&ce.loweredFrom) ce=null;
			if(ce) rec(ce.s);
			else r~=s;
		}
	}
	rec(we.trans.s);
	return r;
}

Id classicalBase(Expression e){ // (the classical variable of a component, e.g., `a` for `a[i][j]`)
	e=unwrap(e);
	while(auto idx=cast(IndexExp)e) e=unwrap(idx.e);
	auto id=cast(Identifier)e;
	return id&&id.type&&id.type.isClassical()?nameOf(id):Id();
}

Id[] changedNames(Expression e){ // (the classical variables that a statement changes, e.g., `t+=c` or `(y,t):=let { t+=c; … } in (z,t)`, other than the ones that it defines)
	auto c=changes(e);
	static if(language==silq) return c[0].filter!(n=>!c[1].canFind(n)||availableAfter(e,n)||c[2].canFind(n)).array;
	else return c[0];
}
Id[] lossyChanges(Expression e){ // (the classical variables that a statement consumes and defines again, e.g., `v` in `with { w:=1; } do { forget(v); v:=w+1; }`: the recomputation keeps their forgets and moves, see `recomputation`, so the reversal cannot recompute their versions before it from the versions after it; not if they are not available after it, e.g., for `if c { forget(v); v:=2; } else { forget(v); }`, where the reversals of its branches recompute the definitions, see `redefined` in `reverseStatements`, unless it also changes the versions before it in place, e.g., for `if c { forget(v); v:=2; } else { v+=1; xs[v%4]:=X(xs[v%4]); }`, whose reversal would revert the update from the version before it)
	auto c=changes(e);
	static if(language==silq) return c[1].filter!(n=>availableAfter(e,n)||c[2].canFind(n)).array;
	else return c[1];
}
private bool movedIntoItself(Expression s,Id n){ // (whether a statement defines `n` only by moving the version before it into the new version, e.g., `k:=k` or `(k,w):=(k,1)`, also in the body of a `with` statement: the new version is the one before it, which the reversal moves back)
	bool identity(Expression l,Expression r){
		l=unwrap(l);
		for(;;){ // (as `unwrap`, but not through a conversion or a coercion that changes the value or the type, e.g., `v:=v coerce !uint[2]` or `v:=v as !ℤ` for `v:!ℕ`, whose new version is not the one before it)
			if(auto tae=cast(TypeAnnotationExp)r){
				if(!tae.e.type||!tae.type||tae.e.type!=tae.type) return false;
				r=tae.e;
			}else if(auto let=cast(LetExp)r){
				auto fwd=let.isForward(false);
				if(!fwd) break;
				r=fwd;
			}else break;
		}
		if(auto lid=cast(Identifier)l){
			auto rid=cast(Identifier)r;
			return nameOf(lid)==n&&rid&&(rid.moved||!rid.constLookup&&!rid.implicitDup)&&nameOf(rid)==n;
		}
		auto lt=cast(TupleExp)l,rt=cast(TupleExp)r;
		return lt&&rt&&lt.length==rt.length&&iota(lt.length).any!(i=>identity(lt.e[i],rt.e[i]));
	}
	bool any=false;
	foreach(x;s.subexpressions) if(auto de=cast(DefineExp)x) if(definedNames(de).canFind(n)){
		if(de.isSwap||!identity(de.e1,de.e2)) return false;
		any=true;
	}
	return any;
}
private Id[][3] changes(Expression e,Id[]* consumedOut=null){ // (`consumedOut`: the variables of enclosing blocks that it forgets or moves; the third list: the variables whose versions before it it changes in place, see `lossyChanges`)
	Id[] r,local,consumed,lossy,inPlace;
	void change(Id n){
		r~=n;
		if(!consumed.canFind(n)) inPlace~=n;
	}
	void rec(Expression e){
		if(cast(FunctionDef)e||cast(LambdaExp)e) return;
		if(cast(LetExp)e) return; // (it consumes the variables that it changes, and its reversal recomputes them from copies, see `lowerLetDefine`)
		static if(language==silq) if(auto ce=cast(CompoundExp)e) if(ce.loweredFrom) return rec(ce.loweredFrom);
		if(auto we=cast(WithExp)e){ // (the inverse restores what the transformation changes)
			Id[] consumedInBody;
			auto defined=definedNames(we.bdy).filter!(n=>!movedIntoItself(we.bdy,n)&&availableAfter(we.bdy,n)).array,inBody=changes(we.bdy,&consumedInBody); // (not a variable that the body only moves into its own new version, whose changes in the body count, e.g., `v` for `v+=1; (w,v):=(2,v);`, nor one that it forgets, which it changes, e.g., `k` for `(xs,k):=let{ k-=1; … } in (xs,k); k+=2;` at the last use of `k`)
			auto own=definedNames(we).filter!(n=>!movedIntoItself(we.bdy,n)&&!inBody[0].canFind(n)&&!inBody[1].canFind(n)&&!consumed.canFind(n)).array; // (new variables, as for a definition, e.g., `v` for `with { … } do { v:=u+1; }` before `w:=move(v); v:=2;`, whose move does not consume a variable of an enclosing block)
			static if(language==silq) if(classifyStatement(we)!=ComputationClass.classical){ // (the reversal of the body recomputes the definitions, see `projection`)
				inBody[0]=inBody[0].filter!(n=>!inBody[1].canFind(n)).array;
				inBody[1]=[];
			}
			foreach(n;chain(inBody[0],defined)){
				auto des=transStatements(we).map!(x=>cast(DefineExp)x).filter!(de=>de&&definedNames(de).canFind(n));
				if(!des.empty){ foreach(de;des) if(auto b=classicalBase(de.e2)) change(b); } // (the inverse writes back the component that the body changes or defines again, e.g., for `a[i]+=c` or a swap)
				else if(!defined.canFind(n)||inBody[1].canFind(n)){
					r~=n;
					if(inBody[2].canFind(n)&&!consumed.canFind(n)) inPlace~=n;
				}
			}
			lossy~=inBody[1];
			foreach(n;consumedInBody) if(!local.canFind(n)&&!consumed.canFind(n)) consumed~=n; // (e.g., `v` for `with { … } do { w:=move(v); }` before `v:=w+1;`, which defines it again)
			local~=own;
			return;
		}
		static if(language==silq){
			bool outer(Identifier id){ return id.type&&id.type.isClassical()&&!local.canFind(nameOf(id)); }
			if(auto fe=cast(ForgetExp)e) foreach(v;forgottenVariables(fe)) if(auto id=cast(Identifier)unwrap(v)) if(outer(id)) consumed~=nameOf(id);
			if(auto id=cast(Identifier)e) if(id.moved&&outer(id)) consumed~=nameOf(id);
		}
		if(auto ae=isOpAssignExp(e)) if(auto b=classicalBase(ae.e1)) change(b);
		if(auto de=cast(DefineExp)e){
			rec(de.e2); // (first, for the variables that it consumes, e.g., `v:=f(move(v))`)
			Id[] redefined; // (a new version of a variable that a `let` expression on the right-hand side consumes, e.g., `(y,k):=let { k+=1; … } in (z,k)`, which the reversals of later statements would not see if it is not recomputed; the reversal of a call checks the version that it receives)
			if(cast(LetExp)unwrap(de.e2)&&classifyStatement(de)!=ComputationClass.classical) foreach(id;definedIdentifiers(de)) if(id.type&&id.type.isClassical()){
				auto n=nameOf(id);
				foreach(x;de.e2.subexpressions) if(auto y=cast(Identifier)x) if(nameOf(y)==n){ redefined~=n; break; }
			}
			Id[] again; // (variables that it consumes before, see `lossyChanges`)
			static if(language==silq) foreach(id;definedIdentifiers(de)) if(id.type&&id.type.isClassical()){
				auto n=nameOf(id);
				if(consumed.canFind(n)&&!redefined.canFind(n)&&!movedIntoItself(de,n)) again~=n;
			}
			foreach(n;redefined) change(n);
			r~=again;
			lossy~=again;
			local~=definedNames(de).filter!(n=>!redefined.canFind(n)&&!again.canFind(n)&&!movedIntoItself(de,n)).array; // (not a variable that it moves into its own new version, whose earlier changes count, e.g., `v` for `v+=1; (w,v):=(2,v);`)
			void lhs(Expression x){ // (components of the left-hand side, e.g., of a swap `(a[0],a[1]):=(a[1],a[0])`)
				x=unwrap(x);
				if(auto tpl=cast(TupleExp)x) foreach(y;tpl.e) lhs(y);
				else if(cast(IndexExp)x) if(auto b=classicalBase(x)) change(b);
			}
			lhs(de.e1);
			rec(de.e1);
			return;
		}
		if(auto ite=cast(IteExp)e){ // (a branch changes the versions before it in place also where the other branch consumes them, e.g., `v` for `if c { forget(v); v:=2; } else { v+=1; }`)
			rec(ite.cond);
			auto before=consumed.dup;
			rec(ite.then);
			if(!ite.othw) return;
			auto inThen=consumed;
			consumed=before;
			rec(ite.othw);
			foreach(n;inThen) if(!consumed.canFind(n)) consumed~=n;
			return;
		}
		foreach(x;e.components) rec(x);
	}
	rec(e);
	if(consumedOut) *consumedOut=consumed;
	Id[] result(Id[] names){
		Id[] res;
		foreach(n;names) if(!local.canFind(n)&&!res.canFind(n)) res~=n;
		return res;
	}
	return [result(r),result(lossy),result(inPlace)];
}

Id[] writtenBack(WithExp we){ // (the classical variables into which the inverse writes back what the body changes or defines again, e.g., `k` for `with { c:=k; } do { c+=1; }`: a recomputation keeps their moves, see `recomputation`)
	Id[] r;
	auto updated=chain(changedNames(we.bdy),definedNames(we.bdy)).array;
	foreach(x;transStatements(we)) if(auto de=cast(DefineExp)x) if(definedNames(de).any!(n=>updated.canFind(n))) if(auto b=classicalBase(de.e2)) r~=b;
	return r;
}

bool readsBesidesUpdates(Expression e,Id name){ // (whether a statement reads a variable other than to update it, e.g., in `t+=c`, in a swap of components or in `a[i]+=c`)
	bool rec(Expression e,bool target=false){ // (`target`: the left-hand side of an update or a definition)
		e=unwrap(e);
		if(auto id=cast(Identifier)e) return !target&&nameOf(id)==name;
		if(target){
			if(auto idx=cast(IndexExp)e) return rec(idx.e,true)||rec(idx.a);
			if(auto tpl=cast(TupleExp)e) return tpl.e.any!(x=>rec(x,true));
		}
		if(auto ae=isOpAssignExp(e)) return rec(ae.e1,true)||rec(ae.e2);
		if(auto de=cast(DefineExp)e) return rec(de.e1,true)||rec(de.e2);
		if(auto fe=cast(ForgetExp)e) if(!fe.val) return false; // (its reversal does not need the value)
		if(auto we=cast(WithExp)e){
			auto updated=chain(changedNames(we.bdy),definedNames(we.bdy)).array;
			foreach(x;transStatements(we)){
				auto de=cast(DefineExp)x;
				if(de&&definedNames(de).any!(n=>updated.canFind(n))){ if(rec(de.e2,true)) return true; } // (a component that the inverse writes back, see `changedNames`)
				else if(rec(x)) return true;
			}
			return rec(we.bdy);
		}
		foreach(x;e.components) if(rec(x)) return true;
		return false;
	}
	return rec(e);
}

private SetX!Declaration declaredWithin(Expression s){ // (the variables that a statement or expression declares, also the new versions of updates, e.g., of `v` for `v+=1`, and those in the inverses of `with` statements, which are not components, e.g., the version of `t` that `v[0]:=t` writes back for `with { a:=v[0]; } do { a+=1; }`)
	SetX!Declaration r;
	void rec(Expression e){
		foreach(x;e.subexpressions){
			if(auto de=cast(DefineExp)x) foreach(id;definedIdentifiers(de)) if(id.meaning) r.insert(id.meaning);
			if(auto fe=cast(ForExp)x) if(fe.loopVar) r.insert(fe.loopVar);
			static if(language==silq) if(auto we=cast(WithExp)x) if(we.itrans) rec(we.itrans);
			static if(language==silq) if(auto ae=cast(AAssignExp)x) foreach(repl;ae.replacements) if(repl.new_) r.insert(repl.new_); // (not splits of the versions before them)
		}
	}
	rec(s);
	return r;
}
private bool isVersionOf(Declaration d,SetX!Declaration decls){ return d.derivedSequence.any!(o=>o in decls); } // (also in a nested block, e.g., of `s` in the branches of `let{ s:=1:𝔹; } in (if q then dup(s) else x)`)
bool recomputable(LetExp le){ // (whether the reversal can uncompute a value that an analyzed `let` expression defines by evaluating it again: it only calls `qfree` functions and only reads the variables of enclosing blocks)
	if(!le.isSemCompleted()||!hasOnlyQfreeCalls(le)) return false;
	auto local=declaredWithin(le);
	bool isLocal(Declaration d){ return isVersionOf(d,local); }
	foreach(x;le.subexpressions){
		if(cast(FunctionDef)x||cast(LambdaExp)x||cast(ReturnExp)x) return false;
		if(auto id=cast(Identifier)x){
			if(id.meaning&&!id.meaning.isToplevelDeclaration()&&!isLocal(id.meaning)&&!id.constLookup&&!id.implicitDup) return false;
		}else if(auto ce=cast(CompoundExp)x){
			if(ce.blscope_) foreach(d;chain(ce.blscope_.forgottenVarsOnEntry,ce.blscope_.forgottenVars)) if(!isLocal(d)) return false;
		}
	}
	return true;
}
bool usesUp(Id name,Expression[] statements){ // (whether the statements consume, forget or redefine a variable called `name`)
	bool rec(Expression e){
		if(auto we=cast(WithExp)e) return rec(we.bdy)&&!(we.itrans&&definedNames(we.itrans).canFind(name)); // (the inverse restores what the transformation or the body consumes, also in a loop)
		if(auto id=cast(Identifier)e)
			if(id.meaning&&id.meaning.name&&id.meaning.name.id==name&&!id.constLookup&&!id.implicitDup)
				return true;
		if(cast(DefineExp)e&&definedNames(e).canFind(name)) return true;
		foreach(x;e.components) if(rec(x)) return true;
		return false;
	}
	return statements.any!rec;
}

Expression[] headers(Expression s){ // (the condition of an `if` statement, the bounds of a `for` loop or the number of iterations of a `repeat` loop, which the reversal evaluates first)
	static if(language==silq) if(auto ce=cast(CompoundExp)s) if(ce.loweredFrom) return headers(ce.loweredFrom);
	if(auto ite=cast(IteExp)s) return [ite.cond];
	if(auto fe=cast(ForExp)s){
		if(auto rng=fe.aggr.isRange()) return [rng.left]~(rng.step?[rng.step]:[])~[rng.right];
		if(auto cnt=fe.aggr.isContainer()) return [cnt.e];
	}
	if(auto re=cast(RepeatExp)s) return [re.num];
	return [];
}

static if(language==silq)
Id[] definedWithin(Expression e){ // (the variables that a statement defines, also within nested blocks, e.g., the locals and the variable of a loop)
	Id[] r;
	foreach(x;e.subexpressions){
		if(auto de=cast(DefineExp)x) r~=definedNames(de);
		else if(auto fe=cast(ForExp)x){
			if(fe.var) r~=nameOf(fe.var);
			if(fe.pattern) foreach(y;fe.pattern.subexpressions) if(auto id=cast(Identifier)y) r~=nameOf(id);
		}
	}
	return r;
}

Expression recomputation(Expression s,Scope sc,Id[] inner=null,Id[] later=null){ // (the copy of a classical statement that the reversal of a block recomputes; `inner`: the variables of `with` statements, also of enclosing ones, e.g., the components that they move out and write back; `later`: the variables that later statements of the block define)
	Expression.CopyArgs cargs;
	static if(language==silq){
		auto own=declaredWithin(s);
		bool isOwn(Identifier id){ return id.meaning&&isVersionOf(id.meaning,own); }
		MapSX!(Id,Id) renames; // (variables that it defines again only for itself, e.g., `v` for `with { … } do { w:=move(v); if c { v:=w+1; … } }`: the copy reads the version before it, as for the other variables that it moves or forgets, and renames its own versions)
		bool renamed(Id n){ return !!renames.getPtr(n); }
		bool updatesBefore(Id n){ return s.subexpressions.any!(x=>cast(AAssignExp)x&&(cast(AAssignExp)x).replacements.any!(r=>r.previous&&r.previous.name&&r.previous.name.id==n&&!isVersionOf(r.previous,own))); } // (an update of the version before it, which the copy would not keep, e.g., `t` for `with { u:=2; } do { t+=u; w:=move(t); t:=w*2; … }`: the copy consumes it, as the statement does)
		bool carried(Id n){ // (a variable that a loop of the statement carries from one iteration to the next, e.g., `v` for `for i in 0..2 { v:=move(v); }`: the reads in the body see the version before the loop as well as the own versions, which the copy cannot rename apart)
			foreach(x;s.subexpressions){
				CompoundExp bdy=null;
				if(auto fe=cast(ForExp)x) bdy=fe.bdy;
				else if(auto re=cast(RepeatExp)x) bdy=re.bdy;
				else if(auto we=cast(WhileExp)x) bdy=we.bdy;
				if(!bdy||!definedWithin(bdy).canFind(n)) continue;
				auto inBody=declaredWithin(bdy);
				if(bdy.subexpressions.any!((y){ auto id=cast(Identifier)y; return id&&nameOf(id)==n&&id.meaning&&!isVersionOf(id.meaning,inBody); })) return true;
			}
			return false;
		}
		bool mixed(Id n){ // (a variable that only one branch of a conditional of the statement defines, after which it is available: the reads after it see the version before it as well as an own version, e.g., `v` for `if c { (w,v):=(1,v); } v+=1;`, which the copy cannot rename apart)
			foreach(x;s.subexpressions) if(auto ite=cast(IteExp)x){
				auto then=definedWithin(ite.then).canFind(n),othw=ite.othw&&definedWithin(ite.othw).canFind(n);
				if(then!=othw&&availableAfter(ite.then,n)&&(!ite.othw||availableAfter(ite.othw,n))) return true;
			}
			return false;
		}
		foreach(n;definedWithin(s)) if(!renamed(n)&&!later.canFind(n)&&!inner.canFind(n)&&definesForItself(s,n)&&!updatesBefore(n)&&!carried(n)&&!mixed(n)&&!movedIntoItself(s,n)) renames[n]=freshName(); // (not a variable that it only moves into its own new versions, which are the version before it, e.g., `v` for `(w,v):=(1,v); v+=1; forget(v);`, whose reversal changes it back in place)
		auto local=definedWithin(s).filter!(n=>!renamed(n)).array~later; // (a forget or a move of one of them may precede a definition of the same name, e.g., `with { … } do { forget(v); v:=w+1; }`)
	}
	static if(language==silq) cargs.mapExp=(Expression x,ref Expression.CopyArgs args){ // (reads the variables that it moves or forgets, such that the reversed statements see the same versions)
		if(cast(FunctionDef)x) return x.copy();
		if(auto fe=cast(ForgetExp)x){
			bool kept(Expression v){ // (e.g., at the last use of a variable of the block in a loop in the body of a `with` statement, which the reversal of an earlier statement reads)
				auto id=cast(Identifier)unwrap(v);
				return id&&id.type&&id.type.isClassical()&&(!local.canFind(nameOf(id))||movedIntoItself(s,nameOf(id))&&!later.canFind(nameOf(id)))&&(renamed(nameOf(id))?!isOwn(id):!inner.canFind(nameOf(id))); // (also one that the statement only moves into its own new versions, e.g., `v` for `(v,w):=(v,0)`, which is not one of its own)
			}
			auto vars=forgottenVariables(fe);
			if(vars.all!kept){
				auto r=new CompoundExp([]);
				r.loc=fe.loc;
				return cast(Expression)r;
			}
			if(!fe.val&&vars.any!kept){ // (together with variables of its own, e.g., `forget((w,v))` at the end of `with { … } do { (v,w):=(v,0); }`)
				auto rest=vars.filter!(v=>!kept(v)).map!(v=>v.copy(args)).array;
				Expression var=rest[0];
				if(rest.length>1){
					auto tpl=new TupleExp(rest);
					tpl.loc=fe.var.loc;
					var=tpl;
				}
				auto r=new ForgetExp(var,null);
				r.loc=fe.loc;
				return cast(Expression)r;
			}
		}
		if(auto we=cast(WithExp)x){
			inner~=chain(definedNames(we.trans),definedNames(we.bdy).filter!(n=>!movedIntoItself(we.bdy,n))).array; // (not a variable of an enclosing block that the body only moves into its own new versions)
			auto outer=inner;
			inner~=writtenBack(we);
			auto trans=we.trans.copy(args);
			inner=outer;
			auto r=new WithExp(trans,we.bdy.copy(args),we.isIndices);
			if(we.itrans&&we.isIndices) r.itrans=we.itrans.copy(args); // (as for the reversal, see `reverseStatement`)
			r.loc=we.loc;
			return cast(Expression)r;
		}
		if(auto id=cast(Identifier)x){
			if(isOwn(id)) if(auto p=renames.getPtr(nameOf(id))){
				auto r=id.copy();
				r.id=*p;
				return cast(Expression)r;
			}
			if(id.moved&&!local.canFind(nameOf(id))&&(renamed(nameOf(id))||!inner.canFind(nameOf(id)))){
				auto r=id.copy();
				r.moved=false;
				return cast(Expression)r;
			}
		}
		if(auto de=cast(DefineExp)x) if(isClassicalMove(de)&&!de.e2.subexpressions.any!((y){ auto id=cast(Identifier)y; return id&&(local.canFind(nameOf(id))||(renamed(nameOf(id))?isOwn(id):inner.canFind(nameOf(id)))); })){
			auto rhs=new CallExp(getDup(de.e2.loc,sc),de.e2.copy(args),false,false);
			rhs.loc=de.e2.loc;
			auto r=new DefineExp(de.e1.copy(args),rhs);
			r.loc=de.loc;
			return cast(Expression)r;
		}
		return null;
	};
	return s.copy(cargs);
}

static if(language==silq)
private bool withoutEffect(Expression e){ // (a part that neither defines nor changes values, e.g., an `if` statement whose branches are empty)
	if(auto ce=cast(CompoundExp)e) return ce.s.all!withoutEffect;
	if(auto ite=cast(IteExp)e) return withoutEffect(ite.then)&&(!ite.othw||withoutEffect(ite.othw));
	if(auto fe=cast(ForExp)e) return withoutEffect(fe.bdy);
	if(auto re=cast(RepeatExp)e) return withoutEffect(re.bdy);
	return false;
}
static if(language==silq)
private CompoundExp classicalPart(CompoundExp b,Scope sc,Id[] drop,Id[] vars,Expression result=null,Id[] skip=null,Id[] after=null){ // (the classical part of a block, which the reversal recomputes, see `projection`; `result`: an expression after the block that reads its variables; `after`: the variables that statements after the block define again, see `later`)
	bool readsDropped(Expression e){ return drop.length&&e.subexpressions.any!(x=>cast(Identifier)x&&drop.canFind(nameOf(cast(Identifier)x))); }
	auto ss=mergeCompound(b.s);
	auto parts=new Expression[](ss.length);
	auto omitted=new bool[](ss.length); // (statements without classical parts that define or change values, which the classical part then must not read, see `unused`)
	Id[] defined; // (the variables of the block that the classical part defines and keeps: it forgets them where the block does, unlike the variables that the block forgets otherwise, as `recomputation` does)
	CompoundExp forgetting(Id[] names,Location loc){
		Expression[] forgets;
		foreach(n;names){
			auto var=new Identifier(n);
			var.loc=loc;
			auto f=new ForgetExp(var,null);
			f.loc=loc;
			forgets~=f;
		}
		auto ce=new CompoundExp(forgets);
		ce.loc=loc;
		return ce;
	}
	auto later=new Id[][](ss.length); // (the variables that later statements define again, whose forgets and moves the classical part keeps, see `recomputation`: those that their parts define or that are available after them, but not those that statements which it leaves out define for themselves, e.g., `v` in `if c { v:=w+1; }`)
	auto skipped=new bool[](ss.length); // (see `projection`)
	Id[] defs=after.dup;
	foreach_reverse(j,s;ss){
		later[j]=defs;
		if(auto fe=cast(ForgetExp)s) if(!fe.val) continue;
		auto changes=changedNames(s);
		auto changesDropped=changes.any!(n=>drop.canFind(n));
		skipped[j]=skip.length&&!changes.length&&definedNames(s).length&&definedNames(s).all!(n=>skip.canFind(n));
		if(!skipped[j]&&(!changesDropped||!changes.all!(n=>drop.canFind(n))||definedNames(s).length)){
			if(classifyStatement(s)==ComputationClass.classical&&!changesDropped){
				if(readsDropped(s)) omitted[j]=true;
				else parts[j]=recomputation(s,sc,vars,later[j]);
			}else if(auto p=projection(s,sc,drop,vars,null,later[j])) parts[j]=p;
			else if(changes.length) omitted[j]=true; // (the values that it changes would not be recomputed)
			if(parts[j]&&withoutEffect(parts[j])) parts[j]=null; // (e.g., `if u==3 { }` for `if u==3 { x[2]:=X(x[2]); }`, which then does not need `u`)
		}
		defs~=chain(parts[j]?definedWithin(parts[j]):null,classicalEscapingNames(s)).array;
	}
	foreach(j,s;ss){
		if(auto fe=cast(ForgetExp)s){ // (also of a variable that a later statement defines again, e.g., `forget(v); v:=2;`)
			Id[] names;
			foreach(v;forgottenVariables(fe)) if(auto id=cast(Identifier)unwrap(v)) if(id.type&&id.type.isClassical()&&(later[j].canFind(nameOf(id))||defined.canFind(nameOf(id)))) names~=nameOf(id);
			if(names.length) parts[j]=forgetting(names,fe.loc);
			defined=defined.filter!(n=>!names.canFind(n)).array;
			continue;
		}
		if(skipped[j]) continue;
		auto consumed=defined.filter!(n=>!availableAfter(s,n)&&(!parts[j]||availableAfter(parts[j],n))).array; // (e.g., `v` for `if c { … } else { w:=move(v); }`, also if the classical part leaves the statement out)
		if(parts[j]){
			defined=defined.filter!(n=>availableAfter(parts[j],n)).array;
			foreach(n;definedNames(parts[j])) if(!defined.canFind(n)&&!readsBeforeDefining(b,n)) defined~=n; // (not a variable of an enclosing block that the block defines again, e.g., `j` for `(xs,j):=let{ j-=1; … } in (xs,j);`, whose version after the classical part the reversal of the block reads)
		}
		if(consumed.length){
			auto f=forgetting(consumed,s.loc);
			if(parts[j]){
				auto ce=new CompoundExp([parts[j],f]);
				ce.loc=s.loc;
				parts[j]=ce;
			}else parts[j]=f;
			defined=defined.filter!(n=>!consumed.canFind(n)).array;
		}
	}
	bool unused(size_t j){ // (local variables that it defines or changes, which no later part reads other than to forget them, e.g., a definition that reads a dropped variable)
		auto names=chain(definedNames(ss[j]),changedNames(ss[j])).array;
		if(!names.length||!names.all!(n=>ss[0..j+1].any!(t=>definedNames(t).canFind(n)))) return false;
		Id[] mentions(Expression e){ Id[] m; walkIdentifiers(e.copy(),(Identifier id){ m~=id.id; }); return m; }
		bool noop(Expression e){ auto fe=cast(ForgetExp)e; return fe&&!fe.val; }
		return !chain(parts[j+1..$].filter!(t=>t&&!noop(t)),only(result).filter!(e=>!!e)).any!(t=>mentions(t).any!(n=>names.canFind(n)));
	}
	foreach(j;0..ss.length) if(omitted[j]&&!unused(j)) return null;
	auto res=new CompoundExp(parts.filter!(p=>!!p).array);
	res.loc=b.loc;
	return res;
}
static if(language==silq)
Expression projection(Expression s,Scope sc,Id[] drop=null,Id[] inner=null,Id[] skip=null,Id[] after=null){ // (the classical part of an `if` statement, a loop, a `with` statement, a `let` expression or a call that is reversed, which the reversal recomputes; without the changes of the variables in `drop`, which it then must not read; `inner`: see `recomputation`)
	if(auto ce=cast(CompoundExp)s) if(ce.loweredFrom) return projection(ce.loweredFrom,sc,drop,inner,skip,after);
	bool readsDropped(Expression e){ return drop.length&&e.subexpressions.any!(x=>cast(Identifier)x&&drop.canFind(nameOf(cast(Identifier)x))); }
	CompoundExp part(CompoundExp b,Expression result=null,Id[] more=null){ return classicalPart(b,sc,drop,inner~more,result,skip,result?null:after); } // (the forgets of variables that later statements define again, e.g., `v` for `with { … } do { forget(v); … }` before `v:=2;` in a branch, see `later`)
	bool carriedLost(CompoundExp b,CompoundExp p){ return definedWithin(b).any!(n=>readsBeforeDefining(b,n,true)&&availableAfter(b,n)&&consumesVariable(p,n)&&!availableAfter(p,n)); } // (the classical part of the body of a loop forgets a version that the body defines again for the next iteration, but leaves out the definition, e.g., `v` for `for i in 0..2 { k+=1; forget(v); v:=i+k; }` without the changes of `k`)
	Expression res;
	if(headers(s).any!readsDropped) return null;
	if(auto ite=cast(IteExp)s){
		if(!ite.cond.type||!ite.cond.type.isClassical()) return null;
		CompoundExp branch(CompoundExp b){ // (it may read the variables in `drop` that only the other branch changes, e.g., `k` for `if c { k+=1; } else { u+=k; }`)
			auto changes=changedNames(b);
			return classicalPart(b,sc,drop.filter!(n=>changes.canFind(n)||usesUp(n,b.s)).array,inner,null,skip,after);
		}
		auto then=branch(ite.then),othw=ite.othw?branch(ite.othw):null;
		if(!then||ite.othw&&!othw) return null;
		res=new IteExp(ite.cond.copy(),then,othw);
	}else if(auto fe=cast(ForExp)s){
		auto bdy=part(fe.bdy);
		if(!bdy||carriedLost(fe.bdy,bdy)) return null;
		res=new ForExp(fe.var?fe.var.copy():null,fe.pattern?fe.pattern.copy():null,fe.aggr.copy(Expression.CopyArgs.init),bdy);
	}else if(auto re=cast(RepeatExp)s){
		auto bdy=part(re.bdy);
		if(!bdy||carriedLost(re.bdy,bdy)) return null;
		res=new RepeatExp(re.num.copy(),bdy);
	}else if(auto we=cast(WithExp)s){ // (the classical parts of the transformation and the body, e.g., `with { } do { k*=2; }` for `with { a:=xs[j]; } do { k*=2; a:=H(a); }`)
		auto changes=changedNames(we.bdy);
		if(changedNames(we).any!(n=>drop.canFind(n)&&!changes.canFind(n))) return null; // (a classical component that the inverse writes back)
		auto more=chain(definedNames(we.trans),definedNames(we.bdy)).array;
		auto trans=part(we.trans,we.bdy,more~writtenBack(we)),bdy=part(we.bdy,null,more);
		if(!trans||!bdy) return null;
		auto r=new WithExp(trans,bdy);
		if(we.isIndices&&trans.s.length){ // (a classical component that it moves out and writes back)
			if(trans.s.length!=transStatements(we).length) return null;
			r.isIndices=true;
			if(we.itrans) r.itrans=we.itrans.copy();
		}
		res=r;
	}else if(auto de=cast(DefineExp)s){ // (the classical results of a `let` expression, e.g., `k:=let { k+=1; } in k` for `(y,k):=let { k+=1; z:=X(x); } in (z,k)`)
		if(auto ce=cast(CallExp)unwrap(de.e2)){ // (or of a call, see `callProjection`)
			res=callProjection(de,ce,sc,drop,inner);
			if(!res) return null;
			res.loc=s.loc;
			return res;
		}
		auto le=cast(LetExp)unwrap(de.e2);
		if(!le) return null;
		Expression[] lhs,rhs;
		void pair(Expression l,Expression r){
			l=unwrap(l), r=unwrap(r);
			auto lt=cast(TupleExp)l,rt=cast(TupleExp)r;
			if(lt&&rt&&lt.length==rt.length){
				foreach(i;0..lt.length) pair(lt.e[i],rt.e[i]);
				return;
			}
			bool classical(Expression e){
				if(!e.type||!e.type.isClassical()) return false;
				foreach(x;e.subexpressions) if(x.type&&!x.type.isClassical()) return false;
				return true;
			}
			if(auto id=cast(Identifier)l) if(id.type&&id.type.isClassical()&&classical(r)){
				lhs~=id.copy();
				rhs~=r.copy();
			}
		}
		pair(de.e1,le.e);
		if(!lhs.length||readsDropped(le.e)) return null;
		auto bdy=part(le.s,le.e);
		if(!bdy) return null;
		Id[] outer,local; // (variables of the enclosing block that the `let` expression changes, other than the results: the recomputation changes copies, as the reversal of the `let` expression copies the versions before it, see `lowerLetDefine`)
		auto results=definedIdentifiers(de).map!nameOf.array;
		foreach(t;mergeCompound(le.s.s)){
			foreach(n;changedNames(t)) if(!local.canFind(n)&&!results.canFind(n)&&!outer.canFind(n)) outer~=n;
			local~=definedNames(t);
		}
		if(outer.length){
			MapSX!(Id,Id) renames;
			Expression[] copies;
			foreach(n;outer){
				renames[n]=freshName();
				auto cid=new Identifier(renames[n]),var=new Identifier(n);
				cid.loc=var.loc=le.loc;
				auto dup=new CallExp(getDup(le.loc,sc),var,false,false);
				dup.loc=le.loc;
				auto cpy=new DefineExp(cid,dup);
				cpy.loc=le.loc;
				copies~=cpy;
			}
			void rename(Identifier id){ if(!id.meaning) if(auto p=renames.getPtr(id.id)) id.id=*p; }
			walkIdentifiers(bdy,&rename,true);
			foreach(r;rhs) walkIdentifiers(r,&rename,true);
			bdy.s=copies~bdy.s;
		}
		Expression tuple(Expression[] es){
			if(es.length==1) return es[0];
			auto tpl=new TupleExp(es);
			tpl.loc=de.loc;
			return tpl;
		}
		auto nle=new LetExp(bdy,tuple(rhs));
		nle.loc=le.loc;
		res=new DefineExp(tuple(lhs),nle);
	}else return null;
	res.loc=s.loc;
	static if(language==silq){
		bool forgetsLater(Expression x){ // (it forgets a variable that later statements define again, e.g., `v` for `with { … } do { forget(v); xs[u]:=X(xs[u]); }` before `v:=2;` in a branch, see `classicalPart`)
			auto fe=cast(ForgetExp)x;
			return fe&&forgottenVariables(fe).any!((v){ auto id=cast(Identifier)unwrap(v); return id&&after.canFind(nameOf(id)); });
		}
		if(after.length&&res.subexpressions.any!forgetsLater) return res;
	}
	return definedNames(res).length||changedNames(s).length?res:null;
}

static if(language==silq){
private size_t[][] classicalPaths(Expression type){ // (the classical components of values of type `type` that are not parts of larger classical components, e.g., `[[1]]` for `𝔹^4 × !ℕ`)
	if(type.isClassical()) return [[]];
	size_t[][] r;
	if(auto tt=type.isTupleTy()) foreach(i;0..tt.length) foreach(p;classicalPaths(tt[i])) r~=[i]~p;
	return r;
}
private Expression atPath(Expression e,size_t[] path){ // (the component of a tuple expression, see `classicalPaths`)
	foreach(i;path){
		auto tpl=cast(TupleExp)unwrap(e);
		if(!tpl||i>=tpl.length) return null;
		e=tpl.e[i];
	}
	return e;
}
private Expression tupleIfMany(Expression[] es,Location loc){ // (not analyzed, unlike `tupleOf`)
	if(es.length==1) return es[0];
	auto tpl=new TupleExp(es);
	tpl.loc=loc;
	return tpl;
}
/// a function that computes the classical components of the result of `fd` (see `classicalPaths`) from its classical parameters, without the quantum computations, e.g., `k+1` for `def g(xs:𝔹^4,const k:!ℕ)mfree{ xs[k]:=H(xs[k]); return (xs,k+1); }`; with it, the reversal of a call recomputes the classical results that the reversed call receives (see `callProjection`); `null` if the classical part of `fd` cannot be separated, e.g., if it reads a quantum parameter or returns early
FunctionDef classicalSlice(FunctionDef fd){
	if(fd.classicalSlice) return fd.classicalSlice is fd?null:fd.classicalSlice;
	fd.classicalSlice=fd;
	auto sc=fd.scope_;
	if(!sc||!fd.isToplevelDeclaration()||fd.isSquare||!fd.ftype||!fd.body_||fd.isSemError()) return null;
	auto handler=sc.handler;
	handler.suppress++; // (the slice may not be valid, e.g., if its body reads a quantum parameter)
	scope(exit) handler.suppress--;
	auto bfd=fd;
	if(astopt.removeLoops&&fd.origBody_&&hasLoop(fd.origBody_)){ // (as for `reverseFunction`)
		auto src=new FunctionDef(null,fd.params.map!(p=>p.copy()).array,fd.isTuple,fd.rret?fd.rret.copy():null,fd.origBody_.copy());
		src.copyIntrinsicFieldsFrom(fd);
		src.keepLoops=true;
		src.loc=fd.loc;
		src.scope_=sc;
		src=cast(FunctionDef)presemantic(src,sc);
		if(src) src=functionDefSemantic(src,sc);
		if(!src||!src.isSemCompleted()&&src.sstate!=SemState.passive) return null;
		bfd=src;
	}
	auto ss=mergeCompound(bfd.body_.s);
	auto ret=ss.length?cast(ReturnExp)ss[$-1]:null;
	if(!ret||ss[0..$-1].any!(s=>!!mayReturn(s))) return null;
	Expression[] results;
	foreach(p;classicalPaths(fd.ftype.cod)){
		auto r=atPath(ret.e,p);
		if(!r) return null;
		results~=r;
	}
	if(!results.length) return null;
	Parameter[] params;
	foreach(p;bfd.params) if(p.vtype&&p.vtype.isClassical()){
		if(!p.dtype) return null;
		auto np=new Parameter(p.isConst,p.name.copy(),p.dtype.copy());
		np.loc=p.loc;
		params~=np;
	}
	auto name=new Identifier(freshName());
	name.loc=fd.name?fd.name.loc:fd.loc;
	auto body_=new CompoundExp([]);
	body_.loc=bfd.body_.loc;
	auto slice=new FunctionDef(name,params,params.length!=1,null,body_);
	slice.annotation=pure_;
	slice.inferAnnotation=true;
	slice.keepLoops=true; // (as `bfd`)
	slice.loc=fd.loc;
	fd.classicalSlice=slice; // (for recursive calls)
	auto part=classicalPart(bfd.body_,bfd.fscope_,[],[],tupleIfMany(results,ret.e.loc));
	if(!part){ fd.classicalSlice=fd; return null; }
	auto nret=new ReturnExp(tupleIfMany(results.map!(r=>recomputation(r,bfd.fscope_)).array,ret.e.loc));
	nret.loc=ret.loc;
	body_.s=part.s~[cast(Expression)nret];
	slice=cast(FunctionDef)presemantic(slice,sc);
	if(slice) slice=functionDefSemantic(slice,sc);
	if(!slice||!slice.isSemCompleted()&&slice.sstate!=SemState.passive){ fd.classicalSlice=fd; return null; }
	return slice;
}
private Expression callProjection(DefineExp de,CallExp ce,Scope sc,Id[] drop,Id[] inner){ // (the classical results of a call, which the classical slice of the function recomputes, e.g., `c:=s(j)` for `(xs,c):=g(xs,j)`, see `classicalSlice`)
	auto id=cast(Identifier)unwrap(ce.e);
	auto fd=id?cast(FunctionDef)id.meaning:null;
	if(!fd||ce.isSquare||!ce.type||ce.type.isClassical()) return null;
	auto slice=classicalSlice(fd);
	if(!slice) return null;
	Id[] results;
	bool pattern(Expression e){
		e=unwrap(e);
		if(auto tpl=cast(TupleExp)e) return tpl.e.all!pattern;
		auto id=cast(Identifier)e;
		if(id) results~=nameOf(id);
		return !!id;
	}
	Expression[] lhs;
	foreach(p;classicalPaths(fd.ftype.cod)){
		auto l=atPath(de.e1,p);
		if(!l||!pattern(l)) return null;
		lhs~=l.copy();
	}
	Expression[] args;
	auto tpl=cast(TupleExp)ce.arg;
	foreach(i,p;fd.params){
		if(!p.vtype||!p.vtype.isClassical()) continue;
		auto a=!fd.isTuple?ce.arg:tpl&&tpl.length==fd.params.length?tpl.e[i]:null;
		if(!a||a.subexpressions.any!(x=>x.type&&!x.type.isClassical())) return null; // (the reversal does not see the quantum values before the call, e.g., `xs.length`)
		if(a.subexpressions.any!(x=>cast(Identifier)x&&(drop.canFind(nameOf(cast(Identifier)x))||results.canFind(nameOf(cast(Identifier)x))))) return null; // (e.g., a result that redefines a classical argument that the call consumes, whose reversal is not supported)
		args~=recomputation(a,sc,inner);
	}
	auto fid=new Identifier(slice.name.id);
	fid.loc=ce.e.loc;
	auto call=new CallExp(fid,tupleIfMany(args,ce.arg.loc),false,false);
	call.loc=ce.loc;
	return new DefineExp(tupleIfMany(lhs,de.e1.loc),call);
}
}

static if(language==silq)
bool hasExactInverse(ABinaryExp be){ // (classical updates that the reversal of a function reverts in place, e.g., `t+=c` or `t*=2`, but neither `t*=c`, which loses the value for `c=0`, nor updates of floating-point numbers)
	auto num=isNumericTy(be.e1.type);
	if(num==NumericType.ℝ||num==NumericType.ℂ) return false;
	if(auto id=cast(Identifier)unwrap(be.e1)) if(be.e2.subexpressions.any!(x=>cast(Identifier)x&&nameOf(cast(Identifier)x)==nameOf(id))) return false; // (the inverse would read the version after the update, e.g., `t+=h(t)`)
	if(cast(AddAssignExp)be||cast(SubAssignExp)be||cast(BitXorAssignExp)be||cast(XorAssignExp)be) return true;
	if(!cast(MulAssignExp)be&&!cast(DivAssignExp)be||num!=NumericType.ℕt&&num!=NumericType.ℤt&&num!=NumericType.ℚt) return false; // (e.g., `t*=2` loses the highest bit of `t:!uint[4]`)
	auto val=be.e2.asIntegerConstant(true);
	return val&&val.get()!=0;
}

struct NeedOld{ // (the variables of enclosing blocks whose versions before a statement its reversal would need, e.g., for `u:=dup(k); k+=u;` or for a conditional that changes a variable of its condition: an enclosing block may provide copies of them, see `reversal` in `reverseStatements`)
	Id[] vars;
	Q!(Id[],Location,string)[] errors; // (deferred errors, e.g., of reversals of `if` statements and loops that change a variable of their condition or range)
}

static if(language==silq){
private Expression narrowing(Id n,Expression ty,Location loc){ // (`n=n coerce ty`: the reversals of earlier statements expect the type before a statement whose merge widens it, e.g., `!ℕ` for `j` in `if c { j-=1; }`)
	auto lhs=new Identifier(n),var=new Identifier(n);
	lhs.loc=var.loc=loc;
	auto cv=new TypeAnnotationExp(var,ty.copy(),TypeAnnotationType.coercion);
	cv.loc=loc;
	auto r=new AssignExp(lhs,cv);
	r.loc=loc;
	return r;
}
private bool closed(Expression ty){ foreach(id;freeIdentifiers(ty)) return false; return true; }
private Declaration mergedVersion(CompoundExp[] blocks,Id n){ // (the version after an `if` statement or a loop, which merges those of the branches or iterations)
	foreach(b;blocks) if(b&&b.blscope_){
		foreach(d;b.blscope_.splitVars) if(d.getId==n&&d.mergedInto) return d.mergedInto;
		foreach(d;b.blscope_.mergedVars) if(d.getId==n&&d.mergedInto) return d.mergedInto;
	}
	return null;
}
private Expression typeBefore(CompoundExp[] blocks,Id n){ // (of the version before an `if` statement or a loop, which the branches or iterations split)
	foreach(b;blocks) if(b&&b.blscope_) foreach(d;b.blscope_.splitVars) if(d.getId==n&&d.splitFrom) return typeForDecl(d.splitFrom);
	return null;
}
Expression[] branchNarrowings(IteExp ite,CompoundExp b,Id[] names,Id[] given){ // (to the types of the versions that a branch merges, at the start of its reversal)
	Expression[] r;
	Expression forgottenType(CompoundExp c,Id n){ // (of the version that a branch forgets at its end)
		if(!c) return null;
		foreach_reverse(s;c.s) if(auto fe=cast(ForgetExp)s){
			if(fe.val) continue;
			foreach(v;forgottenVariables(fe)) if(auto id=cast(Identifier)unwrap(v)) if(nameOf(id)==n) return id.type;
		}else break;
		return null;
	}
	if(b.blscope_) foreach(n;names){
		auto m=mergedVersion([ite.then,ite.othw],n);
		if(!m){ // (both branches forget it, but the reversal receives the version after the classical part of the statement, which merges them, see `projected`, e.g., `j` for `if j==0 { j+=1; xs[j]:=H(xs[j]); } else { j-=2; }` at the last use of `j`)
			if(!given.canFind(n)) continue;
			auto ty=forgottenType(b,n),other=forgottenType(b is ite.then?ite.othw:ite.then,n);
			if(!other&&!(b is ite.then?ite.othw:ite.then)) other=typeBefore([ite.then,ite.othw],n);
			if(!ty||!other) continue;
			auto merged=joinTypes(ty,other);
			if(merged&&closed(ty)&&ty!=merged) r~=narrowing(n,ty,b.loc);
			continue;
		}
		auto from=m.mergedFrom.find!(d=>d.scope_&&d.scope_.isNestedIn(b.blscope_));
		auto ty=from.empty?typeBefore([ite.then,ite.othw],n):typeForDecl(from.front),merged=typeForDecl(m);
		if(ty&&merged&&closed(ty)&&ty!=merged) r~=narrowing(n,ty,b.loc);
	}
	return r;
}
Expression[] statementNarrowings(Expression s,Id[] names){ // (to the types before a loop or an `if` statement without `else`, after its reversal)
	if(auto ce=cast(CompoundExp)s) if(ce.loweredFrom) s=ce.loweredFrom;
	CompoundExp b;
	if(auto ite=cast(IteExp)s){ if(!ite.othw) b=ite.then; }
	else if(auto fe=cast(ForExp)s) b=fe.bdy;
	else if(auto re=cast(RepeatExp)s) b=re.bdy;
	Expression[] r;
	if(b) foreach(n;names){
		auto before=typeBefore([b],n),m=mergedVersion([b],n);
		auto after=m?typeForDecl(m):null;
		if(before&&after&&closed(before)&&before!=after) r~=narrowing(n,before,s.loc);
	}
	return r;
}
}

static if(language==silq)
bool readsOld(Expression s){ // (statements whose reversals can read copies of the versions of variables before them, see `NeedOld`)
	if(auto ce=cast(CompoundExp)s) if(ce.loweredFrom) return readsOld(ce.loweredFrom);
	if(cast(IteExp)s||cast(RepeatExp)s) return true;
	if(auto fe=cast(ForExp)s) return !!fe.aggr.isRange();
	auto de=cast(DefineExp)s;
	return de&&cast(LetExp)unwrap(de.e2);
}

static if(language==silq){
Identifier[] identifiersOf(Declaration[] decls,Location loc){ // (of the quantum variables in `decls`, e.g., that a block forgets at its end)
	Identifier[] r;
	foreach(d;decls){
		if(!d.isLinear()||!d.name) continue;
		auto id=new Identifier(d.name.id);
		id.loc=loc;
		id.meaning=d;
		id.type=typeForDecl(d);
		if(!id.type) continue;
		id.constLookup=false;
		id.setSemCompleted();
		r~=id;
	}
	return r;
}
ForgetExp makeForget(Expression var,Expression val,Location loc){
	auto fe=new ForgetExp(var,val);
	fe.loc=loc;
	fe.type=unit;
	fe.setSemCompleted();
	return fe;
}
Expression[] forgottenVariables(ForgetExp fe){
	if(auto tpl=cast(TupleExp)unwrap(fe.var)) return tpl.e;
	return [fe.var];
}
Expression[] uncomputed(Expression s){ // (with explicit forgets for the quantum variables that a forget without value forgets, see `resolveForgets`)
	if(auto fe=cast(ForgetExp)s) if(fe.uncomputation.length){
		if(!fe.outerUncomputation.length) return fe.uncomputation;
		auto recomputed=recomputedBefore(fe); // (recomputed before the enclosing statement)
		Expression[] r;
		foreach(u;fe.uncomputation){
			auto ufe=cast(ForgetExp)u;
			auto vars=forgottenVariables(ufe).filter!(v=>!(cast(Identifier)unwrap(v)&&recomputed.canFind(nameOf(cast(Identifier)unwrap(v))))).array;
			if(vars.length) r~=vars.length<forgottenVariables(ufe).length?makeForget(tupleOf(vars,ufe.loc),ufe.val,ufe.loc):ufe;
		}
		if(!r.length) r=[makeForget(tupleOf([],fe.loc),null,fe.loc)]; // (of nothing, which the reversal ignores)
		return r;
	}
	Expression[] after; // (forgets after the statement, which the reversal recomputes before the reversed statement)
	if(auto we=cast(WithExp)s) after~=we.uncomputation; // (the reversal of the statement derives the inverse of the transformation again)
	if(auto ite=cast(IteExp)s) after~=ite.uncomputation;
	foreach(fe;embeddedForgets(s)) if(fe.outerUncomputation.length&&fe.outerStatement is s){ after~=fe.outerUncomputation; break; }
	return [s]~after;
}
private Id[] recomputedBefore(ForgetExp fe){ // (the variables that a forget within a part of a statement that the reversal evaluates again forgets and that the reversal recomputes before the statement, see `embeddedForgets`, or before an enclosing conditional)
	Id[] r;
	foreach(u;fe.outerUncomputation) foreach(v;forgottenVariables(cast(ForgetExp)u)) if(auto id=cast(Identifier)unwrap(v)) r~=nameOf(id);
	return r~fe.outerHoisted;
}
private void reevaluatedParts(Expression e,ref Expression[] parts){ // (of the right-hand side of a definition: the parts that its reversal evaluates again, e.g., the `const` arguments of a reversed call, see `lowerDefine`)
	e=unwrap(e);
	if(cast(Identifier)e||cast(LiteralExp)e) return;
	if(auto tpl=cast(TupleExp)e){ foreach(x;tpl.e) reevaluatedParts(x,parts); return; }
	if(auto vec=cast(VectorExp)e){ foreach(x;vec.e) reevaluatedParts(x,parts); return; }
	if(auto le=cast(LetExp)e){ // (its statements are reversed as statements, see `lowerLetDefine`)
		if(auto fwd=le.isForward(true)) reevaluatedParts(fwd,parts);
		else reevaluatedParts(le.e,parts);
		return;
	}
	if(auto ite=cast(IteExp)e){
		parts~=ite.cond;
		foreach(b;[ite.then,ite.othw]) if(b&&b.s.length==1) reevaluatedParts(b.s[0],parts);
		return;
	}
	if(auto ce=cast(CallExp)e){
		if(auto prim=isPrimitiveCall(ce)){
			if(util.among(prim,"H","X","Y","Z")) reevaluatedParts(ce.arg,parts);
			else parts~=ce.arg;
			return;
		}
		if(auto ft=cast(FunTy)ce.e.type) if(!ft.isSquare&&ft.isConstForReverse.length){
			auto tpl=cast(TupleExp)unwrap(ce.arg);
			if(tpl&&tpl.length==ft.isConstForReverse.length){
				foreach(i,a;tpl.e){
					if(ft.isConstForReverse[i]) parts~=a;
					else reevaluatedParts(a,parts);
				}
				return;
			}
			if(ft.isConstForReverse.all) parts~=ce.arg;
			else if(!ft.isConstForReverse.any) reevaluatedParts(ce.arg,parts);
			else parts~=ce.arg;
			return;
		}
	}
	parts~=e; // (e.g., `a⊕b`, which the reversal forgets with that value)
}
static if(language==silq)
LetExp blockUpdate(Expression e){ // (the `let` expression on the right-hand side of an update whose reversal reverses its block around the update, as for a definition, see `lowerLetDefine`: the evaluation of a copy would read variables that the update consumes, e.g., `t` in `y⊕=(let{ a:=t; } in a⊕x);`)
	if(!cast(BitXorAssignExp)e&&!cast(XorAssignExp)e) return null;
	auto le=cast(LetExp)unwrap((cast(ABinaryExp)e).e2);
	if(!le||le.isForward(true)||!le.s.isSemCompleted()) return null;
	bool consumes=false;
	le.freeVarsImpl((Identifier id){ if(id.moved||!id.constLookup&&!id.implicitDup&&id.type&&!id.type.isClassical()) consumes=true; return 0; });
	return consumes?le:null;
}
ForgetExp[] embeddedForgets(Expression s){ // (the forgets without value within the parts of a statement that its reversal evaluates again, e.g., in a `let` expression on the right-hand side of `x⊕=…`: for the variables of enclosing blocks that they forget, the reversal evaluates the parts without forgetting them, see `reevaluationCopy`, and recomputes them before)
	Expression[] parts;
	if(auto be=isOpAssignExp(s)){
		LetExp le=null;
		static if(language==silq) le=blockUpdate(s);
		if(le){ parts=[be.e1]; reevaluatedParts(le,parts); } // (the reversal of its block recomputes the forgets of the block, see `lowerLetDefine`)
		else parts=[be.e1,be.e2];
	}
	else if(auto ae=cast(AssertExp)s) parts=[ae.e];
	else if(auto fe=cast(ForgetExp)s){ if(fe.val) parts=[fe.val]; }
	else if(auto ite=cast(IteExp)s) parts=[ite.cond];
	else if(auto de=cast(DefineExp)s){ if(!de.isSwap) reevaluatedParts(de.e2,parts); }
	ForgetExp[] r;
	foreach(p;parts) foreach(x;p.subexpressions) if(auto fe=cast(ForgetExp)x) if(!fe.val) r~=fe;
	return r;
}
Expression reevaluationCopy(Expression e,Expression delegate(Expression) replacement=null,Id[] kept=null){ // (of a part of a statement that the reversal evaluates again, without the forgets of the variables that it recomputes before the statement, see `embeddedForgets`, and of `kept`; `replacement`: of subexpressions)
	Expression.CopyArgs cargs;
	cargs.mapExp=(Expression x,ref Expression.CopyArgs args){
		if(replacement) if(auto r=replacement(x)) return r;
		auto fe=cast(ForgetExp)x;
		if(!fe||fe.val) return null;
		auto recomputed=(fe.outerUncomputation.length?recomputedBefore(fe):[])~kept;
		bool isRecomputed(Expression v){ return cast(Identifier)unwrap(v)&&recomputed.canFind(nameOf(cast(Identifier)unwrap(v))); }
		if(!fe.outerUncomputation.length&&!forgottenVariables(fe).any!isRecomputed) return null;
		auto vars=forgottenVariables(fe).filter!(v=>!isRecomputed(v)).map!(v=>v.copy(args)).array;
		Expression var;
		if(vars.length==1) var=vars[0];
		else{
			var=new TupleExp(vars); // (of nothing if none remains)
			var.loc=fe.var.loc;
		}
		auto r=new ForgetExp(var,null);
		r.loc=fe.loc;
		r.erpId=fe.erpId;
		return cast(Expression)r;
	};
	return e.copy(cargs);
}
static if(language==silq)
LetExp continuedLet(LetExp le){ // (a forward `let` expression with statements as the result, also with type annotations, whose statements continue those of `le`, see `lowerLetDefine`)
	auto inner=le.e;
	for(auto tae=cast(TypeAnnotationExp)inner;tae;tae=cast(TypeAnnotationExp)inner) inner=tae.e;
	auto fle=cast(LetExp)inner;
	return fle&&fle.isForward(true)&&fle.s.s.length>1?fle:null;
}
static if(language==silq)
Identifier[] resultForgets(LetExp le){ // (the quantum variables of the block of a `let` expression that the part of its result that the reversal of an update evaluates again forgets, e.g., at their last uses, and does not change otherwise, e.g., `a` for `y⊕=(let{ a:=t; } in (let{ b:=dup(a); } in b))`: the reversal recomputes them before the update, see `lowerLetDefine`)
	auto cle=continuedLet(le);
	Id[] local,changed;
	foreach(s;chain(le.s.s,cle?cle.s.s:[])) local~=definedNames(s);
	Identifier[] r;
	void add(Identifier id){ if(id.type&&!id.type.isClassical()&&local.canFind(nameOf(id))&&!r.any!(o=>nameOf(o)==nameOf(id))) r~=id; }
	foreach(x;(cle?cle.e:le.e).subexpressions){
		if(auto fe=cast(ForgetExp)x){ if(!fe.val) foreach(v;forgottenVariables(fe)) if(auto id=cast(Identifier)unwrap(v)) add(id); }
		else if(auto ce=cast(CompoundExp)x){ if(ce.blscope_) foreach(id;identifiersOf(ce.blscope_.forgottenVarsOnEntry~ce.blscope_.forgottenVars,ce.loc)) add(id); }
		else if(cast(DefineExp)x) changed~=definedNames(x);
		else if(auto be=isOpAssignExp(x)) if(auto id=cast(Identifier)unwrap(be.e1)) changed~=nameOf(id);
	}
	return r.filter!(id=>!changed.canFind(nameOf(id))).array;
}
Identifier[] outerForgets(WithExp we){ // (the quantum variables of enclosing blocks that the inverse of the transformation forgets, e.g., at their last uses, also in nested blocks)
	if(!we.itrans) return [];
	Id[] local;
	foreach(b;[we.trans,we.itrans]) foreach(x;b.subexpressions) if(cast(DefineExp)x) local~=definedNames(x);
	Identifier[] r;
	void add(Identifier id){ if(id.type&&!id.type.isClassical()&&!local.canFind(nameOf(id))&&!r.any!(o=>nameOf(o)==nameOf(id))) r~=id; }
	foreach(x;we.itrans.subexpressions){
		if(auto fe=cast(ForgetExp)x){ if(!fe.val) foreach(v;forgottenVariables(fe)) if(auto id=cast(Identifier)unwrap(v)) add(id); }
		else if(auto ce=cast(CompoundExp)x) if(ce.blscope_) foreach(id;identifiersOf(ce.blscope_.forgottenVarsOnEntry~ce.blscope_.forgottenVars,ce.loc)) add(id);
	}
	return r;
}
Expression[] uncomputationOf(Expression[] uncomputation,Declaration[] decls,Location loc){ // (`uncomputation`, unless the block was not resolved: then, a forget that the reversal rejects)
	if(uncomputation.length) return uncomputation;
	auto ids=identifiersOf(decls,loc);
	if(!ids.length) return [];
	return [makeForget(tupleOf(cast(Expression[])ids,loc),null,loc)];
}
Expression tupleOf(Expression[] es,Location loc){
	if(es.length==1) return es[0];
	auto tpl=new TupleExp(es);
	tpl.loc=loc;
	if(es.all!(e=>!!e.type)){
		tpl.type=tupleTy(es.map!(e=>e.type).array);
		tpl.setSemCompleted();
	}else tpl.setSemForceError();
	return tpl;
}

private Expression[] flatten(Expression[] s){ // (as `mergeCompound`, without changing nested blocks)
	Expression[] r;
	foreach(e;s){
		if(auto ce=cast(CompoundExp)e) if(!ce.blscope_&&!ce.loweredFrom){ r~=flatten(ce.s); continue; }
		if(auto ce=cast(CommaExp)e){ r~=flatten([ce.e1,ce.e2]); continue; }
		r~=e;
	}
	return r;
}
private Expression[] components(Expression[] s){ // (with the definitions of the components of tuple definitions, for the slices, see `componentDefinitions`)
	Expression[] r;
	foreach(e;s){
		if(auto de=cast(DefineExp)e) if(auto components=componentDefinitions(de)){ r~=components; continue; }
		r~=e;
	}
	return r;
}
private Expression[] componentDefinitions(DefineExp de){ // (of a definition of variables by a tuple of values that do not mention them, e.g., `t₂:=y` in `(t₁,t₂):=(x⊕1,y)`, whose recomputation does not need `x`; otherwise `null`)
	if(de.isSwap||!de.isSemCompleted()) return null;
	auto lt=cast(TupleExp)unwrap(de.e1),rt=cast(TupleExp)unwrap(de.e2);
	if(!lt||!rt||lt.length!=rt.length||lt.length<2) return null;
	auto ids=lt.e.map!(x=>cast(Identifier)unwrap(x)).array;
	if(ids.any!(id=>!id||!id.meaning)) return null;
	foreach(x;rt.e) if(ids.any!(id=>mentions(x,nameOf(id)))) return null;
	Expression[] r;
	foreach(i;0..lt.length){
		auto c=new DefineExp(lt.e[i],rt.e[i]);
		c.loc=de.loc;
		c.type=unit;
		c.setSemCompleted();
		r~=c;
	}
	return r;
}
private struct ForgetFrame{ // (statements that precede a forget in the function whose reversal recomputes its variables, see `resolveForgets`)
	Expression[] statements; // (in the block of the forget, or before the statement that contains that block)
	ForgetFrame* parent;
	Expression loop; // (whose body the block is: also its earlier iterations precede the forget)
	Expression[] earlier; // (the parts of the statement before the part of the forget: their changes are between the statements and the forget, e.g., the forget of `f` in `f(c)` for the forget of `h` in `(t,u):=(f(c),h(c));` after `def h(const z:𝔹)qfree⇒z&f(c);`)
}
private struct Slice{ // (of the statements before a forget, which recompute the value of a variable, see `ForgetResolution.value`)
	Id[] needed; // (variables whose versions after the current statement the recomputation needs)
	Id[] changed; // (variables that change between the current statement and the forget)
	Expression[] replay; // (the statements that the recomputation evaluates again, on copies of the variables that they write, last first)
}
private struct StatementNames{
	Id[] reads; // (of the versions of variables before the statement)
	Id[] defines; // (for later statements)
	Id[] writes; // (the variables whose versions it changes: that it defines, updates, consumes or forgets)
}
private bool mentions(Expression e,Id name){
	bool r=false;
	walkIdentifiers(e,(Identifier id){ if(nameOf(id)==name) r=true; });
	return r;
}
private struct ForgetResolution{ // (the reversal of a function recomputes the quantum variables that it forgets with values that it computes from the variables that are available there, see `ForgetExp.uncomputation`)
	StatementNames[void*] cache;
	StatementNames names(Expression s){
		if(auto r=cast(void*)s in cache) return *r;
		StatementNames r;
		void add(ref Id[] a,Id n){ if(n!=Id()&&!a.canFind(n)) a~=n; }
		if(auto fd=cast(FunctionDef)s){ // (a local function, whose value has copies of the values that it captures)
			if(fd.name) r.defines=r.writes=[fd.name.id];
			foreach(d;fd.capturedDecls) if(d.name&&!d.isToplevelDeclaration()) add(r.reads,d.name.id);
			return cache[cast(void*)s]=r;
		}
		auto local=declaredWithin(s);
		bool isLocal(Declaration d){ return isVersionOf(d,local); }
		void base(Expression e){
			e=unwrap(e);
			while(auto idx=cast(IndexExp)e) e=unwrap(idx.e);
			if(auto id=cast(Identifier)e) if(!id.meaning||!isLocal(id.meaning)) add(r.writes,nameOf(id));
		}
		void lhs(Expression e){ // (components of the left-hand side of a definition, e.g., of a swap `(a[0],a[1]):=(a[1],a[0])`)
			e=unwrap(e);
			if(auto tpl=cast(TupleExp)e) foreach(y;tpl.e) lhs(y);
			else if(auto vec=cast(VectorExp)e) foreach(y;vec.e) lhs(y);
			else if(auto ce=cast(CatExp)e){ lhs(ce.e1); lhs(ce.e2); }
			else if(cast(IndexExp)e) base(e);
		}
		foreach(x;s.subexpressions){
			if(auto id=cast(Identifier)x){
				if(!id.meaning||id.meaning.isToplevelDeclaration()||isLocal(id.meaning)) continue;
				add(r.reads,nameOf(id));
				if(!id.constLookup&&!id.implicitDup||id.byRef) add(r.writes,nameOf(id));
			}else if(auto de=cast(DefineExp)x) lhs(de.e1);
			else if(auto ae=isOpAssignExp(x)) base(ae.e1);
			else if(auto ce=cast(CompoundExp)x){
				if(ce.blscope_) foreach(d;chain(ce.blscope_.forgottenVarsOnEntry,ce.blscope_.forgottenVars)) if(d.name&&!isLocal(d)) add(r.writes,d.name.id);
			}else if(auto we=cast(WithExp)x) foreach(id;outerForgets(we)) if(!id.meaning||!isLocal(id.meaning)) add(r.writes,nameOf(id));
		}
		r.defines=definedNames(s);
		foreach(n;r.defines) add(r.writes,n);
		return cache[cast(void*)s]=r;
	}
	static bool replayable(Expression s){ // (whether the recomputation can evaluate a statement again, on copies of the variables that it writes)
		if(auto fd=cast(FunctionDef)s) return fd.name&&fd.ftype&&fd.ftype.captureAnnotation<=CaptureAnnotation.const_;
		if(!hasOnlyQfreeCalls(s)) return false;
		foreach(x;s.subexpressions) if(cast(ReturnExp)x||cast(FunctionDef)x||cast(DoWhileExp)x) return false;
		return true;
	}
	MapSX!(Id,Id) current; // (during `value`: the copies of the needed versions of variables that the recomputation defines)
	Id[] keep; // (during `value`: variables whose copies an enclosing `if` statement or loop still needs)
	Id[] bound; // (during `value`: the variables of the enclosing loops that the recomputation evaluates again)
	Expression renamedCopy(Expression e,Id[] renamed){
		MapSX!(Id,Id) renames;
		foreach(m;renamed){
			if(m !in current) current[m]=freshName();
			renames[m]=current[m];
		}
		auto c=e.copy();
		walkIdentifiers(c,(Identifier id){ if(auto p=renames.getPtr(id.id)) id.id=*p; },true);
		return c;
	}
	void add(ref Id[] a,Id[] names){ foreach(n;names) if(!a.canFind(n)) a~=n; }
	bool sliceStatements(Expression[] ss,ref Slice sl){ // (adds the statements that write the needed variables to the recomputation, last first; `false` if it cannot evaluate one of them again)
		foreach_reverse(s;ss) if(!sliceStatement(s,sl)) return false;
		return true;
	}
	bool sliceStatement(Expression s,ref Slice sl){
		auto n=names(s);
		if(n.writes.any!(w=>sl.needed.canFind(w))){
			bool failed=false;
			if(auto p=project(s,sl,failed)) sl.replay~=p;
			else if(failed||!replayable(s)) return false;
			else{
				auto renamed=n.defines~n.reads.filter!(m=>(n.writes.canFind(m)||sl.changed.canFind(m))&&!n.defines.canFind(m)&&!bound.canFind(m)).array;
				if(auto fd=cast(FunctionDef)s){
					auto id=new Identifier(fd.name.id);
					id.loc=fd.name.loc;
					auto de=new DefineExp(id,functionValue(fd));
					de.loc=fd.loc;
					sl.replay~=renamedCopy(de,renamed);
				}else sl.replay~=renamedCopy(s,renamed);
				auto fresh=n.defines.filter!(m=>!n.reads.canFind(m)).array;
				foreach(m;fresh) if(!keep.canFind(m)) current.remove(m);
				sl.needed=sl.needed.filter!(m=>!fresh.canFind(m)).array;
				add(sl.needed,renamed.filter!(m=>!fresh.canFind(m)).array);
			}
		}
		add(sl.changed,n.writes.filter!(w=>!bound.canFind(w)).array);
		return true;
	}
	Id[] headerNames(Expression[] headers,Id[] changed){ // (the variables that the condition of an `if` statement or the bounds of a loop read and that change after them)
		Id[] r;
		foreach(h;headers) foreach(x;h.subexpressions) if(auto id=cast(Identifier)x) if(id.meaning&&!id.meaning.isToplevelDeclaration()&&changed.canFind(nameOf(id))) add(r,[nameOf(id)]);
		return r;
	}
	Expression project(Expression s,ref Slice sl,ref bool failed){ // (the parts of an `if` statement or a loop that write the needed variables, or `null` for other statements)
		CompoundExp body_(Expression[] replay,Location loc){
			auto r=new CompoundExp(replay.retro.array);
			r.loc=loc;
			return r;
		}
		auto changed=chain(sl.changed,names(s).writes).array; // (also by the statement, e.g., in the other branch or in later iterations)
		auto outer=keep;
		scope(exit) keep=outer;
		if(auto ite=cast(IteExp)s){
			keep=chain(outer,sl.needed).array; // (the variables that are needed after it keep their copies in both branches)
			Id[] before;
			CompoundExp[2] branches;
			foreach(i,b;[ite.then,ite.othw]){
				if(!b){ add(before,sl.needed); continue; }
				auto bs=Slice(sl.needed.dup,chain(sl.changed,forgottenNames(b)).array,null);
				if(!sliceStatements(components(flatten(b.s)),bs)){ failed=true; return null; }
				add(before,bs.needed);
				branches[i]=body_(bs.replay,b.loc);
			}
			keep=outer;
			foreach(m;sl.needed) if(!before.canFind(m)&&!keep.canFind(m)) current.remove(m); // (defined in both branches)
			auto cond=headerNames([ite.cond],changed);
			auto res=new IteExp(renamedCopy(ite.cond,cond),branches[0],branches[1]);
			res.loc=ite.loc;
			sl.needed=before;
			add(sl.needed,cond);
			return res;
		}
		CompoundExp bdy;
		auto outerBound=bound;
		scope(exit) bound=outerBound;
		if(auto fe=cast(ForExp)s){
			bdy=fe.bdy;
			if(fe.var) bound=chain(outerBound,only(nameOf(fe.var))).array;
		}else if(auto re=cast(RepeatExp)s) bdy=re.bdy;
		else return null;
		auto carried=sl.needed.dup; // (the variables that the recomputation needs at the end of each iteration)
		for(;;){ // (until the ones that it needs at the start of an iteration are among them)
			auto saved=current.dup;
			keep=chain(outer,carried).array;
			auto bs=Slice(carried.dup,changed.dup,null);
			auto ok=sliceStatements(components(flatten(bdy.s)),bs);
			current=saved;
			if(!ok){ failed=true; return null; }
			if(bs.needed.all!(m=>carried.canFind(m))) break;
			add(carried,bs.needed);
		}
		auto bs=Slice(carried.dup,changed.dup,null);
		sliceStatements(components(flatten(bdy.s)),bs);
		keep=outer;
		auto nbdy=body_(bs.replay,bdy.loc);
		Expression res;
		Id[] header;
		if(auto fe=cast(ForExp)s){
			header=headerNames(headers(fe),changed);
			auto aggr=fe.aggr.copy(Expression.CopyArgs.init);
			auto r=new ForExp(fe.var?fe.var.copy():null,fe.pattern?fe.pattern.copy():null,aggr,nbdy);
			MapSX!(Id,Id) renames;
			foreach(m;header){
				if(m !in current) current[m]=freshName();
				renames[m]=current[m];
			}
			walkIdentifiers(r,(Identifier id){ if(auto p=renames.getPtr(id.id)) id.id=*p; },true,nbdy);
			res=r;
		}else if(auto re=cast(RepeatExp)s){
			header=headerNames([re.num],changed);
			res=new RepeatExp(renamedCopy(re.num,header),nbdy);
		}
		res.loc=s.loc;
		sl.needed=carried;
		add(sl.needed,header);
		return res;
	}
	Expression value(Identifier var,ForgetFrame* frame,Id[] changed){ // (of `var` at the forget, from the variables that are available there, or `null`; `changed`: variables that change between the statements of `frame` and the forget)
		auto name=nameOf(var);
		current.clear();
		keep=[];
		bound=[];
		auto result=freshName();
		current[name]=result;
		auto sl=Slice([name],changed.dup,null);
		for(auto f=frame;f;f=f.parent){
			foreach_reverse(i,s;f.statements){
				if(!sliceStatement(s,sl)) return null;
				if(sl.needed.length) continue;
				if(sl.replay.length==1&&names(s).reads.all!(m=>!sl.changed.canFind(m)||m==name)) if(auto fd=cast(FunctionDef)s) return functionValue(fd); // (a local function whose captures are available)
				if(sl.replay.length==1) if(auto de=cast(DefineExp)s) if(!de.isSwap&&cast(Identifier)unwrap(de.e1)&&de.e2.type&&names(s).reads.all!(m=>!sl.changed.canFind(m)||m==name)){ // (its definition, which only reads variables that are available)
					Expression direct=de.e2;
					if(auto ce=cast(CallExp)direct) if(!ce.isSquare){ // (e.g., `forget(t=x)` for `t:=dup(x)`)
						Expression fun=ce.e;
						if(auto sq=cast(CallExp)fun) if(sq.isSquare) fun=sq.e;
						if(auto id=cast(Identifier)fun) if(isPreludeSymbol(id)=="dup") direct=ce.arg;
					}
					return direct;
				}
				auto bdy=new CompoundExp(sl.replay.retro.array);
				bdy.loc=var.loc;
				auto res=new Identifier(result);
				res.loc=var.loc;
				auto le=new LetExp(bdy,res);
				le.loc=var.loc;
				le.type=var.type;
				le.analyzed=true;
				return le;
			}
			if(f.loop){ // (the earlier iterations change the variables that the loop writes)
				auto n=names(f.loop);
				if(n.writes.any!(w=>sl.needed.canFind(w))) return null;
				add(sl.changed,n.writes);
			}
			foreach(p;f.earlier){
				auto writes=names(p).writes;
				if(writes.any!(w=>sl.needed.canFind(w))) return null;
				add(sl.changed,writes);
			}
		}
		return null; // (e.g., a version of a parameter that the function consumes)
	}
	Expression[] site(Expression[] vars,ForgetFrame* frame,Id[] changed,Location loc){ // (the explicit forgets of the quantum variables, dependent ones first, and a forget of the others)
		Identifier[] quantum;
		Expression[] rest;
		foreach(v;vars){
			auto id=cast(Identifier)unwrap(v);
			if(id&&id.meaning&&id.type&&!id.type.isClassical()) quantum~=id;
			else rest~=v;
		}
		Expression[] r;
		auto gone=changed.dup;
		while(quantum.length){
			auto values=quantum.map!(v=>value(v,frame,gone)).array;
			size_t k=0;
			foreach(i;0..quantum.length) if(!iota(quantum.length).any!(j=>j!=i&&values[j]&&mentions(values[j],nameOf(quantum[i])))){ k=i; break; }
			if(values[k]) r~=makeForget(quantum[k],values[k],loc);
			else rest~=quantum[k];
			gone~=nameOf(quantum[k]);
			quantum=quantum[0..k]~quantum[k+1..$];
		}
		if(rest.length) r=[cast(Expression)makeForget(tupleOf(rest,loc),null,loc)]~r;
		return r;
	}
	ForgetFrame* block(CompoundExp b,ForgetFrame* parent,Expression loop){ // (returns the frame at its end)
		if(b.blscope_){
			auto ids=identifiersOf(b.blscope_.forgottenVarsOnEntry,b.loc);
			if(ids.length) b.entryUncomputation=site(cast(Expression[])ids,new ForgetFrame([],parent,loop),[],b.loc);
		}
		auto end=statements(flatten(b.s),parent,loop);
		if(b.blscope_){
			auto ids=identifiersOf(b.blscope_.forgottenVars,b.loc);
			if(ids.length) b.exitUncomputation=site(cast(Expression[])ids,end,[],b.loc);
		}
		return end;
	}
	Expression statement; // (during `statements`: the innermost statement that contains the current expression)
	ForgetFrame* statements(Expression[] stmts,ForgetFrame* parent,Expression loop){ // (returns the frame at their end)
		auto outer=statement;
		scope(exit) statement=outer;
		Expression[] before; // (the statements before the current one, with the definitions of the components of tuple definitions, see `components`)
		foreach(i,s;stmts){
			auto f=new ForgetFrame(before,parent,loop);
			before~=components([s]);
			if(auto fe=cast(ForgetExp)s){
				if(!fe.val) fe.uncomputation=site(forgottenVariables(fe),f,[],fe.loc);
				else embedded(s,f);
				continue;
			}
			if(auto ret=cast(ReturnExp)s){
				auto ids=identifiersOf(ret.forgottenVars,ret.loc);
				if(ids.length) ret.uncomputation=site(cast(Expression[])ids,f,names(ret.e).writes,ret.loc); // (after the return value, which may consume variables)
			}
			statement=s;
			expression(s,f);
			embedded(s,f);
		}
		return new ForgetFrame(before,parent,loop);
	}
	void embedded(Expression s,ForgetFrame* f){ // (the forgets of variables of enclosing blocks within the parts of a statement that the reversal evaluates again, after the statement, see `embeddedForgets`)
		auto forgets=embeddedForgets(s);
		if(!forgets.length) return;
		auto local=declaredWithin(s);
		Expression[] outer;
		foreach(fe;forgets) foreach(v;forgottenVariables(fe)) if(auto id=cast(Identifier)unwrap(v)) if(id.meaning&&!isVersionOf(id.meaning,local)&&id.type&&!id.type.isClassical()&&!outer.any!(o=>nameOf(cast(Identifier)o)==nameOf(id))) outer~=id;
		if(!outer.length) return;
		auto values=site(outer,f,names(s).writes.filter!(w=>!outer.any!(o=>nameOf(cast(Identifier)o)==w)).array,s.loc).filter!(u=>!!(cast(ForgetExp)u).val).array;
		if(!values.length) return;
		foreach(fe;forgets){ // (the outermost statement, e.g., a definition whose reversal evaluates again a `let` expression with statements that forget them)
			fe.outerUncomputation=values;
			fe.outerStatement=s;
			fe.outerHoisted=null;
		}
	}
	void hoist(IteExp ite,ForgetFrame* f){ // (the quantum variables that both branches of an `if` statement or expression with a quantum condition forget, also within nested statements and expressions, e.g., in both branches of a classical `if` statement, and that it does not change otherwise, are recomputed before its reversal, as their definitions under the condition may not be supported, e.g., of closures)
		if(!ite.othw||!ite.cond.type||ite.cond.type.isClassical()) return;
		static struct Site{ Expression[]* uncomputation; Location loc; ForgetExp embedded; } // (where the reversal of a branch recomputes variables that it forgets; `embedded`: a forget within a part that the reversal evaluates again, see `embeddedForgets`)
		Site[] sites;
		Id[] other=names(ite.cond).writes.dup; // (the variables that the branches change other than by forgetting them)
		Identifier[] forgottenIn(CompoundExp b){
			Identifier[] r;
			void forgotten(Identifier id){ if(id.meaning&&id.type&&!id.type.isClassical()&&!r.any!(o=>nameOf(o)==nameOf(id))) r~=id; }
			void base(Expression e){
				e=unwrap(e);
				while(auto idx=cast(IndexExp)e) e=unwrap(idx.e);
				if(auto id=cast(Identifier)e) add(other,[nameOf(id)]);
			}
			void lhs(Expression e){
				e=unwrap(e);
				if(auto tpl=cast(TupleExp)e) foreach(y;tpl.e) lhs(y);
				else if(auto vec=cast(VectorExp)e) foreach(y;vec.e) lhs(y);
				else if(auto ce=cast(CatExp)e){ lhs(ce.e1); lhs(ce.e2); }
				else if(cast(IndexExp)e) base(e);
			}
			void visit(Expression e){
				if(auto ce=cast(CompoundExp)e){
					if(ce.loweredFrom) return visit(ce.loweredFrom);
					if(ce.blscope_){
						foreach(id;identifiersOf(ce.blscope_.forgottenVarsOnEntry~ce.blscope_.forgottenVars,ce.loc)) forgotten(id);
						sites~=[Site(&ce.entryUncomputation,ce.loc),Site(&ce.exitUncomputation,ce.loc)];
					}
					foreach(x;ce.s) visit(x);
					return;
				}
				if(auto fe=cast(ForgetExp)e) if(!fe.val){
					foreach(v;forgottenVariables(fe)){
						if(auto id=cast(Identifier)unwrap(v)) forgotten(id);
						else visit(v);
					}
					sites~=Site(&fe.uncomputation,fe.loc);
					if(fe.outerUncomputation.length) sites~=Site(&fe.outerUncomputation,fe.loc,fe);
					return;
				}
				if(auto we=cast(WithExp)e){
					add(other,names(we.trans).writes);
					foreach(id;outerForgets(we)) forgotten(id);
					sites~=Site(&we.uncomputation,we.loc);
					visit(we.bdy);
					return;
				}
				if(auto fd=cast(FunctionDef)e){
					if(fd.name) add(other,[fd.name.id]);
					foreach(_,ids;fd.captures) foreach(c;ids) visit(c);
					return;
				}
				if(auto id=cast(Identifier)e){
					if(id.meaning&&!id.meaning.isToplevelDeclaration()&&(!id.constLookup&&!id.implicitDup||id.byRef)) add(other,[nameOf(id)]);
					return;
				}
				if(auto nite=cast(IteExp)e){
					sites~=Site(&nite.uncomputation,nite.loc); // (hoisted out of a nested conditional)
					visit(nite.cond);
					visit(nite.then);
					if(nite.othw) visit(nite.othw);
					return;
				}
				if(auto de=cast(DefineExp)e){
					add(other,definedNames(de));
					lhs(de.e1);
				}
				if(auto ae=isOpAssignExp(e)) base(ae.e1);
				if(auto fe=cast(ForExp)e) if(fe.loopVar&&fe.loopVar.name) add(other,[fe.loopVar.name.id]);
				foreach(x;e.components) visit(x);
			}
			visit(b);
			return r;
		}
		auto inThen=forgottenIn(ite.then),inOthw=forgottenIn(ite.othw);
		Expression[] candidates;
		foreach(id;inThen) if(inOthw.any!(o=>nameOf(o)==nameOf(id))&&!other.canFind(nameOf(id))) candidates~=id;
		if(!candidates.length) return;
		auto changed=names(statement?statement:ite).writes.filter!(w=>!candidates.any!(c=>nameOf(cast(Identifier)c)==w)).array; // (also by the statement that contains an `if` expression)
		auto values=site(candidates,f,changed,ite.loc).filter!(u=>!!(cast(ForgetExp)u).val).array;
		if(!values.length) return;
		auto hoisted=values.map!(u=>nameOf(cast(Identifier)unwrap((cast(ForgetExp)u).var))).array;
		Id[] exclude(ref Expression[] uncomputation,Location loc){ // (the branches do not recompute them; returns the ones that it removes)
			Id[] removed;
			if(!uncomputation.length) return removed;
			Expression[] r;
			foreach(u;uncomputation){
				auto fe=cast(ForgetExp)u;
				Expression[] vars;
				foreach(v;forgottenVariables(fe)){
					auto id=cast(Identifier)unwrap(v);
					if(id&&hoisted.canFind(nameOf(id))) removed~=nameOf(id);
					else vars~=v;
				}
				if(vars.length) r~=vars.length<forgottenVariables(fe).length?makeForget(tupleOf(vars,fe.loc),fe.val,fe.loc):fe;
			}
			if(!r.length) r=[makeForget(tupleOf([],loc),null,loc)]; // (of nothing, which the reversal ignores)
			uncomputation=r;
			return removed;
		}
		foreach(site_;sites){
			auto removed=exclude(*site_.uncomputation,site_.loc);
			if(site_.embedded) add(site_.embedded.outerHoisted,removed); // (the reversal still evaluates the part again without forgetting them, see `recomputedBefore`)
		}
		ite.uncomputation=values;
	}
	void expression(Expression e,ForgetFrame* f){ // (`f`: the frame of the statement that contains `e`)
		if(cast(FunctionDef)e||cast(LambdaExp)e||cast(DoWhileExp)e) return; // (reversed separately, or not at all)
		if(auto ce=cast(CompoundExp)e){
			if(ce.loweredFrom) return expression(ce.loweredFrom,f);
			block(ce,f,null);
			return;
		}
		if(auto le=cast(LetExp)e){
			if(le.isForward(true)&&le.s.s.length>1){ // (`let{ x:=e; forget(…); } in x`, see `lowerDefine`)
				expression(le.s.s[0],f);
				foreach(j;1..le.s.s.length) if(auto fe=cast(ForgetExp)le.s.s[j]) if(!fe.val) fe.uncomputation=site(forgottenVariables(fe),new ForgetFrame(le.s.s[0..j],f,null),[],fe.loc);
				return;
			}
			auto end=block(le.s,f,null);
			static if(language==silq) if(blockUpdate(statement) is le){
				auto ids=resultForgets(le);
				auto cle=continuedLet(le);
				if(ids.length) le.resultUncomputation=site(cast(Expression[])ids,cle?new ForgetFrame(cle.s.s,end,null):end,[],le.loc);
			}
			expression(le.e,end);
			return;
		}
		ForgetFrame* after(Expression[] earlier){ return earlier.length?new ForgetFrame([],f,null,earlier):f; }
		if(auto ite=cast(IteExp)e){
			expression(ite.cond,f);
			auto g=after([ite.cond]);
			block(ite.then,g,null);
			if(ite.othw) block(ite.othw,g,null);
			hoist(ite,f);
			return;
		}
		if(auto fe=cast(ForExp)e){ block(fe.bdy,f,fe); return; }
		if(auto we=cast(WhileExp)e){ block(we.bdy,f,we); return; }
		if(auto re=cast(RepeatExp)e){ block(re.bdy,f,re); return; }
		if(auto we=cast(WithExp)e){
			block(we.bdy,block(we.trans,f,null),null);
			auto outer=outerForgets(we);
			if(outer.length) we.uncomputation=site(cast(Expression[])outer,f,chain(names(we.trans).writes,names(we.bdy).writes).array,we.loc); // (after the statement)
			return;
		}
		bool ordered=!cast(DefineExp)e&&!cast(AssignExp)e&&!isOpAssignExp(e); // (the left-hand side of a definition or an update is written after the right-hand side)
		Expression[] earlier;
		foreach(x;e.components){
			expression(x,after(earlier));
			if(ordered) earlier~=x;
		}
	}
}
void resolveForgets(CompoundExp body_){ // (see `ForgetExp.uncomputation`)
	ForgetResolution r;
	r.statements(flatten(body_.s),null,null);
}
}
Expression[] reverseStatements(Expression[] statements,Expression[] middle,Scope sc,bool unchecked,bool noImplicitDup,bool hoistClassical=false,bool defer=false,Id[] given=null,Id[] alive=null,Id[] copied=null,Id[]* excludedCopied=null,Id[] forgotten=null,NeedOld* needOld=null){
	statements=mergeCompound(statements);
	static if(language==silq) statements=statements.map!uncomputed.joiner.array;
	if(hoistClassical){ // (`given`: the variables whose values the reversal receives, e.g., the classical results of a function; `alive`: the variables that the reversal of an enclosing block recomputes; `copied`: the variables of an enclosing block whose changes are recomputed on copies, see `lowerLetDefine`)
		auto defined=middle.map!definedNames.joiner.array; // (received after the recomputation, which they are checked against)
		static if(language==silq) Id[] givenAfter(size_t i){ return given.filter!(n=>!usesUp(n,statements[i+1..$].filter!(t=>!movedIntoItself(t,n)).array)).array; } // (not a definition that moves the variable into its own new version, which keeps the received version, see `movedIntoItself`)
		else Id[] givenAfter(size_t i){ return given.filter!(n=>!usesUp(n,statements[i+1..$])).array; }
		bool reads(Expression e,Id name){ return e.subexpressions.any!(x=>cast(Identifier)x&&nameOf(cast(Identifier)x)==name); }
		auto changed=statements.map!changedNames.array;
		static if(language==silq){
			auto lossy=new Id[][](statements.length); // (the changes that the reversal cannot undo in place, see `lossyChanges`)
			auto outer=chain(alive,copied).array; // (the variables of enclosing blocks that the reversal of the block sees)
			auto redefined=new Id[][](statements.length); // (classical variables of the block or of enclosing blocks that a statement defines again after they are forgotten or moved, e.g., `v` in `forget(v); v:=2;`: the recomputation keeps the earlier versions for the reversals of earlier statements, see `recomputation`, and forgets them right before the statement, which changes them)
			auto classicalDefined=statements.map!classicalEscapingNames.array;
			bool ofBlock(size_t j,Id n){ // (a variable that an earlier statement of the block defines, not one of an enclosing block that it only moves into its own new version, e.g., `v` for `(w,v):=(1,v)` in the body of a `with` statement in a loop, whose reversal recomputes the iterations on copies of the versions before them, see `NeedOld`; nor one whose kept version a statement between them forgets without leaving a new one, e.g., `v` for `with { … } do { v:=1; w:=move(v); }` after `forget(v)`, see `redefined`)
				foreach_reverse(h;0..j){
					if(redefined[h].canFind(n)) return availableAfter(statements[h],n);
					if(classicalDefined[h].canFind(n)&&availableAfter(statements[h],n)&&!movedIntoItself(statements[h],n)) return true;
				}
				return false;
			}
			auto unsupported=new Id[][](statements.length); // (classical variables that the body of a `with` statement with quantum operations defines again after an earlier statement forgets or moves them, see `reversal`)
			auto readAgain=new Id[][](statements.length); // (classical variables that a statement reads, consumes and defines again only for itself, e.g., `v` for `if c { w:=move(v); v:=w+1; xs[v]:=X(xs[v]); } else { w:=move(v); }`, after which `v` is not available: the recomputation of its classical part keeps the move, see `recomputation`, but its reversal reads the version before it, see `reversal`)
			foreach(j,s;statements){
				lossy[j]=lossyChanges(s);
				if(auto we=cast(WithExp)s) if(classifyStatement(s)!=ComputationClass.classical){ // (the reversal of the body recomputes the definitions, see `projection`: the recomputation of the block would not see the versions after it, also of a variable that an earlier statement forgets or moves, or that it reads before it forgets or moves it itself)
					auto again=changes(we.bdy)[1];
					readAgain[j]=again.filter!(n=>!availableAfter(s,n)&&readsBefore(s,n)).array;
					foreach(n;chain(again,classicalDefined[j])) if(availableAfter(s,n)&&!lossy[j].canFind(n)&&!unsupported[j].canFind(n)&&!movedIntoItself(s,n)){
						bool survives;
						auto self=consumesBeforeDefining(we.bdy,n,&survives),consumed=again.canFind(n)||self,local=ofBlock(j,n);
						if(self&&!survives&&local&&!readsBefore(s,n)&&definedInBlocks(we.bdy,n)) lossy[j]~=n; // (it only forgets the version before it of a variable of the block, on each path, which is lost, as for other statements, e.g., `v` for `v:=j+1; with { … } do { with { … } do { forget(v); } v:=2; … }`: the reversal of the body receives the new version, see `reversal`)
						else if(consumed||local||outer.canFind(n)) unsupported[j]~=n;
					}
					continue;
				}
				auto again=changes(s)[1]; // (the recomputation keeps their forgets and moves, see `recomputation`)
				readAgain[j]=again.filter!(n=>!availableAfter(s,n)&&readsBefore(s,n)).array;
				Id[] consumedItself; // (the statement forgets or moves the version before it itself, e.g., `v` for `with { … } do { forget(v); with { … } do { v:=2; } }`: no forget before the recomputation)
				foreach(n;classicalDefined[j]) if(!changed[j].canFind(n)&&!again.canFind(n)&&!redefined[j].canFind(n)&&!consumedItself.canFind(n)&&!movedIntoItself(s,n)&&(outer.canFind(n)||ofBlock(j,n))){
					if(consumesBeforeDefining(s,n)) consumedItself~=n; // (also where its new version is not available after it, e.g., `v` for `with { … } do { forget(v); with { … } do { v:=j+3; forget(v); } }`, which loses the version before it)
					else if(availableAfter(s,n)||classifyStatement(s)==ComputationClass.classical) redefined[j]~=n; // (for a statement that the reversal reverses in place, only where its new version is available after it, e.g., not for `if c { v:=1; xs[v]:=X(xs[v]); } else { v:=2; }` after `forget(v)` if no later statement reads `v`, whose reversal defines `v` in the branches; but the recomputation of a classical statement forgets the kept version first also where its new version is not available after it, e.g., for `with { r:=2; } do { v:=t*2; }` in a branch after `w:=move(v)`)
				}
				foreach(n;chain(redefined[j],consumedItself)){
					if(!changed[j].canFind(n)) changed[j]~=n;
					if(!lossy[j].canFind(n)) lossy[j]~=n;
				}
			}
			bool availableAtEnd(Id n){
				auto avail=true;
				foreach(t;statements) avail=availableAfter(t,n,avail);
				return avail&&!forgotten.canFind(n);
			}
			auto before=outer.filter!(n=>!copied.canFind(n)&&!given.canFind(n)&&lossy.joiner.canFind(n)&&!availableAtEnd(n)).array; // (variables of enclosing blocks that a statement of the block changes such that the reversal cannot recompute their versions before it, see `lossyChanges`, and that are not available after the block, other than those whose versions after it the reversal receives, e.g., `v` for `forget(v); v:=2;` in a branch of a conditional whose other branch updates `v`: the reversal of the block receives their versions before it and recomputes all of their changes, e.g., `v` for `v+=1; xs[v]:=X(xs[v]); forget(v); v:=2; forget(v);` in the body of a `with` statement)
		}
		auto headerChanges=new Id[][](statements.length); // (the variables of the condition or bounds of an `if` statement or a loop that it changes: the reversal reads copies of the versions before it)
		foreach(i,s;statements) foreach(h;headers(s)) foreach(x;h.subexpressions) if(auto id=cast(Identifier)x) if(changed[i].canFind(nameOf(id))&&!headerChanges[i].canFind(nameOf(id))) headerChanges[i]~=nameOf(id);
		auto local=chain(copied,statements.map!(s=>definedNames(s).filter!(n=>!movedIntoItself(s,n))).joiner).array; // (not a variable of an enclosing block that a statement only moves into its own new version, see `movedIntoItself`)
		size_t[Id] innerFrom; // (the variables of the block as `local`, but without new versions of variables of an enclosing block, e.g., one that a `let` expression returns, see `NeedOld`; from the statement that defines them on, before which they are those of an enclosing block, e.g., `v` for `if v%4==3 { … forget(v); } else { forget(v); } v:=dup(j);` in the body of a loop, whose version before the loop an enclosing block may provide)
		foreach(n;copied) innerFrom[n]=0;
		foreach(j,s;statements) foreach(n;definedNames(s)) if(!changed[j].canFind(n)&&!(n in innerFrom)&&!movedIntoItself(s,n)) innerFrom[n]=j;
		bool innerAt(size_t i,Id n){ auto k=n in innerFrom; return k&&*k<=i; }
		auto undoFirst=new bool[](statements.length); // (updates of variables of an enclosing block that no later statement mentions, e.g., in a branch: they are reversed first, such that the recomputed statements see the versions before them)
		bool noop(Expression e){ auto fe=cast(ForgetExp)e; return fe&&!fe.val&&fe.var.type&&fe.var.type.isClassical(); } // (its reversal does nothing, see `lowerDefine`)
		bool classicalUpToForgets(Expression s){ // (also, e.g., an `if` statement whose branch forgets a classical variable at its last use)
			if(noop(s)) return true;
			static if(language==silq) if(auto ce=cast(CompoundExp)s) if(ce.loweredFrom) return classicalUpToForgets(ce.loweredFrom);
			if(auto ite=cast(IteExp)s) return ite.cond.type&&ite.cond.type.isClassical()&&chain(ite.then.s,ite.othw?ite.othw.s:[]).all!(t=>classicalUpToForgets(t));
			if(auto fe=cast(ForExp)s) return fe.bdy.s.all!(t=>classicalUpToForgets(t));
			if(auto re=cast(RepeatExp)s) return re.bdy.s.all!(t=>classicalUpToForgets(t));
			return classifyStatement(s)==ComputationClass.classical;
		}
		bool onlyClassical(Expression s){ // (no quantum values, closures or calls other than to `dup`)
			foreach(x;s.subexpressions){
				if(x.type&&!x.type.isClassical()||cast(LambdaExp)x||cast(FunctionDef)x) return false;
				if(auto ce=cast(CallExp)x) if(!ce.isSquare){
					Expression f=ce.e;
					if(auto sq=cast(CallExp)f) if(sq.isSquare) f=sq.e;
					auto id=cast(Identifier)f;
					if(!id||isPreludeSymbol(id)!="dup") return false;
				}
			}
			return true;
		}
		auto dead=new bool[](statements.length); // (classical statements whose values no later statement uses, e.g., the definition of a local that is forgotten right after it, or a swap of the components of a local vector at its end: the reversal neither recomputes nor reverses them)
		Id[] mentions(Expression e){ Id[] r; walkIdentifiers(e.copy(),(Identifier id){ r~=id.id; }); return r; } // (as the reversal mentions them, e.g., a type variable that the analysis substitutes into an annotation, or a capture of a local function)
		auto mentionsOf=statements.map!mentions.array,mentionedAfter=middle.map!mentions.joiner.array;
		bool forgetsIn(Expression s,Id n){ // (e.g., an `if` statement whose branch forgets it at its last use)
			auto ite=cast(IteExp)s;
			if(!ite) return false;
			foreach(b;[ite.then,ite.othw]) if(b&&(forgottenNames(b).canFind(n)||b.s.any!(t=>noop(t)&&reads(t,n)||forgetsIn(t,n)))) return true;
			return false;
		}
		foreach_reverse(i,s;statements){
			auto names=chain(definedNames(s),changed[i]).array;
			if(noop(s)||!onlyClassical(s)) continue;
			static if(language==silq) if(!names.length){ dead[i]=!cast(ForgetExp)s; continue; } // (e.g., `with { u:=1; } do { w:=move(v); }`, which forgets its variables itself: its recomputation may read variables of earlier statements that are not recomputed)
			if(!names.length) continue;
			bool isLocal(Id n){ return copied.canFind(n)||statements[0..i+1].any!(t=>definedNames(t).canFind(n)&&!movedIntoItself(t,n)); } // (not a variable of an enclosing block that a statement only moves into its own new version, e.g., `v` for `(w,v):=(1,v); v+=w;` before `forget(v)`, whose changes the reversal reverts)
			bool usedUp(Id n){ return usesUp(n,statements[i+1..$])||forgotten.canFind(n)||forgetsIn(s,n)||!availableAfter(s,n); } // (otherwise, it may be used after the block; also one that the statement forgets itself, e.g., at its last use in the body of a `with` statement)
			static if(language==silq) bool unseen(Id n){ return outer.canFind(n)&&!availableAtEnd(n); } // (a variable of an enclosing block that the block does not leave available: the reversal of the block keeps the version before it, e.g., `v` for `with { … } do { for i in 0..2 { v+=1; forget(v); v:=i; } }` in the body of a `with` statement after which no statement reads `v`)
			else bool unseen(Id n){ return false; }
			if(!names.all!(n=>(isLocal(n)||unseen(n))&&usedUp(n)&&!given.canFind(n)&&!defined.canFind(n)&&!mentionedAfter.canFind(n))) continue;
			dead[i]=iota(i+1,statements.length).all!(j=>dead[j]||noop(statements[j])||!names.any!(n=>mentionsOf[j].canFind(n)));
		}
		Id[] invariants; // (classical definitions that only read variables that no statement of the block changes, e.g., `v:=n+c`, can be recomputed first, such that statements that are reversed first may read them, see `early`)
		auto changedAll=changed.joiner.array;
		foreach(i,s;statements){
			auto names=definedNames(s);
			if(dead[i]||!names.length||changed[i].length||classifyStatement(s)!=ComputationClass.classical) continue;
			if(names.any!(n=>changedAll.canFind(n)||given.canFind(n)||defined.canFind(n)||copied.canFind(n)||statements.count!(t=>definedNames(t).canFind(n))>1)) continue;
			Id[] mentioned;
			foreach(x;s.subexpressions) if(auto id=cast(Identifier)x) if(!names.canFind(nameOf(id))) mentioned~=nameOf(id);
			if(mentioned.any!(n=>changedAll.canFind(n)||defined.canFind(n)||local.canFind(n)&&!invariants.canFind(n))) continue;
			invariants~=names;
		}
		foreach_reverse(i,s;statements){
			if(dead[i]||!classicalUpToForgets(s)||definedNames(s).length||!changed[i].length||headerChanges[i].length) continue;
			static if(language==silq) if(lossy[i].length||changed[i].any!(n=>before.canFind(n))) continue; // (the reversal does not have the versions before it, or does not have the ones after it, see `before`)
			Id[] mentioned;
			foreach(x;s.subexpressions) if(auto id=cast(Identifier)x) mentioned~=nameOf(id);
			auto read=mentioned.filter!(n=>!changed[i].canFind(n)).array;
			if(mentioned.any!(n=>local.canFind(n)&&!invariants.canFind(n))||changed[i].any!(n=>middle.any!(t=>reads(t,n)))||read.any!(n=>defined.canFind(n))) continue;
			undoFirst[i]=iota(i+1,statements.length).all!(j=>undoFirst[j]||dead[j]||noop(statements[j])||!changed[i].any!(n=>reads(statements[j],n))&&!changed[j].any!(n=>read.canFind(n)));
		}
		auto early=new bool[](statements.length); // (the invariant definitions that the statements which are reversed first read, also indirectly)
		foreach_reverse(i,s;statements){
			auto names=definedNames(s);
			if(names.length&&names.all!(n=>invariants.canFind(n))) early[i]=iota(i+1,statements.length).any!(j=>(undoFirst[j]||early[j])&&names.any!(n=>reads(statements[j],n)));
		}
		auto changedAfter=new Id[][](statements.length);
		foreach_reverse(i;1..statements.length) changedAfter[i-1]=changedAfter[i]~(undoFirst[i]||dead[i]?[]:changed[i]);
		auto recomputed=new bool[](statements.length);
		auto projections=new Expression[](statements.length); // (classical variables that a reversed `if` statement or loop defines for later statements or changes are recomputed as well)
		auto projectionChanges=new Id[][](statements.length);
		auto blockedAt=new Id[][](statements.length); // (variables of an enclosing block that a statement which is not recomputed reads before a later statement changes them, see `NeedOld`)
		Id[] excluded; // (variables that a reversed statement which is not recomputed changes, e.g., a loop with quantum statements: the statements that define them are reversed as well)
		for(;;){
			auto hoisted=copied.dup;
			foreach(i,s;statements){
				auto after=givenAfter(i);
				bool movedBack(Id n){ return movedIntoItself(s,n)&&!changedAfter[i].canFind(n)&&!usesUp(n,statements[i+1..$].filter!(t=>!movedIntoItself(t,n)&&!noop(t)).array); } // (a variable that the reversal changes in place, see `excluded`, and that it moves into its own new version, if no later statement changes or uses it up, other than by a forget whose reversal does nothing: the recomputation moves the version after it, which the reversal of the block starts with, into itself before the reversal changes it, e.g., `v` for `v+=dup(j); (w,v):=(j*2,v);` in a branch)
				static if(language==silq) bool recomputable(Id n){ return hoisted.canFind(n)||before.canFind(n)||lossy[i].canFind(n)&&outer.canFind(n); } // (also a variable of an enclosing block whose version before the block the reversal of the block receives, see `before`, which saves it where a statement defines it again, see `oldVersions`, as for a variable of an enclosing block that the statement defines again, e.g., `v` for `with { … } do { v:=j*2; v+=1; }` after `forget(v)` in a branch, if the block leaves it available)
				else bool recomputable(Id n){ return hoisted.canFind(n); }
				bool valid(Id[] names,Id[] changes){
					if(!changes.all!recomputable) return false; // (e.g., the reversal of a nested block reverses the changes of variables that an enclosing block defines)
					static if(language==silq) bool keptBefore(Id n){ return outer.canFind(n)&&!given.canFind(n)&&iota(i).all!(h=>!changed[h].canFind(n))&&iota(i+1,statements.length).all!(k=>!changed[k].canFind(n)||redefined[k].canFind(n)); } // (a variable of an enclosing block whose version before the block the reversal sees and that later statements only define again, whose recomputations keep that version, see `redefined`, e.g., `v` for `w:=move(v);` before `v:=w+1;` in a branch)
					else bool keptBefore(Id n){ return false; }
					if(changedAfter[i].any!(n=>!recomputable(n)&&!keptBefore(n)&&(names.canFind(n)?movedIntoItself(s,n)&&readsBesidesMove(s,n):readsOther(s,n)))) return false; // (the recomputation would see the version after the change, also of a variable that it moves into its own new version and reads otherwise, e.g., `v` for `(w,v):=(v*2,v);` before `v+=1;` in a branch)
					return !chain(names,changes).any!(n=>excluded.canFind(n)&&!movedBack(n)||after.canFind(n)&&!defined.canFind(n)&&!movedIntoItself(s,n)); // (the reversed definition checks the received value, unless the new version is the one before it)
				}
				auto names=definedNames(s);
				recomputed[i]=!dead[i]&&classifyStatement(s)==ComputationClass.classical&&valid(names,changed[i]);
				projections[i]=null;
				static if(language==silq) if(!recomputed[i]&&!dead[i]){
					auto drop=changed[i].filter!(n=>!recomputable(n)||after.canFind(n)&&!defined.canFind(n)).array; // (variables whose current versions the reversal changes in place, e.g., a variable of an enclosing block that a `let` expression returns, in a loop that also changes one that it consumes)
					auto p=projection(s,sc,drop);
					void consider(Expression p){
						auto pnames=definedNames(p),pchanges=changed[i].filter!(n=>!drop.canFind(n)).array; // (all of the others, see `projection`)
						auto receives=cast(DefineExp)s&&cast(CallExp)unwrap((cast(DefineExp)s).e2); // (the reversed call receives the classical results, see `callProjection`)
						static if(language==silq) if(cast(WithExp)s&&classifyStatement(s)!=ComputationClass.classical&&lossy[i].length) receives=true; // (the reversal of the body receives the new versions of the variables that it forgets and defines again, see `aliveFor`, also where no later statement that the reversal keeps reads them)
						if((pchanges.length||receives||iota(i+1,statements.length).any!(k=>!dead[k]&&!noop(statements[k])&&pnames.any!(n=>reads(statements[k],n))))&&valid(pnames,pchanges)){ // (not for later statements whose values no statement uses, see `dead`, e.g., `w:=v+3` after `with { … } do { v:=j*2; for i in 0..2 { forget(v); v:=u+i; } xs[j]:=X(xs[j]); }`, whose reversal would then receive `v`, nor for forgets without values, e.g., `forget(t)` after `with { … } do { t:=move(v); xs[w]:=X(xs[w]); v:=1; }`)
							projections[i]=p;
							projectionChanges[i]=pchanges;
						}
					}
					if(p) consider(p);
					static if(language==silq) if(p&&!projections[i]){ // (without the definitions of variables whose values the reversal receives, which the reversed statement checks, e.g., `w` for `with { … } do { v:=dup(u); w:=u*2; xs[v]:=X(xs[v]); }` that the reversal of an enclosing block recomputes: the classical part reads the received values)
						auto skip=definedNames(p).filter!(n=>after.canFind(n)&&!defined.canFind(n)).array;
						if(skip.length) if(auto q=projection(s,sc,drop,null,skip)) consider(q);
					}
					if(!projections[i]&&(p||classifyStatement(s)==ComputationClass.classical)){ // (also in earlier iterations, e.g., before the variables that the statement changes are excluded)
						foreach(n;changedAfter[i]) if(!hoisted.canFind(n)&&!innerAt(i,n)&&reads(s,n)&&!blockedAt[i].canFind(n)) blockedAt[i]~=n;
						if(names.any!(n=>!after.canFind(n)&&iota(i+1,statements.length).any!(j=>!dead[j]&&reads(statements[j],n)))) // (definitions that the reversals of later statements read, which it computes from the versions before it of the variables that it changes, e.g., `w` and `v` for `with { … } do { w:=v*2; v+=3; }` in a branch)
							foreach(n;drop) if(!innerAt(i,n)&&reads(s,n)&&!blockedAt[i].canFind(n)) blockedAt[i]~=n;
					}
				}
				if(recomputed[i]) hoisted~=names.filter!(n=>!movedIntoItself(s,n)||hoisted.canFind(n)).array; // (not a variable that it only moves into its own new version, whose version the recomputation does not compute, e.g., `v` for `(w,v):=(2,v);` before `v+=1;` in a branch, whose reversal changes `v` back in place)
				else if(projections[i]) hoisted~=definedNames(projections[i]);
			}
			bool needed(Id n){ return given.canFind(n)||copied.canFind(n)||middle.any!(t=>readsBesidesUpdates(t,n))||iota(statements.length).any!(j=>!dead[j]&&readsBesidesUpdates(statements[j],n)); } // (otherwise, its values do not matter, e.g., a vector whose components are updated but not read; but the reversal of an update of a copy reads the version after it, e.g., of `k` for `(y,j):=let { repeat 2 { k+=j; j*=2; } } in (x,j);`, which would fail on the version before it)
			auto more=iota(statements.length).filter!(i=>!recomputed[i]&&!projections[i]&&!dead[i]).map!(i=>changed[i]).joiner.filter!(n=>hoisted.canFind(n)&&!excluded.canFind(n)&&needed(n)).array;
			static if(language==silq) foreach(i;0..statements.length) if(!recomputed[i]&&!projections[i]&&!dead[i]&&changed[i].any!(n=>copied.canFind(n)&&more.canFind(n))) // (the reversal would not have the versions of the copy after the statement, see `excludedCopied` in `lowerLetDefine`)
				foreach(n;changed[i]) if(!hoisted.canFind(n)&&!innerAt(i,n)&&!blockedAt[i].canFind(n)) blockedAt[i]~=n;
			if(!more.length){
				if(excludedCopied) *excludedCopied=excluded.filter!(n=>copied.canFind(n)).array;
				if(needOld) foreach(n;blockedAt.joiner) if(!needOld.vars.canFind(n)) needOld.vars~=n;
				break;
			}
			excluded~=more;
		}
		Id[] checked=copied.filter!(n=>!excluded.canFind(n)&&given.canFind(n)).array; // (also a copy that no statement changes, e.g., of a classical parameter that a function returns, see `reverseFunction`)
		foreach(i,s;statements){
			auto names=recomputed[i]?chain(definedNames(s),changed[i]).array:projections[i]?chain(definedNames(projections[i]),projectionChanges[i]).array:[];
			checked~=names.filter!(n=>givenAfter(i).canFind(n)).array;
		}
		foreach(e;middle) foreach(id;definedIdentifiers(e)) if(checked.canFind(nameOf(id))) id.implicitDup=true;
		auto undone=new bool[](statements.length); // (the reversal of an earlier statement reads the version before the change, also that of an update that is reversed itself)
		for(bool more=true;more;){
			more=false;
			foreach(i;0..statements.length) if(recomputed[i]&&!undone[i]&&changed[i].any!(n=>iota(i).any!(j=>!dead[j]&&(!recomputed[j]||undone[j])&&reads(statements[j],n))))
				undone[i]=more=true;
			static if(language==silq) foreach(i;0..statements.length) if(recomputed[i]&&!undone[i]&&(lossy[i].any!(n=>outer.canFind(n))||changed[i].any!(n=>before.canFind(n)))) undone[i]=more=true; // (the reversal of the block ends with the versions before it, which the enclosing block may read)
		}
		static if(language==silq) bool readEarlier(size_t i,Id n){ // (the version before the statement, for the reversal of an earlier statement)
			return iota(i).any!(h=>!dead[h]&&!undoFirst[h]&&(!recomputed[h]||undone[h])&&reads(statements[h],n));
		}
		static if(language==silq) bool neededBefore(size_t i,Id n){ // (the version before the statement, e.g., for the reversal of an earlier statement, or for an enclosing block)
			return outer.canFind(n)||readEarlier(i,n);
		}
		auto hoistedAll=chain(copied,iota(statements.length).map!(i=>recomputed[i]?definedNames(statements[i]):projections[i]?definedNames(projections[i]):[]).joiner).array;
		auto saves=new Id[][](statements.length); // (the fresh names of the copies, see `headerChanges`)
		static if(language==silq) foreach(i;0..statements.length) if(headerChanges[i].length&&(projections[i]||recomputed[i]&&undone[i])&&headerChanges[i].all!(n=>hoistedAll.canFind(n)||before.canFind(n))) saves[i]=headerChanges[i].map!(n=>freshName()).array;
		auto savedValues=new Expression[][](statements.length); // (for a statement that the reversal reverses in place without recomputing its classical part, the right-hand sides of the definitions before it of the variables of its condition or range that only read variables that no statement of the block changes or defines: the copies evaluate them, e.g., `v` for `v:=j+j; if v%4==0 { v+=u; xs[j%4]:=X(xs[j%4]); }` in the body of a `with` statement whose reversal receives `v`)
		static if(language==silq) foreach(i;0..statements.length) if(headerChanges[i].length&&!saves[i].length&&!recomputed[i]&&!projections[i]){
			Expression[] values;
			foreach(n;headerChanges[i]){
				auto h=iota(i).retro.find!(k=>definedNames(statements[k]).canFind(n)||changed[k].canFind(n));
				if(h.empty) break;
				auto de=cast(DefineExp)statements[h.front];
				if(!de||!cast(Identifier)unwrap(de.e1)||changed[h.front].length||classifyStatement(de)!=ComputationClass.classical||de.e2.consumes) break;
				if(de.e2.subexpressions.any!(x=>cast(Identifier)x&&(changedAll.canFind(nameOf(cast(Identifier)x))||local.canFind(nameOf(cast(Identifier)x))&&!invariants.canFind(nameOf(cast(Identifier)x))))) break;
				values~=de.e2;
			}
			if(values.length==headerChanges[i].length){
				saves[i]=headerChanges[i].map!(n=>freshName()).array;
				savedValues[i]=values;
			}
		}
		auto aliveAt=new Id[][](statements.length); // (the variables whose current versions the reversal of a statement sees as recomputed values)
		alive=alive~copied;
		foreach(i,s;statements){
			aliveAt[i]=alive;
			auto names=definedNames(s);
			alive=alive.filter!(n=>!names.canFind(n)).array;
			static if(language==silq) if(recomputed[i]&&!early[i]||projections[i]) alive=alive.filter!(n=>!redefined[i].canFind(n)||availableAfter(s,n)).array; // (the recomputation forgets the kept version before the statement, which leaves no new one, e.g., `v` for `with { … } do { v:=1; w:=move(v); }` after `forget(v)`, see `redefined`)
			if(recomputed[i]) alive~=names;
			else if(projections[i]) alive~=definedNames(projections[i]);
			else static if(language==silq) alive~=aliveAt[i].filter!(n=>names.canFind(n)&&movedIntoItself(s,n)&&!changed[i].canFind(n)).array; // (the new version of a variable that a statement which the reversal reverses in place moves into itself is the recomputed one, e.g., `v` for `(v,):=(v,)`, which the recomputation of a later definition after `forget(v)` forgets first, see `redefined`)
		}
		static if(language==silq){
			auto shadowed=new Id[][](statements.length); // (kept versions of earlier variables with the names of variables of its own of a statement, which the statement does not see: its recomputation renames its variables, see `renamedLocals`, and the reversal of a conditional or a `with` statement saves the kept versions, see `redefined`)
			foreach(i,s;statements){
				auto escaping=definedNames(s);
				foreach(n;definedWithin(s)) if((aliveAt[i].canFind(n)||(recomputed[i]||projections[i])&&given.canFind(n)&&!defined.canFind(n)&&!givenAfter(i).canFind(n))&&!escaping.canFind(n)&&!redefined[i].canFind(n)&&!shadowed[i].canFind(n)){ // (also, for a recomputation, the versions from later statements that the reversal receives before it, e.g., `v` for `if c { v:=1; … }` in the body of a `with` statement that defines `v` after it, but not those that it receives afterwards, see `middle`)
					auto avail=outer.canFind(n);
					foreach(t;statements[0..i]) avail=availableAfter(t,n,avail);
					if(!avail||!readsOther(s,n)) shadowed[i]~=n; // (also if the statement does not mention the version before it, which it then does not see, e.g., `v` for `if c { v:=w+1; }` in a branch after `w:=move(v)`, as the version is available only to the reversal)
				}
			}
			bool isLoop(Expression e){
				if(auto ce=cast(CompoundExp)e) if(ce.loweredFrom) return isLoop(ce.loweredFrom);
				return cast(ForExp)e||cast(RepeatExp)e||cast(WhileExp)e;
			}
			auto saving=iota(statements.length).map!(i=>isLoop(statements[i])?shadowed[i]:[]).array; // (for a loop, the reversal saves them around its reversal, e.g., `v` for `for i in 0..2 { v:=i+j; … }` after `forget(v)`)
			auto copies=new Expression[](statements.length);
			bool lostBy(size_t i,Id n){ // (the recomputation of a statement that the reversal also reverses forgets or moves the version before it, e.g., `v` for `with { … } do { k+=1; for i in 0..2 { forget(v); v:=i; } }`, but not for `with { … } do { k+=1; forget(v); v:=2; }`, whose recomputation renames its own versions, see `recomputation`)
				if(!recomputed[i]) return false;
				if(!copies[i]) copies[i]=recomputation(statements[i],sc);
				return consumesVariable(copies[i],n)&&!availableAfter(copies[i],n);
			}
			auto preserved=new Id[2][][](statements.length); // (copies of the versions before a statement whose reversal does not read copies, see `readsOld`, that its projection forgets or moves and defines again only for itself, which do not count as changes, see `changedNames`, but which the reversals of earlier statements read: the reversal of the statement receives them, e.g., `v` for `with { … } do { xs[0]:=X(xs[0]); k+=1; forget(v); v:=2; }` after `xs[v]:=X(xs[v]);`, see `before`)
			foreach(i;0..statements.length){
				if(projections[i]&&!readsOld(statements[i])){
					auto pc=chain(projectionChanges[i],definedNames(projections[i])).array;
					preserved[i]=aliveAt[i].filter!(n=>!pc.canFind(n)&&!changed[i].canFind(n)&&!shadowed[i].canFind(n)&&consumesVariable(projections[i],n)&&(neededBefore(i,n)||availableAfter(projections[i],n)&&readsBefore(statements[i],n))).map!(n=>cast(Id[2])[n,freshName()]).array; // (also the versions that the reversal of the statement reads, which the projection replaces with its own, e.g., `v` for `with { … } do { for i in 0..2 { forget(v); v:=i; } k+=1; xs[0]:=X(xs[0]); forget(v); }` after `xs[v]:=X(xs[v]);`, see `classicalPart`)
				}else if(recomputed[i]&&undone[i]&&!readsOld(statements[i])) preserved[i]=aliveAt[i].filter!(n=>!changed[i].canFind(n)&&!shadowed[i].canFind(n)&&lostBy(i,n)&&(readEarlier(i,n)||!lossy[i].length&&readsBefore(statements[i],n))).map!(n=>cast(Id[2])[n,freshName()]).array; // (also the versions that the recomputation of a statement that the reversal reverses as well loses, see `lostBy`, if the reversals of earlier statements of the block or of the statement read them, but not an enclosing block, which then does not see them, e.g., `v` for `with { … } do { k+=1; for i in 0..2 { forget(v); v:=i; } }` after `xs[v+k]:=X(xs[v+k]);`; not the reversal of a statement with lossy changes, which gives back the versions before it that the recomputation saves, see `oldVersions`)
			}
			bool consumedByProjection(size_t i,Id n){ return projections[i]&&!readsOld(statements[i])&&!changed[i].canFind(n)&&consumesOuterVersion(projections[i],n)&&!availableAfter(projections[i],n); } // (the classical part of the statement, which the reversal recomputes first, forgets the version before it and leaves none, e.g., `v` for `with { … } do { with { … } do { for i in 0..2 { k+=1; forget(v); v:=i; } } xs[0]:=X(xs[0]); }` after which no statement reads `v`)
			Id[] aliveFor(size_t i){ // (the reversal of a `with` statement with quantum operations receives the versions after it of the variables that it forgets or moves and defines again itself, whose versions before it are lost, see `unsupported`; not the versions that the recomputation of the statement loses, unless it receives copies of them, see `preserved`)
				auto we=cast(WithExp)statements[i];
				return aliveAt[i].filter!(n=>!saving[i].canFind(n)&&!(we&&classifyStatement(we)!=ComputationClass.classical&&lossy[i].canFind(n))&&!((lostBy(i,n)||consumedByProjection(i,n))&&!preserved[i].canFind!(o=>o[0]==n))).array;
			}
		}else Id[] aliveFor(size_t i){ return aliveAt[i]; }
		auto oldVersions=new Id[2][][](statements.length); // (copies of the versions before a statement whose classical part is recomputed, for its reversal, see `NeedOld`)
		Id[][] consumedBy=new Id[][](statements.length); // (variables in `oldVersions` that do not exist after the recomputed statement, e.g., `v` for `with { … } do { forget(v); if c { v:=1; … } }`, also where it only changes them and forgets them at their last uses, e.g., `v` for `with { … } do { t:=dup(u); v+=1; (w,v):=(j*2,v); }` after `forget(t)`, as its recomputation keeps the forgets of its own variables, see `recomputation`)
		enum headerChangeError="reversal of `if` statement or loop that changes a variable of its condition or range not supported yet";
		enum redefinitionError="reversal of redefinitions of classical variables not supported yet";
		Expression reversal(size_t i){
			static if(language==silq) if(auto fe=cast(ForgetExp)statements[i]) if(fe.val) if(auto id=cast(Identifier)unwrap(fe.var)){
				if(id.type&&id.type.isClassical()&&(aliveAt[i].canFind(nameOf(id))||givenAfter(i).canFind(nameOf(id)))){ // (the forgotten value is recomputed or received, it is checked)
					auto var=id.copy();
					var.moved=false;
					Expression nval=new CallExp(getDup(fe.val.loc,sc),fe.val.copy(),false,false);
					nval.loc=fe.val.loc;
					if(fe.val.type!=fe.var.type){
						nval=new TypeAnnotationExp(nval,fe.var.type,TypeAnnotationType.coercion);
						nval.loc=fe.val.loc;
					}
					auto r=new ForgetExp(nval,var);
					r.loc=fe.loc;
					return r;
				}
			}
			static if(language==silq) if(auto be=cast(ABinaryExp)statements[i]) if(isOpAssignExp(be)) if(auto id=cast(Identifier)unwrap(be.e1)) if(id.type&&id.type.isClassical()&&!hasExactInverse(be)){ // (e.g., `t*=c`, which loses the value for `c=0`)
				auto n=nameOf(id);
				if(recomputed[i]&&undone[i]){ // (the version before it, which the recomputation saves, replaces the one after it, see `oldVersions`)
					oldVersions[i]=[cast(Id[2])[n,freshName()]];
					auto r=new CompoundExp([]);
					r.loc=be.loc;
					return r;
				}
				if(needOld&&!innerAt(i,n)){ // (an enclosing block may recompute it from the version before it, see `NeedOld`)
					if(defer){ if(!needOld.vars.canFind(n)) needOld.vars~=n; } // (otherwise, it is reverted in place, see below)
					else{
						needOld.errors~=q(chain(only(n),blockedAt.joiner.filter!(m=>m!=n)).array,be.loc,"reversal of assignments not supported yet");
						auto r=statements[i].copy();
						r.setSemError();
						return r;
					}
				}
			}
			static if(language==silq) if(unsupported[i].length){
				if(needOld) needOld.errors~=q(chain(unsupported[i],blockedAt.joiner.filter!(m=>!unsupported[i].canFind(m))).array,statements[i].loc,redefinitionError);
				else sc.error(redefinitionError,statements[i].loc);
				auto r=statements[i].copy();
				r.setSemError();
				return r;
			}
			static if(language==silq) if(recomputed[i]&&undone[i]&&readsOld(statements[i])){
				auto lost=aliveAt[i].filter!(n=>!changed[i].canFind(n)&&!shadowed[i].canFind(n)&&lostBy(i,n)&&readEarlier(i,n)).array; // (the reversal of an earlier statement reads the version that the recomputation of a conditional loses, e.g., `v` for `if c { … } else { with { … } do { k+=1; for i in 0..2 { forget(v); v:=i; } forget(v); } }` after `xs[v+k]:=X(xs[v+k]);`: unlike that of a statement whose reversal does not read copies, see `preserved`, the reversal of the conditional does not receive it)
				if(lost.length){
					if(needOld) needOld.errors~=q(chain(lost,blockedAt.joiner.filter!(m=>!lost.canFind(m))).array,statements[i].loc,redefinitionError);
					else sc.error(redefinitionError,statements[i].loc);
					auto r=new ErrorExp();
					r.loc=statements[i].loc;
					r.setSemError();
					return r;
				}
			}
			static if(language==silq) if(!recomputed[i]&&!projections[i]){
				auto lost=changed[i].filter!(n=>before.canFind(n)).array; // (the reversal of the block receives the versions before it, see `before`, but the reversal of the statement would change them in place)
				if(lost.length){
					if(needOld) needOld.errors~=q(chain(lost,blockedAt.joiner.filter!(m=>!lost.canFind(m))).array,statements[i].loc,redefinitionError);
					else sc.error(redefinitionError,statements[i].loc);
					auto r=new ErrorExp();
					r.loc=statements[i].loc;
					r.setSemError();
					return r;
				}
			}
			static if(language==silq) if(projections[i]){
				auto kept=readAgain[i].filter!(n=>consumesVariable(projections[i],n)&&!(lossy[i].canFind(n)&&readsOld(statements[i]))).array; // (the recomputation of the classical part consumes the version that the reversal reads, see `readAgain`, unless the reversal reads a copy of it, see `lossyChanges`)
				if(kept.length){
					if(needOld) needOld.errors~=q(chain(kept,blockedAt.joiner.filter!(m=>!kept.canFind(m))).array,statements[i].loc,redefinitionError);
					else sc.error(redefinitionError,statements[i].loc);
					auto r=new ErrorExp(); // (not an empty block, which `mergeCompound` drops, nor a copy of the statement, whose analysis would define its variables again)
					r.loc=statements[i].loc;
					r.setSemError();
					return r;
				}
			}
			static if(language==silq) if(lossy[i].length){ // (e.g., `v:=2` after `forget(v)`, or `with { w:=1; } do { forget(v); v:=w+1; }`)
				if(recomputed[i]&&undone[i]){ // (the versions before it of the variables that it changes, which the recomputation saves, replace the ones after it, see `oldVersions`)
					oldVersions[i]=changed[i].map!(n=>cast(Id[2])[n,freshName()]).array;
					auto copy=recomputation(statements[i],sc);
					consumedBy[i]=changed[i].filter!(n=>!availableAfter(copy,n,!(redefined[i].canFind(n)&&aliveAt[i].canFind(n)&&!early[i]))).array; // (the kept version of a variable that it defines again is forgotten before it, see `redefined`, e.g., `v` for `forget(v); with { … } do { v:=w+1; … forget(v); }`, whose recomputation renames its own versions, see `recomputation`)
					auto r=new CompoundExp([]);
					r.loc=statements[i].loc;
					return r;
				}
				if(!(projections[i]&&readsOld(statements[i]))&&lossy[i].any!(n=>neededBefore(i,n))){ // (otherwise, its reversal recomputes them on copies, see below)
					auto vars=lossy[i].filter!(n=>!innerAt(i,n)).array;
					if(needOld&&vars.length) needOld.errors~=q(chain(vars,blockedAt.joiner.filter!(m=>!vars.canFind(m))).array,statements[i].loc,redefinitionError); // (an enclosing block may recompute them from the versions before it, see `NeedOld`)
					else sc.error(redefinitionError,statements[i].loc);
					auto r=statements[i].copy();
					r.setSemError();
					return r;
				}
			}
			static if(language==silq) if(auto be=cast(ABinaryExp)statements[i]) if(isOpAssignExp(be)) if(auto id=cast(Identifier)unwrap(be.e1)){
				auto n=nameOf(id);
				if(id.type&&id.type.isClassical()&&(defer||hasExactInverse(be))&&(iota(i).any!(j=>readsBesidesUpdates(statements[j],n))||!copied.canFind(n)&&!statements[0..i].any!(t=>definedNames(t).canFind(n)))){ // (`t=(t-c) coerce !ℕ` for `t+=c`: the reversals of earlier statements see the type from before the update, also those in enclosing blocks)
					Expression val=null;
					if(cast(AddAssignExp)be) val=new SubExp(be.e1.copy(),be.e2.copy());
					else if(cast(SubAssignExp)be) val=new AddExp(be.e1.copy(),be.e2.copy());
					else if(cast(MulAssignExp)be) val=new DivExp(be.e1.copy(),be.e2.copy());
					else if(cast(DivAssignExp)be) val=new MulExp(be.e1.copy(),be.e2.copy());
					if(val){
						val.loc=be.loc;
						auto cv=new TypeAnnotationExp(val,id.type,TypeAnnotationType.coercion);
						cv.loc=be.loc;
						auto r=new AssignExp(be.e1.copy(),cv);
						r.loc=be.loc;
						return r;
					}
				}
			}
			auto projected=projections[i]?chain(definedNames(projections[i]),projectionChanges[i].filter!(n=>availableAfter(projections[i],n)&&!availableAfter(statements[i],n))).array:undone[i]?definedNames(statements[i]):[]; // (checked by the reversed statement; also the versions after the classical part of the variables that it keeps although the statement forgets them, which the reversed statement changes back, e.g., `k` for `if c { … } else { (xs,k):=let{ k-=1; … } in (xs,k); k+=2; }` at the last use of `k`, see `readsBeforeDefining`)
			static if(language==silq) if(undone[i]){
				if(!copies[i]) copies[i]=recomputation(statements[i],sc);
				projected~=changed[i].filter!(n=>availableAfter(copies[i],n)&&!availableAfter(statements[i],n)).array; // (as for a projection, e.g., `w` for `with { … } do { (s,w):=(dup(n),w); w+=t+s; }` at the last use of `w`)
			}
			static if(language==silq) if(!projections[i]&&!recomputed[i]) projected~=definedNames(statements[i]).filter!(n=>excluded.canFind(n)).array; // (the reversal of a later statement that changes it in place gives back the version after it, e.g., `v` for `with { … } do { v:=u*2; xs[u]:=X(xs[u]); }` before `v+=j`, see `excluded`)
			NeedOld need;
			auto nerrors=sc.handler.nerrors;
			auto r=reverseStatement(statements[i],sc,unchecked,noImplicitDup,hoistClassical,defer,givenAfter(i)~projected,aliveFor(i),null,&need);
			static if(language==silq) if((projections[i]||recomputed[i]&&undone[i])&&readsOld(statements[i])){ // (also a recomputed statement that is reversed in place, e.g., a loop that a conditional in it changes, for earlier statements that read the versions before it)
				auto pc=projections[i]?chain(projectionChanges[i],definedNames(projections[i])).array:chain(changed[i],definedNames(statements[i])).array;
				Id[] old;
				if(chain(need.vars,need.errors.map!(e=>e[0]).joiner).any!(n=>pc.canFind(n))||lossy[i].length) foreach(n;pc) if(!old.canFind(n)) old~=n; // (all of them, as the reversal of the statement may need more once it recomputes some, e.g., an update that it would otherwise reverse first; also for changes that it cannot reverse in place, see `lossyChanges`)
				static if(language==silq) if(projections[i]) foreach(n;aliveAt[i]) if(!old.canFind(n)&&!changed[i].canFind(n)&&!shadowed[i].canFind(n)&&consumesVariable(projections[i],n)&&neededBefore(i,n)) old~=n; // (also the versions before it that the projection forgets or moves, if it defines them again only for itself, which do not count as changes, see `changedNames`, e.g., `v` for `if c { xs[0]:=X(xs[0]); k+=1; } else { forget(v); v:=2; }` after `xs[v]:=X(xs[v]);`)
				if(old.length&&sc.handler.nerrors==nerrors){ // (versions before the statement that the projection changes: the reversal of the statement recomputes them on copies)
					oldVersions[i]=old.map!(n=>cast(Id[2])[n,freshName()]).array;
					if(projections[i]) consumedBy[i]=old.filter!(n=>!availableAfter(projections[i],n)).array; // (e.g., `w` for `if c { … } else { with { … } do { forget(w); w:=2; … } }`, after which it is available only if `c` holds)
					need=NeedOld.init;
					r=reverseStatement(statements[i],sc,unchecked,noImplicitDup,hoistClassical,defer,givenAfter(i)~projected,aliveFor(i),oldVersions[i],&need);
				}
			}
			if(needOld) foreach(n;need.vars) if(!innerAt(i,n)&&!needOld.vars.canFind(n)) needOld.vars~=n;
			foreach(e;need.errors){ // (deferred if an enclosing block may resolve it, also through the other needs of this block)
				auto vars=e[0].filter!(n=>!innerAt(i,n)).array;
				if(needOld) foreach(n;blockedAt.joiner) if(!vars.canFind(n)) vars~=n;
				if(needOld&&vars.length) needOld.errors~=q(vars,e[1],e[2]);
				else sc.error(e[2],e[1]);
			}
			return r;
		}
		Expression reversed(size_t i){ // (with the copies of the variables of the condition or range, see `headerChanges`)
			if(headerChanges[i].length&&!saves[i].length){
				auto loc=headers(statements[i])[0].loc;
				Id[] missing; // (variables of enclosing blocks whose versions before the block may allow the reversal to recompute the classical part of the statement, also those that other statements of the block need)
				foreach(n;chain(headerChanges[i],changed[i],changedAfter[i].filter!(n=>reads(statements[i],n)),blockedAt.joiner)) if(!hoistedAll.canFind(n)&&!innerAt(i,n)&&!missing.canFind(n)) missing~=n;
				if(needOld&&missing.length) needOld.errors~=q(missing,loc,headerChangeError); // (the reversal of an enclosing block may resolve it)
				else sc.error(headerChangeError,loc);
				auto r=statements[i].copy();
				r.setSemError();
				return r;
			}
			if(saves[i].length){
				auto r=reversal(i);
				foreach(h;headers(r)) walkIdentifiers(h,(Identifier id){ if(!id.meaning) foreach(j,n;headerChanges[i]) if(id.id==n) id.id=saves[i][j]; });
				return r;
			}
			return reversal(i);
		}
		Expression[] narrowed(size_t i){ // (with conversions to the types before the statement, see `narrowing`)
			auto r=[reversed(i)];
			static if(language==silq) if(!oldVersions[i].length) r~=statementNarrowings(statements[i],changed[i].filter!(n=>local.canFind(n)||outer.canFind(n)).array); // (not of a variable of an enclosing block whose version before the block its reversal does not see, e.g., `v3` for `for i in 0..3 { forget(v3); v3:=i+v1; v2+=1; }` after `v3:=1;` in the body of a `with` statement that the reversal recomputes and reverts, after which `v3` is not available, see `lostBy`: no reversal reads that version)
			return r;
		}
		static if(language==silq) foreach(i;0..statements.length) if(recomputed[i]&&!undone[i]&&!early[i]){ // (a statement that the reversal only recomputes, whose recomputation loses the version that the reversal of an earlier statement reads, e.g., `v` for `with { … } do { for i in 0..2 { forget(v); v:=i+j; k+=v; } forget(v); }` after `xs[v]:=X(xs[v]);`, see `lostBy`)
			auto lost=aliveAt[i].filter!(n=>!changed[i].canFind(n)&&!shadowed[i].canFind(n)&&lostBy(i,n)&&readEarlier(i,n)).array;
			if(lost.length){
				if(needOld) needOld.errors~=q(chain(lost,blockedAt.joiner.filter!(m=>!lost.canFind(m))).array,statements[i].loc,redefinitionError);
				else sc.error(redefinitionError,statements[i].loc);
			}
		}
		Expression[] undoneFirst=iota(statements.length).retro.filter!(i=>undoFirst[i]).map!narrowed.joiner.array;
		Expression[] quantumStatements;
		static if(language==silq) bool[Id] dropped; // (versions that the recomputations of later statements keep, which the reversal of a statement defines again for its own variables, e.g., `v` for `with { … } do { v:=u+1; xs[v]:=X(xs[v]); forget(v); }` before `v:=2;`: the reversals of earlier statements do not see them)
		foreach_reverse(i;0..statements.length){
			if(recomputed[i]&&!undone[i]||undoFirst[i]||dead[i]) continue;
			static if(language==silq){
				auto after=i+1<statements.length?aliveAt[i+1]:alive;
				foreach(n;definedWithin(statements[i])) if(!(n in dropped)&&!after.canFind(n)&&iota(i+1,statements.length).any!(k=>recomputed[k]&&!undone[k]&&definedNames(statements[k]).canFind(n)&&!movedIntoItself(statements[k],n))){
					dropped[n]=true;
					auto var=new Identifier(n);
					var.loc=statements[i].loc;
					auto fe=new ForgetExp(var,null);
					fe.loc=statements[i].loc;
					quantumStatements~=fe;
				}
			}
			static if(language==silq){
				auto saved=saving[i].map!(n=>freshName()).array;
				foreach(k,n;saving[i]){
					auto loc=statements[i].loc;
					auto lhs=new Identifier(saved[k]),var=new Identifier(n),fvar=new Identifier(n);
					lhs.loc=var.loc=fvar.loc=loc;
					auto rhs=new CallExp(getDup(loc,sc),var,false,false);
					rhs.loc=loc;
					auto cpy=new DefineExp(lhs,rhs);
					cpy.loc=loc;
					auto fe=new ForgetExp(fvar,null);
					fe.loc=loc;
					quantumStatements~=[cast(Expression)cpy,fe];
				}
				foreach(o;preserved[i]){
					if(projections[i]&&availableAfter(projections[i],o[0])){ // (the projection keeps a version of its own, e.g., `v` for `with { … } do { for i in 0..2 { forget(v); v:=i; } k+=1; xs[0]:=X(xs[0]); forget(v); }` after `xs[v]:=X(xs[v]);`, see `classicalPart`)
						auto var=new Identifier(o[0]);
						var.loc=statements[i].loc;
						auto fe=new ForgetExp(var,null);
						fe.loc=statements[i].loc;
						quantumStatements~=fe;
					}
					auto lhs=new Identifier(o[0]),rhs=new Identifier(o[1]);
					lhs.loc=rhs.loc=statements[i].loc;
					auto de=new DefineExp(lhs,rhs);
					de.loc=statements[i].loc;
					quantumStatements~=de;
				}
			}
			quantumStatements~=narrowed(i);
			static if(language==silq) foreach(o;oldVersions[i]){ // (the version before the statement replaces the one after it)
				auto loc=statements[i].loc;
				auto var=new Identifier(o[0]),lhs=new Identifier(o[0]),rhs=new Identifier(o[1]);
				var.loc=lhs.loc=rhs.loc=loc;
				auto fe=new ForgetExp(var,null);
				fe.loc=loc;
				auto de=new DefineExp(lhs,rhs);
				de.loc=loc;
				if(!consumedBy[i].canFind(o[0])) quantumStatements~=fe;
				quantumStatements~=de;
			}
			static if(language==silq) foreach(k,n;saving[i]){
				auto loc=statements[i].loc;
				auto lhs=new Identifier(n),rhs=new Identifier(saved[k]);
				lhs.loc=rhs.loc=loc;
				auto de=new DefineExp(lhs,rhs);
				de.loc=loc;
				quantumStatements~=de;
			}
		}
		Expression[] classicalStatements;
		foreach(i;0..statements.length){
			static if(language==silq) foreach(o;chain(oldVersions[i],preserved[i])){
				auto loc=statements[i].loc;
				auto lhs=new Identifier(o[1]),var=new Identifier(o[0]);
				lhs.loc=var.loc=loc;
				auto rhs=new CallExp(getDup(loc,sc),var,false,false);
				rhs.loc=loc;
				auto cpy=new DefineExp(lhs,rhs);
				cpy.loc=loc;
				classicalStatements~=cpy;
			}
			static if(language==silq) foreach(j,n;saves[i]){
				auto lhs=new Identifier(n),var=new Identifier(headerChanges[i][j]);
				lhs.loc=var.loc=headers(statements[i])[0].loc;
				auto rhs=new CallExp(getDup(var.loc,sc),savedValues[i].length?reevaluationCopy(savedValues[i][j]):var,false,false);
				rhs.loc=var.loc;
				auto cpy=new DefineExp(lhs,rhs);
				cpy.loc=var.loc;
				classicalStatements~=cpy;
			}
			static if(language==silq) if(recomputed[i]&&!early[i]||projections[i]) foreach(n;redefined[i]) if(aliveAt[i].canFind(n)){ // (the version that the recomputation keeps, see `redefined`)
				auto var=new Identifier(n);
				var.loc=statements[i].loc;
				auto fe=new ForgetExp(var,null);
				fe.loc=statements[i].loc;
				classicalStatements~=fe;
			}
			static if(language==silq){
				if(recomputed[i]&&!early[i]) classicalStatements~=renamedLocals(recomputation(statements[i],sc),shadowed[i]);
				else if(projections[i]) classicalStatements~=renamedLocals(projections[i],shadowed[i]);
			}else{
				if(recomputed[i]&&!early[i]) classicalStatements~=recomputation(statements[i],sc);
				else if(projections[i]) classicalStatements~=projections[i];
			}
		}
		auto earlyStatements=iota(statements.length).filter!(i=>early[i]).map!(i=>recomputation(statements[i],sc)).array;
		return earlyStatements~undoneFirst~classicalStatements~middle~quantumStatements;
	}
	return chain(middle,statements.retro.map!(s=>reverseStatement(s,sc,unchecked,noImplicitDup,false,defer))).array;
}

Expression stripElaborationCoercions(Expression e){ // re-derive pattern coercions against current types in the adjoint
	if(auto tae=cast(TypeAnnotationExp)e){
		auto inner=stripElaborationCoercions(tae.e);
		if(tae.fromElaboration){
			inner.loc=tae.loc;
			return inner;
		}
		if(tae.unresolvedT){ // re-resolve wildcards against current types
			tae.t=tae.unresolvedT.copy();
			tae.unresolvedT=null;
		}
		tae.e=inner;
		return tae;
	}
	if(auto ce=cast(CatExp)e){
		ce.e1=stripElaborationCoercions(ce.e1);
		ce.e2=stripElaborationCoercions(ce.e2);
	}
	if(auto te=cast(TupleExp)e) foreach(ref x;te.e) x=stripElaborationCoercions(x);
	if(auto ve=cast(VectorExp)e) foreach(ref x;ve.e) x=stripElaborationCoercions(x);
	return e;
}

LetExp functionValue(FunctionDef fd){ // (the value that a function definition defines, `let { def fresh(…)…; } in fresh`)
	auto fresh=freshName();
	Expression.CopyArgs cargs={rename: new Expression.CopyArgs.Rename(fd, fresh) };
	auto nfd=fd.copy(cargs);
	if(nfd.body_&&!nfd.params.any!(p=>p.name&&p.name.id==fd.name.id)){ // (the recursive references that the renaming misses: those of a definition that is not analyzed yet, and those within lambdas, which are copied from their original definitions)
		foreach(id;nfd.body_.freeIdentifiers) if(id.id==fd.name.id) id.id=fresh;
		import ast.substitute:updateLambdaDefinitions;
		updateLambdaDefinitions(nfd.body_);
	}
	auto nname=new Identifier(fresh);
	nname.loc=fd.name.loc;
	nfd.name=nname;
	auto stm=new CompoundExp([cast(Expression)nfd]);
	stm.loc=fd.loc;
	auto res=new Identifier(fresh);
	res.loc=fd.loc;
	auto r=new LetExp(stm,res);
	r.loc=fd.loc;
	return r;
}

Expression reverseStatement(Expression e,Scope sc,bool unchecked,bool noImplicitDup,bool hoistClassical=false,bool defer=false,Id[] given=null,Id[] alive=null,Id[2][] old=null,NeedOld* needOld=null){ // (`old`: the copies of the versions of variables before the statement, on copies of which its reversal recomputes them; `needOld`: the variables whose versions before the statement its reversal would need, see `NeedOld`)
	enum flags=LowerDefineFlags.createFresh|LowerDefineFlags.reverseMode;
	if(!e) return e;
	Expression error(){
		auto res=e.copy();
		res.setSemError();
		return res;
	}
	if(auto ce=cast(CallExp)e){
		if(string prim=isPrimitiveCall(ce)){
			switch(prim) {
				case null:
				default:
					break;
				case "print","dump":
					return e.copy();
			}
		}
		auto te=new TupleExp([]);
		te.type=unit;
		te.loc=ce.loc;
		static if(language==silq){
			if(auto id=cast(Identifier)unwrap(ce.e)){
				if(isBuiltIn(id)){
					switch(id.name){
						case "__show","__query":
							return lowerDefine!flags(te,te,ce.loc,sc,unchecked,noImplicitDup,defer);
						default:
							break;
					}
				}
			}
		}
		return lowerDefine!flags(ce,te,ce.loc,sc,unchecked,noImplicitDup,defer);
	}
	if(auto ce=cast(CompoundExp)e){
		static if(language==silq) if(ce.loweredFrom) return reverseStatement(ce.loweredFrom,sc,unchecked,noImplicitDup,hoistClassical,defer,null,null,old,needOld);
		auto hoist=hoistClassical||ce.blscope_&&!ce.isSemError(); // (classical locals of a nested block are recomputed in its reversal)
		Id[] excludedOld;
		static if(language==silq) auto stmts=ce.blscope_?uncomputationOf(ce.entryUncomputation,ce.blscope_.forgottenVarsOnEntry,ce.loc)~ce.s~uncomputationOf(ce.exitUncomputation,ce.blscope_.forgottenVars,ce.loc):ce.s; // (the reversal recomputes the quantum variables that it forgets, see `resolveForgets`)
		else auto stmts=ce.s;
		auto res=new CompoundExp(reverseStatements(stmts,[],sc,unchecked,noImplicitDup,hoist,defer,given.filter!(n=>!old.canFind!(o=>o[0]==n)).array,alive,old.map!(o=>o[0]).array,&excludedOld,forgottenNames(ce),needOld)); // (it recomputes the variables in `old` on copies, also those whose versions after it the reversal received)
		res.loc=ce.loc;
		static if(language==silq) if(old.length) res.s=copiesOf(res,old,excludedOld,ce.loc,sc)~res.s;
		foreach(s;res.s) propErr(s,res);
		return res;
	}
	if(auto ite=cast(IteExp)e){
		auto then=cast(CompoundExp)reverseStatement(ite.then,sc,unchecked,noImplicitDup,hoistClassical,defer,given,alive,old,needOld);
		assert(!!then);
		auto othw=cast(CompoundExp)reverseStatement(ite.othw,sc,unchecked,noImplicitDup,hoistClassical,defer,given,alive,old,needOld);
		assert(!!othw==!!ite.othw);
		static if(language==silq){ // (the reversal of a branch starts from the version that the merge widens, see `narrowing`)
			auto names=changedNames(ite).filter!(n=>!old.canFind!(o=>o[0]==n)).array; // (not of the variables whose versions before the statement the reversals of the branches recompute on copies, which they read instead, see `copiesOf`)
			then.s=branchNarrowings(ite,ite.then,names,given)~then.s;
			if(othw) othw.s=branchNarrowings(ite,ite.othw,names,given)~othw.s;
		}
		auto cond=reevaluationCopy(ite.cond);
		if(old.length) walkIdentifiers(cond,(Identifier id){ if(!id.meaning) foreach(o;old) if(id.id==o[0]) id.id=o[1]; }); // (the condition reads the versions before the statement)
		auto res=new IteExp(cond,then,othw);
		res.loc=ite.loc;
		propErr(then,res);
		if(othw) propErr(othw,res);
		return res;
	}
	if(auto we=cast(WithExp)e){
		Expression.CopyArgs cargs;
		Id[] keep; // (the variables that the transformation defines or that its inverse restores)
		static if(language==silq){
			foreach(x;we.trans.subexpressions) if(cast(DefineExp)x) keep~=definedNames(x);
			if(we.itrans) keep~=definedNames(we.itrans);
		}
		static if(language==silq) cargs.mapExp=(Expression x,ref Expression.CopyArgs args){ // (a lowered loop is copied as the loop, which is lowered again)
			if(auto ce=cast(CompoundExp)x){
				if(ce.loweredFrom) return ce.loweredFrom.copy(args);
				bool outerForget(Expression t){ // (e.g., at the last use of a variable of the enclosing block: the reversals of earlier statements may still read it)
					auto fe=cast(ForgetExp)t;
					if(!fe||fe.val||!fe.var.type||!fe.var.type.isClassical()) return false;
					foreach(y;fe.var.subexpressions) if(auto id=cast(Identifier)y) if(keep.canFind(nameOf(id))) return false;
					return true;
				}
				if(ce.s.any!outerForget){
					auto r=new CompoundExp(ce.s.filter!(t=>!outerForget(t)).map!(t=>t.copy(args)).array);
					r.loc=ce.loc;
					return cast(Expression)r;
				}
			}
			if(auto id=cast(Identifier)x) if(id.moved&&!keep.canFind(nameOf(id))){ // (as above)
				auto r=id.copy();
				r.moved=false;
				return cast(Expression)r;
			}
			return null;
		};
		auto trans=we.trans.copy(cargs);
		auto bdy=cast(CompoundExp)reverseStatement(we.bdy,sc,unchecked,noImplicitDup,hoistClassical,defer,given,alive);
		assert(!!bdy);
		static if(language==silq){ // (the classical variables of its own that the body defines, but whose recomputations the reversal of the body keeps: it forgets them at its end, as the body does not have a scope of its own, e.g., `v` for `with { … } do { v:=w+1; xs[w%4]:=X(xs[w%4]); u:=move(v); }`, also if the body leaves them available, but the reversal does not receive them, e.g., `v` for `with { … } do { xs[2]:=X(xs[2]); v:=u*2; }` before `t:=v+j;`, whose value no statement uses, such that the reversal of an earlier statement may define `v` again; not versions of earlier ones, nor ones whose versions before it the reversal of the enclosing block recomputes, which the reversal of the body restores, e.g., `v` for `w:=move(v); with { … } do { v:=u+1; … forget(v); }`)
			Id[] leftover;
			Expression[] restored; // (the definitions of the transformations of nested `with` statements, whose inverses restore their variables, which `availableAfter` does not see: they count only where the body does not leave them available)
			foreach(x;we.bdy.subexpressions) if(auto iwe=cast(WithExp)x){
				foreach(y;iwe.trans.subexpressions) if(cast(DefineExp)y) restored~=y;
				if(iwe.itrans) foreach(y;iwe.itrans.subexpressions) if(cast(DefineExp)y) restored~=y;
			}
			foreach(x;we.bdy.subexpressions) if(auto de=cast(DefineExp)x) foreach(id;definedIdentifiers(de)){
				auto n=nameOf(id);
				if(id.type&&id.type.isClassical()&&!leftover.canFind(n)&&!keep.canFind(n)&&(!restored.any!(y=>y is x)||!availableAfter(we.bdy,n))&&!readsBeforeDefining(we.bdy,n,true)&&!alive.canFind(n)&&availableAfter(bdy,n,false)) leftover~=n;
			}
			if(leftover.length){
				Expression[] forgets;
				foreach(n;leftover){
					auto var=new Identifier(n);
					var.loc=we.loc;
					auto fe=new ForgetExp(var,null);
					fe.loc=we.loc;
					forgets~=fe;
				}
				auto nbdy=new CompoundExp(bdy.s~forgets);
				nbdy.loc=bdy.loc;
				bdy=nbdy;
			}
		}
		auto res=new WithExp(trans,bdy);
		res.isIndices=we.isIndices;
		if(we.itrans&&we.isIndices) res.itrans=we.itrans.copy(cargs); // (otherwise, the inverse of the copied transformation is derived again, for the context of the reversal)
		res.loc=we.loc;
		propErr(trans,res);
		propErr(bdy,res);
		return res;
	}
	if(auto ret=cast(ReturnExp)e){
		sc.error("reversing early returns not supported yet",ret.loc);
		return error();
	}
	if(auto fd=cast(FunctionDef)e){
		if(defer){ // TODO
			sc.error("cannot reverse function definition within `let` pattern",fd.loc);
			return error();
		}
		auto captureAnnotation=fd.ftype?fd.ftype.captureAnnotation:fd.getCaptureAnnotation();
		if(captureAnnotation>CaptureAnnotation.const_){
			sc.error("reversal of `moved` quantum variable capturing not supported yet",fd.loc);
			return error();
		}
		assert(!!fd.name);
		auto gid=new Identifier(fd.name.name);
		gid.loc=fd.loc;
		if(captureAnnotation!=CaptureAnnotation.const_){ // (no quantum captures, nothing to uncompute)
			auto res=new ForgetExp(gid,null);
			res.loc=fd.loc;
			return res;
		}
		auto res=new ForgetExp(gid,functionValue(fd));
		res.isStatement=true;
		res.loc=fd.loc;
		return res;
	}
	// TODO: DatDecl?
	if(auto ce=cast(CommaExp)e) assert(0);
	if(auto de=cast(DefineExp)e){
		if(de.isSwap) return de.copy(); // TODO: ok?
		static if(language==silq) if(!defer) if(auto le=cast(LambdaExp)unwrap(de.e2)) if(auto id=cast(Identifier)unwrap(de.e1)){
			auto captureAnnotation=le.fd.ftype?le.fd.ftype.captureAnnotation:le.fd.getCaptureAnnotation();
			if(captureAnnotation==CaptureAnnotation.none){ // (no quantum captures, nothing to uncompute)
				auto nid=new Identifier(nameOf(id));
				nid.loc=id.loc;
				auto res=new ForgetExp(nid,null);
				res.loc=de.loc;
				return res;
			}
		}
		Expression nrhs=stripElaborationCoercions(de.e1.copy()); // re-derive pattern coercions against current types
		if(de.e1.type!=de.e2.type){
			nrhs=new TypeAnnotationExp(nrhs,de.e2.type,TypeAnnotationType.coercion);
			nrhs.loc=de.e1.loc;
			nrhs.type=de.e2.type;
		}
		return lowerDefine!flags(de.e2,nrhs,de.loc,sc,unchecked,noImplicitDup,defer,old,needOld);
	}
	if(auto ae=cast(AssignExp)e){
		sc.error("reversal of functions containing assignments not supported yet",ae.loc);
		return error();
	}
	if(isOpAssignExp(e)){
		auto be=cast(ABinaryExp)e;
		assert(!!be);
		if(!defer){ // no type information is available for unanalyzed statements
			assert(!!be.e2.type);
			if(be.e1.type.isClassical()){ // (reverted in place, as in the reversal of a `let` expression, see `reversal` in `reverseStatements`)
				if(!hasExactInverse(be)){
					sc.error("reversal of assignments not supported yet",be.loc);
					return error();
				}
			}else if(!isInvertibleOpAssignExp(be)){
				if(be.e2.type.hasClassicalComponent()){
					sc.error("reversal of assignments not supported yet",be.loc);
					return error();
				}
				sc.error("reversal of implicit forgets not supported yet",be.loc);
				return error();
			}
		}
		if(auto ae=cast(AddAssignExp)e){
			auto res=new SubAssignExp(ae.e1.copy(),ae.e2.copy());
			res.loc=ae.loc;
			return res;
		}
		if(auto ae=cast(SubAssignExp)e){
			auto res=new AddAssignExp(ae.e1.copy(),ae.e2.copy());
			res.loc=ae.loc;
			return res;
		}
		if(auto me=cast(MulAssignExp)e){
			auto r=new DivAssignExp(me.e1.copy(),me.e2.copy());
			r.loc=me.loc;
			return r;
		}
		if(auto de=cast(DivAssignExp)e){
			auto r=new MulAssignExp(de.e1.copy(),de.e2.copy());
			r.loc=de.loc;
			return r;
		}
		if(auto ae=cast(CatAssignExp)e){
			if(!cast(Identifier)ae.e1){
				sc.error("reversal of concatenation to non-identifier not supported yet",ae.loc);
				return error();
			}
			if(defer&&!ae.e2.knownLength(true)){ // TODO
				sc.error("cannot reverse `~=` of unknown length within `let` pattern",ae.loc);
				return error();
			}
			auto nlhs=new CatExp(ae.e1.copy(),ae.e2);
			nlhs.loc=ae.loc;
			nlhs.type=ae.e1.type;
			auto nrhs=ae.e1;
			return lowerDefine!flags(nlhs,nrhs,ae.loc,sc,unchecked,noImplicitDup,defer);
		}
		static if(language==silq) if(auto le=blockUpdate(e)) return lowerLetDefine(le,null,be.loc,sc,old,needOld,be);
		if(auto ae=cast(BitXorAssignExp)e) return reevaluationCopy(ae);
		if(auto ae=cast(XorAssignExp)e) return reevaluationCopy(ae);
		sc.error("reversal not supported yet",e.loc);
		return error();
	}
	static if(language==silq) Expression iterationsFromOld(Expression loop,CompoundExp lbdy,Identifier var,ForRange rng,Expression num){ // (each reversed iteration recomputes the versions before it from the versions before the loop, on copies, as its reversal reads them, see `NeedOld`)
		void renameOld(Expression x){ walkIdentifiers(x,(Identifier id){ if(!id.meaning) foreach(o;old) if(id.id==o[0]) id.id=o[1]; },true); }
		auto p=projection(loop,sc,changedNames(loop).filter!(n=>!old.canFind!(o=>o[0]==n)).array);
		auto pbdy=cast(ForExp)p?(cast(ForExp)p).bdy:cast(RepeatExp)p?(cast(RepeatExp)p).bdy:null;
		if(!pbdy) return null;
		auto iold=old.map!(o=>cast(Id[2])[o[0],freshName()]).array;
		auto bdy=cast(CompoundExp)reverseStatement(lbdy,sc,unchecked,noImplicitDup,hoistClassical,defer,null,null,iold,needOld);
		assert(!!bdy);
		Expression[] s;
		foreach(k,o;old){
			auto lhs=new Identifier(iold[k][1]),src=new Identifier(o[1]);
			lhs.loc=src.loc=loop.loc;
			auto rhs=new CallExp(getDup(loop.loc,sc),src,false,false);
			rhs.loc=loop.loc;
			auto cpy=new DefineExp(lhs,rhs);
			cpy.loc=loop.loc;
			s~=cpy;
		}
		walkIdentifiers(pbdy,(Identifier id){ if(!id.meaning) foreach(o;iold) if(id.id==o[0]) id.id=o[1]; },true);
		if(var&&var.name=="_") var=null;
		auto it=new Identifier(var?var.id:freshName());
		it.loc=var?var.loc:loop.loc;
		auto cur=new Identifier(it.id);
		cur.loc=it.loc;
		Expression first; // (the iterations before the current one)
		if(rng){
			auto nvar=new Identifier(freshName());
			nvar.loc=it.loc;
			if(var) walkIdentifiers(pbdy,(Identifier id){ if(!id.meaning&&id.id==var.id) id.id=nvar.id; },true);
			auto left=rng.left.copy(),step=rng.step?rng.step.copy():null;
			renameOld(left);
			if(step) renameOld(step);
			first=new ForExp(nvar,null,ForAggregate(ForRange(rng.leftExclusive,left,step,true,cur)),pbdy);
		}else first=new RepeatExp(cur,pbdy);
		first.loc=loop.loc;
		s~=first;
		auto nbdy=new CompoundExp(s~bdy.s);
		nbdy.loc=bdy.loc;
		ForRange range;
		if(rng) range=rng.copyReversed();
		else{
			auto zero=constantExp(0);
			zero.loc=num.loc;
			range=ForRange(false,zero,null,true,num.copy()).copyReversed();
		}
		range.componentsImpl((Expression x){ renameOld(x); return 0; });
		auto res=new ForExp(it,null,ForAggregate(range),nbdy);
		res.loc=loop.loc;
		propErr(bdy,res);
		return res;
	}
	if(auto fe=cast(ForExp)e){
		auto aggrRev=fe.aggr.copyReversed();
		if(!aggrRev){
			sc.error("reversal of aggregate not supported yet",fe.aggr.loc);
			return error();
		}
		static if(language==silq) if(old.length&&!fe.pattern) if(auto r=iterationsFromOld(fe,fe.bdy,fe.var,fe.aggr.isRange(),null)) return r;
		auto bdy=cast(CompoundExp)reverseStatement(fe.bdy,sc,unchecked,noImplicitDup,hoistClassical,defer,null,null,null,needOld);
		assert(!!bdy);
		auto res=new ForExp(fe.var?fe.var.copy():null,fe.pattern?fe.pattern.copy():null,aggrRev,bdy);
		res.loc=fe.loc;
		propErr(bdy,res);
		return res;
	}
	if(auto we=cast(WhileExp)e){
		sc.error("reversal of while loops not supported yet",we.loc);
		return error();
	}
	static if(language==silq) if(auto dw=cast(DoWhileExp)e){
		sc.error("reversal of do-while loops not supported yet",dw.loc);
		return error();
	}
	if(auto re=cast(RepeatExp)e){
		static if(language==silq) if(old.length) if(auto r=iterationsFromOld(re,re.bdy,null,ForRange.init,re.num)) return r;
		auto bdy=cast(CompoundExp)reverseStatement(re.bdy,sc,unchecked,noImplicitDup,hoistClassical,defer,null,null,null,needOld);
		assert(!!bdy);
		auto res=new RepeatExp(re.num.copy(),bdy);
		res.loc=re.loc;
		propErr(bdy,re);
		return res;
	}
	if(auto oe=cast(ObserveExp)e) enforce(0);
	if(auto oe=cast(CObserveExp)e) enforce(0);
	if(auto ae=cast(AssertExp)e) return reevaluationCopy(ae);
	if(auto fe=cast(ForgetExp)e){
		auto tpl=new TupleExp([]);
		tpl.type=unit;
		tpl.loc=fe.loc;
		return lowerDefine!flags(fe,tpl,fe.loc,sc,unchecked,noImplicitDup,defer);
	}
	sc.error("reversal unsupported",e.loc);
	return error();
}

