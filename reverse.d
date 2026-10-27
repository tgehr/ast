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
			nlhs=olhs.copy();
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
	static if(reverseMode){
		if(!noImplicitDup&&cast(Identifier)olhs&&olhs.type&&olhs.type.isClassical()){
			lhs.implicitDup=true;
			(cast(Identifier)lhs).moved=false; // (the classical value is checked, it remains available)
		}
	}
	static if(language==silq){
		if(auto le=cast(LetExp)olhs){
			if(!le.isForward(true))
				return res=lowerLetDefine(le,rhs,loc,sc,old,needOld);
		}
	}
	if(defer&&!cast(ForgetExp)olhs){
		return res=new DefineExp(olhs.copy(),rhs); // (keeps implicit duplications of analyzed statements)
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
		auto newLhs=new TupleExp(vec.copy().e);
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
	if(cast(Identifier)olhs?isLiftedBuiltIn(olhs):isLiftedBuiltIn(lhs)) return forget();
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
					return lowerDefine!flags(tae.e,newRhs,loc,sc,unchecked,noImplicitDup);
				}else return lowerDefine!flags(tae.e,orhs,loc,sc,unchecked,noImplicitDup);
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
		return lowerDefine!flags(tae.e,newRhs,loc,sc,unchecked,noImplicitDup);
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
			Expression nval=new CallExp(dup,fe.val.copy(),false,false);
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
			auto thenlhs=ite.then.s[0];
			auto othwlhs=ite.othw.s[0];
			auto dthen=lowerDefine!(flags|LowerDefineFlags.createFresh)(thenlhs,tmp,thenlhs.loc,sc,unchecked,noImplicitDup);
			auto dothw=lowerDefine!(flags|LowerDefineFlags.createFresh)(othwlhs,tmp,othwlhs.loc,sc,unchecked,noImplicitDup);
			auto cond=createFresh?ite.cond.copy():ite.cond;
			auto blthen=cast(CompoundExp)dthen;
			if(!blthen) blthen=new CompoundExp([dthen]);
			auto blothw=cast(CompoundExp)dothw;
			if(!blothw) blothw=new CompoundExp([dothw]);
			auto nite=new IteExp(cond,blthen,blothw);
			nite.loc=ite.loc;
			return res=new CompoundExp([d1,nite]);
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
Expression lowerLetDefine(LetExp le,Expression orhs,Location loc,Scope sc,Id[2][] old=null,NeedOld* needOld=null)in{
	assert(!le.isForward(true));
}do{
	enum unchecked=false,noImplicitDup=true;
	// let-pattern bodies are not analyzed; defer lowering of flipped defines to semantic analysis
	auto hoist=le.s.isSemCompleted(); // (the classical locals of an analyzed `let` are recomputed, as for a nested block, and the received values are checked against them)
	Expression mlhs=le.e.copy(),mrhs=orhs;
	if(hoist) if(auto lt=cast(TupleExp)unwrap(le.e)) if(auto rt=cast(TupleExp)orhs) if(lt.length==rt.length){ // (without the classical variables of the enclosing block that it returns, e.g., `k` in `(y,k):=let { k+=1; … } in (z,k)`: the received version is the current one, which the reversal changes in place)
		Expression[] ls,rs;
		foreach(i;0..lt.length){
			auto li=cast(Identifier)lt.e[i],ri=cast(Identifier)rt.e[i];
			if(li&&ri&&li.type&&li.type.isClassical()&&nameOf(li)==nameOf(ri)&&!le.s.s.map!definedNames.joiner.canFind(nameOf(li))) continue;
			ls~=lt.e[i].copy();
			rs~=rt.e[i];
		}
		if(ls.length&&ls.length<lt.length){
			Expression tuple(Expression[] es,Location l){
				if(es.length==1) return es[0];
				auto tpl=new TupleExp(es);
				tpl.loc=l;
				return tpl;
			}
			mlhs=tuple(ls,le.e.loc);
			mrhs=tuple(rs,orhs.loc);
		}
	}
	auto def=new DefineExp(mlhs,mrhs);
	def.loc=loc;
	Id[] copied,excludedCopied; // (the classical variables of the enclosing block that the `let` expression changes and consumes: the reversal recomputes the changes on copies, as the enclosing block recomputes the versions before them)
	if(hoist){
		Id[] result,local;
		foreach(e;[le.e,orhs]) foreach(x;e.subexpressions) if(auto id=cast(Identifier)x) result~=nameOf(id); // (also a new version that the definition defines, e.g., `(y,k):=let { k+=1; … } in (z,0)`, which the enclosing block may recompute)
		foreach(s;mergeCompound(le.s.s)){
			foreach(n;changedNames(s)) if(!copied.canFind(n)&&!local.canFind(n)&&!result.canFind(n)) copied~=n;
			local~=definedNames(s);
		}
		foreach(o;old) if(!copied.canFind(o[0])) copied~=o[0]; // (e.g., a variable of the enclosing block that it returns, see `NeedOld`)
	}
	auto r=new CompoundExp(reverseStatements(le.s.s,[cast(Expression)def],sc,unchecked,noImplicitDup,hoist,true,hoist?definedNames(def):null,null,copied,&excludedCopied,forgottenNames(le.s),needOld));
	r.loc=loc;
	static if(language==silq) if(hoist){
		renameLocals(le,r,def.e2);
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
			walkIdentifiers(r,(Identifier id){ if(!id.meaning) if(auto p=renames.getPtr(id.id)) id.id=*p; },true,def.e2);
			r.s=copies~r.s;
		}
	}
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
		body_.s=mergeCompound((constUnpack?[constUnpack]:[])~reverseStatements(fbody_.s[0..$-1],retDef?[retDef]:[],bfd.fscope_,unchecked,noImplicitDup,true,false,given,received))~[argRet];
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
			foreach(c;chain(ite.then.s,ite.othw?ite.othw.s:[]).map!classifyStatement) r=join(r,c);
			return r;
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
bool isClassicalMove(Expression e){ // (a classical definition that moves classical variables, e.g., at their last use)
	auto de=cast(DefineExp)e;
	if(!de||de.isSwap||!de.e2.type) return false;
	if(!de.e2.subexpressions.all!(x=>!x.type||x.type.isClassical())||!de.e2.isQfree()||!de.e2.consumes) return false;
	auto names=definedNames(de);
	return !de.e2.subexpressions.any!((x){ // (not into a new version of a moved variable)
		auto id=cast(Identifier)x;
		return id&&id.meaning&&!id.constLookup&&!id.implicitDup&&names.canFind(nameOf(id));
	});
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
Id[] forgottenNames(CompoundExp ce){ // (the variables that a block forgets at its end)
	Id[] r;
	static if(language==silq) if(ce.blscope_) foreach(d;ce.blscope_.forgottenVars) if(d.name) r~=d.name.id;
	return r;
}
Id[] definedNames(Expression e){
	if(auto ite=cast(IteExp)e){ // (the variables that both branches define)
		auto othw=ite.othw?definedNames(ite.othw):[];
		return definedNames(ite.then).filter!(n=>othw.canFind(n)).array;
	}
	if(auto ce=cast(CompoundExp)e) return ce.s.map!definedNames.joiner.array;
	return definedIdentifiers(e).map!nameOf.array;
}

Id[] changedNames(Expression e){ // (the classical variables that a statement changes, e.g., `t+=c` or `(y,t):=let { t+=c; … } in (z,t)`, other than the ones that it defines)
	Id[] r,local;
	void rec(Expression e){
		if(cast(FunctionDef)e||cast(LambdaExp)e) return;
		if(cast(LetExp)e) return; // (it consumes the variables that it changes, and its reversal recomputes them from copies, see `lowerLetDefine`)
		static if(language==silq) if(auto ce=cast(CompoundExp)e) if(ce.loweredFrom) return rec(ce.loweredFrom);
		Id base(Expression e){
			e=unwrap(e);
			while(auto idx=cast(IndexExp)e) e=unwrap(idx.e);
			auto id=cast(Identifier)e;
			return id&&id.type&&id.type.isClassical()?nameOf(id):Id();
		}
		if(auto we=cast(WithExp)e){ // (the inverse restores what the transformation changes)
			auto defined=definedNames(we.bdy);
			foreach(n;chain(changedNames(we.bdy),defined)){
				auto des=we.trans.s.map!(x=>cast(DefineExp)x).filter!(de=>de&&definedNames(de).canFind(n));
				if(!des.empty){ foreach(de;des) if(auto b=base(de.e2)) r~=b; } // (the inverse writes back the component that the body changes or defines again, e.g., for `a[i]+=c` or a swap)
				else if(!defined.canFind(n)) r~=n;
			}
			return;
		}
		if(auto ae=isOpAssignExp(e)) if(auto b=base(ae.e1)) r~=b;
		if(auto de=cast(DefineExp)e){
			Id[] redefined; // (a new version of a variable that a `let` expression on the right-hand side consumes, e.g., `(y,k):=let { k+=1; … } in (z,k)`, which the reversals of later statements would not see if it is not recomputed; the reversal of a call checks the version that it receives)
			if(cast(LetExp)unwrap(de.e2)&&classifyStatement(de)!=ComputationClass.classical) foreach(id;definedIdentifiers(de)) if(id.type&&id.type.isClassical()){
				auto n=nameOf(id);
				foreach(x;de.e2.subexpressions) if(auto y=cast(Identifier)x) if(nameOf(y)==n){ redefined~=n; break; }
			}
			r~=redefined;
			local~=definedNames(de).filter!(n=>!redefined.canFind(n)).array;
			void lhs(Expression x){ // (components of the left-hand side, e.g., of a swap `(a[0],a[1]):=(a[1],a[0])`)
				x=unwrap(x);
				if(auto tpl=cast(TupleExp)x) foreach(y;tpl.e) lhs(y);
				else if(cast(IndexExp)x) if(auto b=base(x)) r~=b;
			}
			lhs(de.e1);
		}
		foreach(x;e.components) rec(x);
	}
	rec(e);
	return r.filter!(n=>!local.canFind(n)).array;
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
			foreach(x;we.trans.s){
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

bool usesUp(Id name,Expression[] statements){ // (whether the statements consume, forget or redefine a variable called `name`)
	bool rec(Expression e){
		if(auto ce=cast(CompoundExp)e) return ce.s.any!rec;
		if(auto ite=cast(IteExp)e) return rec(ite.cond)||rec(ite.then)||ite.othw&&rec(ite.othw);
		if(auto we=cast(WithExp)e) return rec(we.bdy)&&!(we.itrans&&definedNames(we.itrans).canFind(name)); // (the inverse restores what the transformation or the body consumes)
		foreach(x;e.subexpressions){
			if(auto id=cast(Identifier)x)
				if(id.meaning&&id.meaning.name&&id.meaning.name.id==name&&!id.constLookup&&!id.implicitDup)
					return true;
			if(cast(DefineExp)x&&definedNames(x).canFind(name)) return true;
		}
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

Expression recomputation(Expression s,Scope sc){ // (the copy of a classical statement that the reversal of a block recomputes)
	Expression.CopyArgs cargs;
	Id[] inner; // (the variables of `with` statements, e.g., the components that they move out and write back)
	static if(language==silq) cargs.mapExp=(Expression x,ref Expression.CopyArgs args){ // (reads the variables that it moves, such that the reversed statements see the same versions)
		if(cast(FunctionDef)x) return x.copy();
		if(auto we=cast(WithExp)x){
			inner~=chain(definedNames(we.trans),definedNames(we.bdy)).array;
			auto r=new WithExp(we.trans.copy(args),we.bdy.copy(args),we.isIndices);
			if(we.itrans&&we.isIndices) r.itrans=we.itrans.copy(args); // (as for the reversal, see `reverseStatement`)
			r.loc=we.loc;
			return cast(Expression)r;
		}
		if(auto id=cast(Identifier)x) if(id.moved&&!inner.canFind(nameOf(id))){
			auto r=id.copy();
			r.moved=false;
			return cast(Expression)r;
		}
		if(auto de=cast(DefineExp)x) if(isClassicalMove(de)&&!de.e2.subexpressions.any!(y=>cast(Identifier)y&&inner.canFind(nameOf(cast(Identifier)y)))){
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
Expression projection(Expression s,Scope sc,Id[] drop=null){ // (the classical part of an `if` statement, a loop or a `let` expression that is reversed, which the reversal recomputes; without the changes of the variables in `drop`, which it then must not read)
	if(auto ce=cast(CompoundExp)s) if(ce.loweredFrom) return projection(ce.loweredFrom,sc,drop);
	bool readsDropped(Expression e){ return drop.length&&e.subexpressions.any!(x=>cast(Identifier)x&&drop.canFind(nameOf(cast(Identifier)x))); }
	CompoundExp part(CompoundExp b,Expression result=null){
		Expression[] r;
		auto ss=mergeCompound(b.s);
		bool unused(size_t j){ // (local variables that it defines or changes, which no later statement reads other than to forget them, e.g., a definition that reads a dropped variable)
			auto names=chain(definedNames(ss[j]),changedNames(ss[j])).array;
			if(!names.length||!names.all!(n=>ss[0..j+1].any!(t=>definedNames(t).canFind(n)))) return false;
			Id[] mentions(Expression e){ Id[] m; walkIdentifiers(e.copy(),(Identifier id){ m~=id.id; }); return m; }
			bool noop(Expression e){ auto fe=cast(ForgetExp)e; return fe&&!fe.val; }
			return !chain(ss[j+1..$].filter!(t=>!noop(t)),only(result).filter!(e=>!!e)).any!(t=>mentions(t).any!(n=>names.canFind(n)));
		}
		foreach(j,s;ss){
			auto changes=changedNames(s);
			auto changesDropped=changes.any!(n=>drop.canFind(n));
			if(changesDropped&&changes.all!(n=>drop.canFind(n))&&!definedNames(s).length) continue;
			if(classifyStatement(s)==ComputationClass.classical&&!changesDropped){
				if(readsDropped(s)){
					if(unused(j)) continue;
					return null;
				}
				r~=recomputation(s,sc);
			}else if(auto p=projection(s,sc,drop)) r~=p;
			else if(changes.length){ // (the values that it changes would not be recomputed)
				if(unused(j)) continue;
				return null;
			}
		}
		auto res=new CompoundExp(r);
		res.loc=b.loc;
		return res;
	}
	Expression res;
	if(headers(s).any!readsDropped) return null;
	if(auto ite=cast(IteExp)s){
		if(!ite.cond.type||!ite.cond.type.isClassical()) return null;
		auto then=part(ite.then),othw=ite.othw?part(ite.othw):null;
		if(!then||ite.othw&&!othw) return null;
		res=new IteExp(ite.cond.copy(),then,othw);
	}else if(auto fe=cast(ForExp)s){
		auto bdy=part(fe.bdy);
		if(!bdy) return null;
		res=new ForExp(fe.var?fe.var.copy():null,fe.pattern?fe.pattern.copy():null,fe.aggr.copy(Expression.CopyArgs.init),bdy);
	}else if(auto re=cast(RepeatExp)s){
		auto bdy=part(re.bdy);
		if(!bdy) return null;
		res=new RepeatExp(re.num.copy(),bdy);
	}else if(auto de=cast(DefineExp)s){ // (the classical results of a `let` expression, e.g., `k:=let { k+=1; } in k` for `(y,k):=let { k+=1; z:=X(x); } in (z,k)`)
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
	return definedNames(res).length||changedNames(s).length?res:null;
}

static if(language==silq)
bool hasExactInverse(ABinaryExp be){ // (classical updates that the reversal of a function reverts in place, e.g., `t+=c` or `t*=2`, but neither `t*=c`, which loses the value for `c=0`, nor updates of floating-point numbers)
	auto num=isNumericTy(be.e1.type);
	if(num==NumericType.ℝ||num==NumericType.ℂ) return false;
	if(cast(AddAssignExp)be||cast(SubAssignExp)be||cast(BitXorAssignExp)be||cast(XorAssignExp)be) return true;
	if(!cast(MulAssignExp)be&&!cast(DivAssignExp)be||num!=NumericType.ℕt&&num!=NumericType.ℤt&&num!=NumericType.ℚt) return false; // (e.g., `t*=2` loses the highest bit of `t:!uint[4]`)
	auto val=be.e2.asIntegerConstant(true);
	return val&&val.get()!=0;
}

struct NeedOld{ // (the variables of enclosing blocks whose versions before a statement its reversal would need, e.g., for `u:=dup(k); k+=u;` or for a conditional that changes a variable of its condition: an enclosing block may provide copies of them, see `reversal` in `reverseStatements`)
	Id[] vars;
	Q!(Id[],Location,string)[] errors; // (deferred errors, e.g., of reversals of `if` statements and loops that change a variable of their condition or range)
}

static if(language==silq)
bool readsOld(Expression s){ // (statements whose reversals can read copies of the versions of variables before them, see `NeedOld`)
	if(auto ce=cast(CompoundExp)s) if(ce.loweredFrom) return readsOld(ce.loweredFrom);
	if(cast(IteExp)s||cast(RepeatExp)s) return true;
	if(auto fe=cast(ForExp)s) return !!fe.aggr.isRange();
	auto de=cast(DefineExp)s;
	return de&&cast(LetExp)unwrap(de.e2);
}

Expression[] reverseStatements(Expression[] statements,Expression[] middle,Scope sc,bool unchecked,bool noImplicitDup,bool hoistClassical=false,bool defer=false,Id[] given=null,Id[] alive=null,Id[] copied=null,Id[]* excludedCopied=null,Id[] forgotten=null,NeedOld* needOld=null){
	statements=mergeCompound(statements);
	if(hoistClassical){ // (`given`: the variables whose values the reversal receives, e.g., the classical results of a function; `alive`: the variables that the reversal of an enclosing block recomputes; `copied`: the variables of an enclosing block whose changes are recomputed on copies, see `lowerLetDefine`)
		auto defined=middle.map!definedNames.joiner.array; // (received after the recomputation, which they are checked against)
		Id[] givenAfter(size_t i){ return given.filter!(n=>!usesUp(n,statements[i+1..$])).array; }
		bool reads(Expression e,Id name){ return e.subexpressions.any!(x=>cast(Identifier)x&&nameOf(cast(Identifier)x)==name); }
		auto changed=statements.map!changedNames.array;
		auto headerChanges=new Id[][](statements.length); // (the variables of the condition or bounds of an `if` statement or a loop that it changes: the reversal reads copies of the versions before it)
		foreach(i,s;statements) foreach(h;headers(s)) foreach(x;h.subexpressions) if(auto id=cast(Identifier)x) if(changed[i].canFind(nameOf(id))&&!headerChanges[i].canFind(nameOf(id))) headerChanges[i]~=nameOf(id);
		auto local=chain(copied,statements.map!definedNames.joiner).array;
		Id[] inner=copied.dup; // (as `local`, but without new versions of variables of an enclosing block, e.g., one that a `let` expression returns, see `NeedOld`)
		foreach(j,s;statements) foreach(n;definedNames(s)) if(!changed[j].canFind(n)&&!inner.canFind(n)) inner~=n;
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
			if(noop(s)||!names.length||!onlyClassical(s)) continue;
			bool isLocal(Id n){ return copied.canFind(n)||statements[0..i+1].any!(t=>definedNames(t).canFind(n)); }
			bool usedUp(Id n){ return usesUp(n,statements[i+1..$])||forgotten.canFind(n)||forgetsIn(s,n); } // (otherwise, it may be used after the block)
			if(!names.all!(n=>isLocal(n)&&usedUp(n)&&!given.canFind(n)&&!defined.canFind(n)&&!mentionedAfter.canFind(n))) continue;
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
		for(Id[] excluded;;){ // (variables that a reversed statement which is not recomputed changes, e.g., a loop with quantum statements: the statements that define them are reversed as well)
			auto hoisted=copied.dup;
			foreach(i,s;statements){
				auto after=givenAfter(i);
				bool valid(Id[] names,Id[] changes){
					if(!changes.all!(n=>hoisted.canFind(n))) return false; // (e.g., the reversal of a nested block reverses the changes of variables that an enclosing block defines)
					if(changedAfter[i].any!(n=>!hoisted.canFind(n)&&!names.canFind(n)&&reads(s,n))) return false; // (the recomputation would see the version after the change)
					return !chain(names,changes).any!(n=>excluded.canFind(n)||after.canFind(n)&&!defined.canFind(n)); // (the reversed definition checks the received value)
				}
				auto names=definedNames(s);
				recomputed[i]=!dead[i]&&classifyStatement(s)==ComputationClass.classical&&valid(names,changed[i]);
				projections[i]=null;
				static if(language==silq) if(!recomputed[i]&&!dead[i]){
					auto drop=changed[i].filter!(n=>!hoisted.canFind(n)||after.canFind(n)&&!defined.canFind(n)).array; // (variables whose current versions the reversal changes in place, e.g., a variable of an enclosing block that a `let` expression returns, in a loop that also changes one that it consumes)
					auto p=projection(s,sc,drop);
					if(p){
						auto pnames=definedNames(p),pchanges=changed[i].filter!(n=>!drop.canFind(n)).array; // (all of the others, see `projection`)
						if((pchanges.length||statements[i+1..$].any!(t=>pnames.any!(n=>reads(t,n))))&&valid(pnames,pchanges)){
							projections[i]=p;
							projectionChanges[i]=pchanges;
						}
					}
					if(!projections[i]&&(p||classifyStatement(s)==ComputationClass.classical)) // (also in earlier iterations, e.g., before the variables that the statement changes are excluded)
						foreach(n;changedAfter[i]) if(!hoisted.canFind(n)&&!inner.canFind(n)&&reads(s,n)&&!blockedAt[i].canFind(n)) blockedAt[i]~=n;
				}
				if(recomputed[i]) hoisted~=names;
				else if(projections[i]) hoisted~=definedNames(projections[i]);
			}
			bool needed(Id n){ return given.canFind(n)||middle.any!(t=>readsBesidesUpdates(t,n))||iota(statements.length).any!(j=>!dead[j]&&readsBesidesUpdates(statements[j],n)); } // (otherwise, its values do not matter, e.g., a vector whose components are updated but not read)
			auto more=iota(statements.length).filter!(i=>!recomputed[i]&&!projections[i]&&!dead[i]).map!(i=>changed[i]).joiner.filter!(n=>hoisted.canFind(n)&&!excluded.canFind(n)&&needed(n)).array;
			static if(language==silq) foreach(i;0..statements.length) if(!recomputed[i]&&!projections[i]&&!dead[i]&&changed[i].any!(n=>copied.canFind(n)&&more.canFind(n))) // (the reversal would not have the versions of the copy after the statement, see `excludedCopied` in `lowerLetDefine`)
				foreach(n;changed[i]) if(!hoisted.canFind(n)&&!inner.canFind(n)&&!blockedAt[i].canFind(n)) blockedAt[i]~=n;
			if(!more.length){
				if(excludedCopied) *excludedCopied=excluded.filter!(n=>copied.canFind(n)).array;
				if(needOld) foreach(n;blockedAt.joiner) if(!needOld.vars.canFind(n)) needOld.vars~=n;
				break;
			}
			excluded~=more;
		}
		Id[] checked;
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
		}
		auto hoistedAll=chain(copied,iota(statements.length).map!(i=>recomputed[i]?definedNames(statements[i]):projections[i]?definedNames(projections[i]):[]).joiner).array;
		auto saves=new Id[][](statements.length); // (the fresh names of the copies, see `headerChanges`)
		static if(language==silq) foreach(i;0..statements.length) if(headerChanges[i].length&&(projections[i]||recomputed[i]&&undone[i])&&headerChanges[i].all!(n=>hoistedAll.canFind(n))) saves[i]=headerChanges[i].map!(n=>freshName()).array;
		auto aliveAt=new Id[][](statements.length); // (the variables whose current versions the reversal of a statement sees as recomputed values)
		alive=alive~copied;
		foreach(i,s;statements){
			aliveAt[i]=alive;
			auto names=definedNames(s);
			alive=alive.filter!(n=>!names.canFind(n)).array;
			if(recomputed[i]) alive~=names;
			else if(projections[i]) alive~=definedNames(projections[i]);
		}
		auto oldVersions=new Id[2][][](statements.length); // (copies of the versions before a statement whose classical part is recomputed, for its reversal, see `NeedOld`)
		enum headerChangeError="reversal of `if` statement or loop that changes a variable of its condition or range not supported yet";
		Expression reversal(size_t i){
			static if(language==silq) if(auto fe=cast(ForgetExp)statements[i]) if(fe.val) if(auto id=cast(Identifier)unwrap(fe.var)){
				if(id.type&&id.type.isClassical()&&aliveAt[i].canFind(nameOf(id))){ // (the forgotten value is recomputed, it is checked)
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
				if(needOld&&!inner.canFind(n)){ // (an enclosing block may recompute it from the version before it, see `NeedOld`)
					if(defer){ if(!needOld.vars.canFind(n)) needOld.vars~=n; } // (otherwise, it is reverted in place, see below)
					else{
						needOld.errors~=q(chain(only(n),blockedAt.joiner.filter!(m=>m!=n)).array,be.loc,"reversal of assignments not supported yet");
						auto r=statements[i].copy();
						r.setSemError();
						return r;
					}
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
			auto projected=projections[i]?definedNames(projections[i]):undone[i]?definedNames(statements[i]):[]; // (checked by the reversed statement)
			NeedOld need;
			auto nerrors=sc.handler.nerrors;
			auto r=reverseStatement(statements[i],sc,unchecked,noImplicitDup,hoistClassical,defer,givenAfter(i)~projected,aliveAt[i],null,&need);
			static if(language==silq) if((projections[i]||recomputed[i]&&undone[i])&&readsOld(statements[i])){ // (also a recomputed statement that is reversed in place, e.g., a loop that a conditional in it changes, for earlier statements that read the versions before it)
				auto pc=projections[i]?chain(projectionChanges[i],definedNames(projections[i])).array:chain(changed[i],definedNames(statements[i])).array;
				Id[] old;
				if(chain(need.vars,need.errors.map!(e=>e[0]).joiner).any!(n=>pc.canFind(n))) foreach(n;pc) if(!old.canFind(n)) old~=n; // (all of them, as the reversal of the statement may need more once it recomputes some, e.g., an update that it would otherwise reverse first)
				if(old.length&&sc.handler.nerrors==nerrors){ // (versions before the statement that the projection changes: the reversal of the statement recomputes them on copies)
					oldVersions[i]=old.map!(n=>cast(Id[2])[n,freshName()]).array;
					need=NeedOld.init;
					r=reverseStatement(statements[i],sc,unchecked,noImplicitDup,hoistClassical,defer,givenAfter(i)~projected,aliveAt[i],oldVersions[i],&need);
				}
			}
			if(needOld) foreach(n;need.vars) if(!inner.canFind(n)&&!needOld.vars.canFind(n)) needOld.vars~=n;
			foreach(e;need.errors){ // (deferred if an enclosing block may resolve it, also through the other needs of this block)
				auto vars=e[0].filter!(n=>!inner.canFind(n)).array;
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
				foreach(n;chain(headerChanges[i],changed[i],changedAfter[i].filter!(n=>reads(statements[i],n)),blockedAt.joiner)) if(!hoistedAll.canFind(n)&&!inner.canFind(n)&&!missing.canFind(n)) missing~=n;
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
		Expression[] undoneFirst=iota(statements.length).retro.filter!(i=>undoFirst[i]).map!reversed.array;
		Expression[] quantumStatements;
		foreach_reverse(i;0..statements.length){
			if(recomputed[i]&&!undone[i]||undoFirst[i]||dead[i]) continue;
			quantumStatements~=reversed(i);
			static if(language==silq) foreach(o;oldVersions[i]){ // (the version before the statement replaces the one after it)
				auto loc=statements[i].loc;
				auto var=new Identifier(o[0]),lhs=new Identifier(o[0]),rhs=new Identifier(o[1]);
				var.loc=lhs.loc=rhs.loc=loc;
				auto fe=new ForgetExp(var,null);
				fe.loc=loc;
				auto de=new DefineExp(lhs,rhs);
				de.loc=loc;
				quantumStatements~=[cast(Expression)fe,de];
			}
		}
		Expression[] classicalStatements;
		foreach(i;0..statements.length){
			static if(language==silq) foreach(o;oldVersions[i]){
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
				auto rhs=new CallExp(getDup(var.loc,sc),var,false,false);
				rhs.loc=var.loc;
				auto cpy=new DefineExp(lhs,rhs);
				cpy.loc=var.loc;
				classicalStatements~=cpy;
			}
			if(recomputed[i]&&!early[i]) classicalStatements~=recomputation(statements[i],sc);
			else if(projections[i]) classicalStatements~=projections[i];
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
		void updateLambdas(Expression e){
			foreach(x;e.subexpressions){
				if(auto le=cast(LambdaExp)x){
					if(le.fd.body_) updateLambdas(le.fd.body_);
					le.orig=le.fd.copy();
				}else if(auto nested=cast(FunctionDef)x) if(nested.body_) updateLambdas(nested.body_);
			}
		}
		updateLambdas(nfd.body_);
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
		auto res=new CompoundExp(reverseStatements(ce.s,[],sc,unchecked,noImplicitDup,hoist,defer,given.filter!(n=>!old.canFind!(o=>o[0]==n)).array,alive,old.map!(o=>o[0]).array,&excludedOld,forgottenNames(ce),needOld)); // (it recomputes the variables in `old` on copies, also those whose versions after it the reversal received)
		res.loc=ce.loc;
		static if(language==silq) if(old.length) res.s=copiesOf(res,old,excludedOld,ce.loc,sc)~res.s;
		foreach(s;res.s) propErr(s,res);
		static if(language==silq){
			if(ce.blscope_&&ce.blscope_.forgottenVars.any!(d=>d.isLinear())){
				sc.error("reversal of implicit forget not supported yet",ce.loc);
				res.setSemError();
			}
		}
		return res;
	}
	if(auto ite=cast(IteExp)e){
		auto then=cast(CompoundExp)reverseStatement(ite.then,sc,unchecked,noImplicitDup,hoistClassical,defer,given,alive,old,needOld);
		assert(!!then);
		auto othw=cast(CompoundExp)reverseStatement(ite.othw,sc,unchecked,noImplicitDup,hoistClassical,defer,given,alive,old,needOld);
		assert(!!othw==!!ite.othw);
		auto cond=ite.cond.copy();
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
		if(auto ae=cast(BitXorAssignExp)e) return ae.copy();
		if(auto ae=cast(XorAssignExp)e) return ae.copy();
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
	if(auto ae=cast(AssertExp)e) return ae.copy();
	if(auto fe=cast(ForgetExp)e){
		auto tpl=new TupleExp([]);
		tpl.type=unit;
		tpl.loc=fe.loc;
		return lowerDefine!flags(fe,tpl,fe.loc,sc,unchecked,noImplicitDup,defer);
	}
	sc.error("reversal unsupported",e.loc);
	return error();
}

