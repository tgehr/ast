// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.reverse;
import astopt;

import std.conv,std.format,std.algorithm,std.range,std.exception;
import ast.lexer,ast.scope_,ast.expression,ast.type,ast.declaration,ast.semantic_,ast.error,util;
import util.tuple:Q=Tuple,q=tuple;

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

enum LowerDefineFlags{
	none=0,
	createFresh=1,
	reverseMode=2,
}

Expression knownLength(Expression e,bool ignoreType){ // TODO: version that returns bool
	Expression res;
	scope(exit) if(res) res.loc=e.loc;
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
		if(auto vec=cast(VectorTy)tae.t)
			return vec.num;
		if(auto tt=tae.t.isTupleTy())
			return res=constantExp(tt.length);
		if(auto pow=cast(PowExp)tae.t)
			return pow.e2;
		if(auto ty=cast(TypeofExp)tae.t){
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
					if(id.meaning.isConst)
						return false;
			}else return false;
		}
		return cast(Identifier)e||cast(IndexExp)e||cast(SliceExp)e;
	}
	if(auto tpl=cast(TupleExp)olhs) return tpl.e.all!validDefEntry;
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
		if(ce.checkReverse&&!unchecked){
			auto r=reverseCallRewriter(ft,ce.loc);
			if(r.movedType.hasClassicalComponent()){
				return false;
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

Expression lowerDefine(LowerDefineFlags flags)(Expression olhs,Expression orhs,Location loc,Scope sc,bool unchecked,bool noImplicitDup)in{
	assert(loc.line);
}do{
	enum createFresh=!!(flags&LowerDefineFlags.createFresh); // TODO: can we get rid of this?
	enum reverseMode=!!(flags&LowerDefineFlags.reverseMode);
	Expression res;
	scope(success) if(res){ res.loc=loc; }
	static if(createFresh) Expression nlhs;
	Expression lhs(){ // TODO: solve better
		static if(createFresh){
			if(!nlhs) nlhs=olhs.copy();
			if(noImplicitDup){ // TODO: this is a hack
				void removeImplicitDup(Expression e){
					e.implicitDup=false;
					if(auto tae=cast(TypeAnnotationExp)e)
						removeImplicitDup(tae.e);
					else if(auto tpl=cast(TupleExp)e)
						foreach(ne;tpl.e)
							removeImplicitDup(ne);
				}
				removeImplicitDup(nlhs);
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
		if(cast(Identifier)olhs&&olhs.type&&olhs.type.isClassical())
			lhs.implicitDup=true;
	}
	if(validDefLhs!flags(olhs,sc,unchecked,noImplicitDup)){
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
		auto tplr=new TupleExp(iota(tpll.e.length).map!(delegate Expression(i){ auto id=new Identifier(freshName); id.loc=orhs.loc; return id; }).array);
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
	if(isLiftedBuiltIn(olhs)) return forget();
	if(auto ce=cast(CallExp)olhs){
		if(auto ft=cast(FunTy)ce.e.type){
			if(ft.isSquare==ce.isSquare&&ft.annotation>=Annotation.qfree&&(ft.nargs||isEmptyTuple(ce.arg))&&ft.isConstForReverse.all)
				return forget();
		}
	}
	if(auto tae=cast(TypeAnnotationExp)olhs){
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
		auto tmp=new Identifier(freshName);
		tmp.loc=orhs.loc;
		auto tmpLen(){
			auto id=new Identifier("length");
			id.loc=tmp.loc;
			return new FieldExp(tmp.copy(),id);
		}
		auto d1=lowerDefine!flags(tmp,orhs,loc,sc,unchecked,noImplicitDup);
		auto known1=knownLength(ce.e1,true),known2=knownLength(ce.e2,true);
		auto ue1=unwrap(ce.e1),ue2=unwrap(ce.e2);
		auto valid1=cast(Identifier)ue1,valid2=cast(Identifier)ue2;
		if(!valid1||!valid2){
			Expression[] stmts1=d1?[d1]:[],stmts2=[];
			auto ne1=ce.e1,ne2=ce.e2;
			if(!cast(Identifier)ue1){
				auto tmpe1=new Identifier(freshName);
				tmpe1.loc=ce.e1.loc;
				stmts2~=lowerDefine!flags(ne1,tmpe1,loc,sc,unchecked,noImplicitDup);
				ne1=tmpe1.copy();
				ne1.loc=ce.e1.loc;
			}
			if(!cast(Identifier)ue2){
				auto tmpe2=new Identifier(freshName);
				tmpe2.loc=ce.e2.loc;
				stmts2~=lowerDefine!flags(ne2,tmpe2,loc,sc,unchecked,noImplicitDup);
				ne2=tmpe2.copy();
				ne2.loc=ce.e2.loc;
			}
			assert(l1||l2);
			if(!(known1&&valid1)&&l1){
				ne1=unwrap(ne1); // TODO: ok?
				auto w1=new WildcardExp();
				w1.loc=ce.e1.loc;
				auto ty1=new PowExp(w1,l1);
				ty1.loc=ce.e1.loc;
				ne1=new TypeAnnotationExp(ne1,ty1,TypeAnnotationType.coercion);
				ne1.loc=ce.e1.loc;
			}
			if(!(known2&&valid2)&&l2){
				ne2=unwrap(ne2); // TODO: ok?
				auto w2=new WildcardExp();
				w2.loc=ce.e2.loc;
				auto ty2=new PowExp(w2,l2);
				ty2.loc=ce.e2.loc;
				ne2=new TypeAnnotationExp(ne2,ty2,TypeAnnotationType.coercion);
				ne2.loc=ce.e2.loc;
			}
			auto nce=new CatExp(ne1,ne2);
			nce.loc=ce.loc;
			auto tmp3=tmp.copy();
			tmp3.loc=orhs.loc;
			auto d2=lowerDefine!flags(nce,tmp3,loc,sc,unchecked,noImplicitDup);
			stmts1~=d2;
			return res=new CompoundExp(stmts1~stmts2);
		}else{
			// default lowering
			//imported!"util.io".writeln("default lowering: ",olhs," := ",orhs,"; ",known1," ",known2);
			// TODO: nicer runtime error message for inconsistent array lengths?
			if(!l1){
				auto l=tmpLen();
				l.loc=l2.loc;
				auto s=new NSubExp(l,l2);
				s.loc=l2.loc;
				l1=s;
			}else if(!l2){
				auto l=tmpLen();
				l.loc=l1.loc;
				auto s=new NSubExp(l,l1);
				s.loc=l1.loc;
				l2=s;
			}
			assert(l1&&l2);
			auto tmp1=tmp.copy();
			tmp1.loc=orhs.loc;
			auto z=constantExp(0);
			z.loc=olhs.loc;
			Expression s1=new SliceExp(tmp1,z,l1);
			s1.loc=tmp1.loc;
			auto tmp2=tmp.copy();
			tmp2.loc=orhs.loc;
			auto l=tmpLen();
			l.loc=olhs.loc;
			Expression s2=new SliceExp(tmp2,l1.copy(),l);
			s2.loc=tmp2.loc;
			auto tmpl=cast(Identifier)ce.e1?ce.e1:new Identifier(freshName);
			if(tmpl!is ce.e1){
				tmpl.loc=ce.e1.loc;
				static if(reverseMode) tmpl.type=ce.e1.type;
			}
			auto d2=lowerDefine!flags(tmpl.copy(),s1,loc,sc,unchecked,noImplicitDup);
			d2.loc=loc;
			auto tmpr=cast(Identifier)ce.e2?ce.e2:new Identifier(freshName);
			if(tmpr!is ce.e2){
				tmpr.loc=ce.e2.loc;
				static if(reverseMode) tmpr.type=ce.e2.type;
			}
			auto d3=lowerDefine!flags(tmpr.copy(),s2,loc,sc,unchecked,noImplicitDup);
			d3.loc=loc;
			auto tmp3=tmp.copy();
			tmp3.loc=orhs.loc;
			auto cat=new CatExp(tmpl.copy(),tmpr.copy());
			cat.loc=ce.loc;
			auto fe=new ForgetExp(tmp3,cat);
			fe.loc=loc;
			auto stmts=(d1?[d1]:[])~[d2,d3,fe];
			if(ce.e1 !is tmpl){
				auto d4=lowerDefine!flags(ce.e1,tmpl,loc,sc,unchecked,noImplicitDup);
				d4.loc=loc;
				stmts~=d4;
			}
			if(ce.e2 !is tmpr){
				auto d5=lowerDefine!flags(ce.e2,tmpr,loc,sc,unchecked,noImplicitDup);
				d5.loc=loc;
				stmts~=d5;
			}
			return res=new CompoundExp(stmts);
		}
	}
	if(auto fe=cast(ForgetExp)olhs){
		if(!fe.val){
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
		auto def=lowerDefine!(flags&~LowerDefineFlags.reverseMode)(fe.var,nval,loc,sc,unchecked,noImplicitDup);
		auto arhs=rhs;
		if(orhs.type!=unit){
			arhs=new TypeAnnotationExp(arhs,unit,TypeAnnotationType.annotation);
			arhs.type=unit;
			arhs.loc=orhs.loc;
		}
		if(!tpl) return res=new CompoundExp([arhs,def]);
		return def;
	}
	if(auto conv=cast(TypeAnnotationExp)olhs) {
		return lowerDefine!flags(conv.e, orhs, loc, sc, unchecked,noImplicitDup);
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
					sc.error(format("cannot reverse primitive '%s'",prim),oce.e.loc);
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
					sc.error(format("cannot reverse primitive '%s'",prim),oce.e.loc);
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
				sc.error(format("cannot reverse primitive '%s'",prim),oce.e.loc);
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
			sc.error("reversed function must be 'mfree'",ce.e.loc);
			return error();
		}
		if(!unchecked&&!needWrapper&&!ft.isClassical){
			sc.error("quantum function call not supported as definition left-hand side",ce.loc); // TODO: support within reversed functions
			return error();
		}
		auto f=ce.e;
		auto r=reverseCallRewriter(ft,f.loc);
		if(!unchecked&&!needWrapper&&r.movedType.hasClassicalComponent()){
			sc.error("reversed function cannot have classical components in 'moved' arguments", f.loc);
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
				sc.error(format("wrong number of arguments to reversed function call (%s instead of %s)",tpl.length,ft.nargs),ce.loc);
				return error();
			}
		}else{
			sc.error("cannot match single tuple to function with mixed 'const' and consumed parameters",ce.loc);
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
	if(auto we=cast(WildcardExp)olhs){
		rhs.implicitDup=false; // TODO: ok?
		return res=new ForgetExp(rhs,null);
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
	if(validDefLhs!flags(e.e1,sc,unchecked,noImplicitDup)) return null;
	return lowerDefine!flags(e.e1,e.e2,e.loc,sc,unchecked,noImplicitDup);
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

static if(language==silq)
FunctionDef reverseFunction(FunctionDef fd)in{
	assert(fd.scope_&&fd.ftype&&fd.ftype.isClassical()&&fd.ftype.annotation>=Annotation.mfree);
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
	/+if(fd.name){
		auto scope_=fd.scope_; // TODO: this is a bit hacky
		if(scope_.canInsert(fd.name.id)){
			fd.scope_=null;
			fd.rename=null;
			if(!scope_.insert(fd,true))
				fd.setSemError();
		}
	}+/
	auto r=reverseCallRewriter(fd.ftype,fd.loc);
	// enforce(!argTypes.any!(t=>t.hasClassicalComponent()),"reversed function cannot have classical components in consumed arguments"); // lack of classical components may not be statically known at the point of function definition due to generic parameters
	auto fbody_=fd.body_;
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
			retDefReplaced=true;
			rpname=(id.meaning&&id.meaning.name?id.meaning.name:id).id;
		}
	}
	if(!retDefReplaced) rpname=freshName();
	Expression dom, cod;
	bool isTuple;
	bool[] isConst;
	Id[] pnames;
	Expression constUnpack=null;
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
		body_.s=mergeCompound((constUnpack?[constUnpack]:[])~reverseStatements(fbody_.s[0..$-1],retDef?[retDef]:[],fd.fscope_,unchecked,noImplicitDup))~[argRet];
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
		if(auto ce=cast(CompoundExp)e) assert(0);
		if(auto ite=cast(IteExp)e){
			if(!ite.cond.type.isClassical()) return ComputationClass.quantum;
			//return chain(ite.then.s,ite.othw?ite.othw.s:[]).map!classifyStatement.reduce!join(classical); // ???
			auto r=bottom;
			foreach(c;chain(ite.then.s,ite.othw?ite.othw.s:[]).map!classifyStatement) r=join(r,c);
			return r;
		}
		if(auto we=cast(WithExp)e){
			//return join(classifyExpression(we.trans,we.bdy));
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
			return classifyExpression(de.e2);
		}
		if(auto ae=cast(AssignExp)e) return unsupported;
		if(isOpAssignExp(e)){
			auto be=cast(ABinaryExp)e;
			assert(!!be);
			assert(!!be.e2.type);
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
			assert(!ce.blscope_);
			r~=mergeCompound(ce.s);
			continue;
		}
		if(auto ce=cast(CommaExp)e){
			r~=mergeCompound([ce.e1]);
			r~=mergeCompound([ce.e2]);
		}
		if(auto ite=cast(IteExp)e){
			assert(!!ite.then);
			ite.then.s=mergeCompound(ite.then.s);
			if(ite.othw) ite.othw.s=mergeCompound(ite.othw.s);
		}
		if(auto fe=cast(ForExp)e) fe.bdy.s=mergeCompound(fe.bdy.s);
		if(auto we=cast(WhileExp)e) we.bdy.s=mergeCompound(we.bdy.s);
		if(auto re=cast(RepeatExp)e) re.bdy.s=mergeCompound(re.bdy.s);
		r~=e;
	}
	return r;
}

Expression[] reverseStatements(Expression[] statements,Expression[] middle,Scope sc,bool unchecked,bool noImplicitDup){
	statements=mergeCompound(statements);
	Expression[] classicalStatements=statements.filter!(s=>classifyStatement(s)==ComputationClass.classical).array;
	foreach(ref e;classicalStatements) e=e.copy();
	Expression[] quantumStatements=statements.retro.filter!(s=>classifyStatement(s)!=ComputationClass.classical).array;
	foreach(ref e;quantumStatements) e=reverseStatement(e,sc,unchecked,noImplicitDup);
	return classicalStatements~middle~quantumStatements;
}

Expression reverseStatement(Expression e,Scope sc,bool unchecked,bool noImplicitDup){
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
							return lowerDefine!flags(te,te,ce.loc,sc,unchecked,noImplicitDup);
						default:
							break;
					}
				}
			}
		}
		return lowerDefine!flags(ce,te,ce.loc,sc,unchecked,noImplicitDup);
	}
	if(auto ce=cast(CompoundExp)e){
		auto res=new CompoundExp(reverseStatements(ce.s,[],sc,unchecked,noImplicitDup));
		res.loc=ce.loc;
		static if(language==silq){
			if(ce.blscope_&&ce.blscope_.forgottenVars.any!(d=>d.isLinear())){
				sc.error("reversal of implicit forget not supported yet",ce.loc);
				res.setSemError();
			}
		}
		return res;
	}
	if(auto ite=cast(IteExp)e){
		auto then=cast(CompoundExp)reverseStatement(ite.then,sc,unchecked,noImplicitDup);
		assert(!!then);
		auto othw=cast(CompoundExp)reverseStatement(ite.othw,sc,unchecked,noImplicitDup);
		assert(!!othw==!!ite.othw);
		auto res=new IteExp(ite.cond.copy(),then,othw);
		res.loc=ite.loc;
		return res;
	}
	if(auto we=cast(WithExp)e){
		auto trans=we.trans.copy();
		auto bdy=cast(CompoundExp)reverseStatement(we.bdy,sc,unchecked,noImplicitDup);
		assert(!!bdy);
		auto res=new WithExp(trans,bdy);
		res.loc=we.loc;
		return res;
	}
	if(auto ret=cast(ReturnExp)e){
		sc.error("reversing early returns not supported yet",ret.loc);
		return error();
	}
	if(auto fd=cast(FunctionDef)e){
		sc.error("reversal of quantum variable capturing not supported yet",fd.loc);
		return error();
	}
	// TODO: DatDecl?
	if(auto ce=cast(CommaExp)e) assert(0);
	if(auto de=cast(DefineExp)e){
		if(de.isSwap) return de.copy(); // TODO: ok?
		Expression nrhs=de.e1;
		if(nrhs.type!=de.e2.type){
			nrhs=new TypeAnnotationExp(nrhs,de.e2.type,TypeAnnotationType.coercion);
			nrhs.loc=de.e1.loc;
			nrhs.type=de.e2.type;
		}
		return lowerDefine!flags(de.e2,nrhs,de.loc,sc,unchecked,noImplicitDup);
	}
	if(auto ae=cast(AssignExp)e){
		sc.error("reversal of functions containing assignments not supported yet",ae.loc);
		return error();
	}
	if(isOpAssignExp(e)){
		auto be=cast(ABinaryExp)e;
		assert(!!be);
		assert(!!be.e2.type);
		if(be.e2.type.isClassical()){
			sc.error("reversal of assignments not supported yet",be.loc);
			return error();
		}
		if(!isInvertibleOpAssignExp(be)){
			if(be.e2.type.hasClassicalComponent()){
				sc.error("reversal of assignments not supported yet",be.loc);
				return error();
			}
			sc.error("reversal of implicit forgets not supported yet",be.loc);
			return error();
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
		if(auto ae=cast(CatAssignExp)e){
			if(!cast(Identifier)ae.e1){
				sc.error("reversal of concatenation to non-identifier not supported yet",ae.loc);
				return error();
			}
			auto nlhs=new CatExp(ae.e1.copy(),ae.e2);
			nlhs.type=ae.e1.type;
			auto nrhs=ae.e1;
			return lowerDefine!flags(nlhs,nrhs,ae.loc,sc,unchecked,noImplicitDup);
		}
		if(auto ae=cast(BitXorAssignExp)e) return ae.copy();
		sc.error("reversal not supported yet",e.loc);
		return error();
	}
	if(auto fe=cast(ForExp)e){
		auto bdy=cast(CompoundExp)reverseStatement(fe.bdy,sc,unchecked,noImplicitDup);
		assert(!!bdy);
		auto leftExclusive=fe.rightExclusive;
		auto left=fe.right.copy();
		auto rightExclusive=fe.leftExclusive;
		auto right=fe.left.copy();
		auto ostep=fe.step?fe.step.copy():null;
		if(!ostep){
			ostep=constantExp(1);
			ostep.loc=left.loc.to(right.loc);
		}
		auto step=new UMinusExp(ostep);
		step.loc=ostep.loc;
		auto res=new ForExp(fe.var.copy(),leftExclusive,left,step,rightExclusive,right,bdy);
		res.loc=fe.loc;
		return res;
	}
	if(auto we=cast(WhileExp)e){
		sc.error("reversal of while loops not supported yet",we.loc);
		return error();
	}
	if(auto re=cast(RepeatExp)e){
		auto bdy=cast(CompoundExp)reverseStatement(re.bdy,sc,unchecked,noImplicitDup);
		assert(!!bdy);
		auto res=new RepeatExp(re.num.copy(),bdy);
		res.loc=re.loc;
		return res;
	}
	if(auto oe=cast(ObserveExp)e) enforce(0);
	if(auto oe=cast(CObserveExp)e) enforce(0);
	if(auto ae=cast(AssertExp)e) return ae.copy();
	if(auto fe=cast(ForgetExp)e){
		auto tpl=new TupleExp([]);
		tpl.type=unit;
		tpl.loc=fe.loc;
		return lowerDefine!flags(fe,tpl,fe.loc,sc,unchecked,noImplicitDup);
	}
	sc.error("reversal unsupported",e.loc);
	return error();
}

