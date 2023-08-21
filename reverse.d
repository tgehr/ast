// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.reverse;
import astopt;

import std.stdio,std.conv,std.format,std.algorithm,std.range,std.exception;
import ast.lexer,ast.scope_,ast.expression,ast.type,ast.declaration,ast.semantic_,ast.error,util;
import util.tuple:Q=Tuple,q=tuple;

Expression constantExp(size_t l){
	Token tok;
	tok.type=Tok!"0";
	tok.str=to!string(l);
	return new LiteralExp(tok);
}

static if(language==silq)
Identifier getDup(Location loc,Scope isc){
	return getPreludeSymbol("dup",loc,isc);
}

bool isClassicalExp(Expression e){
	static if(language==silq) return e.type&&e.subexpressions.all!(x=>!x.type||x.type.isClassical())&&e.isQfree()&&!e.consumes;
	else return true;
}
bool hasImplicitDup(Expression olhs,Scope sc){
	if(olhs.byRef) return false;
	if(auto idx=cast(IndexExp)olhs)
		return !olhs.byRef;
	return false;
}

enum LowerDefineFlags{
	none=0,
	createFresh=1,
	reverseMode=2,
}

bool validDefLhs(LowerDefineFlags flags)(Expression olhs,Scope sc){
	bool validDefEntry(Expression e){
		static if(flags&LowerDefineFlags.reverseMode) if(hasImplicitDup(e,sc)) return false;
		return cast(Identifier)e||cast(IndexExp)e;
	}
	if(auto tpl=cast(TupleExp)olhs) return tpl.e.all!validDefEntry;
	if(auto ce=cast(CallExp)olhs){
		if(isPrimitive(cast(CallExp)unwrap(ce.e)))
			return false;
		auto f=ce.e, ft=cast(ProductTy)f.type;
		if(!ft) return false;
		if(ce.isSquare!=ft.isSquare) return false;
		// if(!equal(ft.isConst,ft.isConstForReverse)) return false; // TODO: can we completely rewrite away isConstForReverse?
		if(iota(ft.nargs).all!(i=>ft.isConstForReverse[i])){
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

ReverseCallRewriter reverseCallRewriter(FunTy ft_,Location loc){
	auto r=ReverseCallRewriter(ft_,loc);
	with(r){
		constTuple=constIndices.walkLength!=1||movedIndices.empty&&ft.isTuple;
		movedTuple=movedIndices.walkLength!=1||constIndices.empty&&ft.isTuple;
		constType=constTuple?tupleTy(constIndices.map!(i=>ft.argTy(i)).array):ft.argTy(constIndices.front);
		movedType=movedTuple?tupleTy(movedIndices.map!(i=>ft.argTy(i)).array):ft.argTy(movedIndices.front);
		returnType=ft.cod;
		returnTuple=returnType==unit;
		return r;
	}
}

struct ReverseCallRewriter{
	ProductTy ft;
	Location loc;
	bool constTuple,movedTuple,returnTuple;
	Expression constType,movedType,returnType;
	@property constIndices()return scope{ return iota(ft.nargs).filter!(i=>ft.isConstForReverse[i]); }
	@property movedIndices()return scope{ return iota(ft.nargs).filter!(i=>!ft.isConstForReverse[i]); }
	@property bool constLast(){ return ft.nargs&&!ft.isConstForReverse[0]&&ft.isConstForReverse[$-1]; }
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
			auto unpackNames=movedIndices.map!((i)=>"`arg_"~(ft.names[i]!=""?ft.names[i]:text(i)));
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
			auto names=(string[]).init;
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
								names~="`arg_"~(ft.names[j]!=""?ft.names[j]:text(j));
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
					names~="`arg_"~(ft.names[j]!=""?ft.names[j]:text(j));
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

Expression lowerDefine(LowerDefineFlags flags)(Expression olhs,Expression orhs,Location loc,Scope sc,bool unchecked)in{
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
		res.sstate=SemState.error;
		return res;
	}
	if(validDefLhs!flags(olhs,sc)){
		if(auto tpl=cast(TupleExp)lhs) if(!tpl.e.length&&(cast(CallExp)rhs||cast(ForgetExp)rhs)) return rhs;
		return res=new DefineExp(lhs,rhs);
	}
	Expression forget(){ return res=new ForgetExp(rhs,lhs); }
	static if(reverseMode){
		if(hasImplicitDup(olhs,sc)){ // TODO: automatically synthesize implicit dups in semantic
			if(auto tpl=cast(TupleExp)unwrap(orhs))
				if(tpl&&tpl.e.length==0) // TODO: this is a hack, support properly
					return res=new DefineExp(lhs,rhs);
			return forget();
		}
	}
	if(auto arr=cast(ArrayExp)olhs){
		auto newLhs=new TupleExp(arr.copy().e);
		newLhs.loc=olhs.loc;
		auto newRhs=orhs;
		if(auto aty=cast(ArrayTy)orhs.type){
			auto tty=tupleTy(aty.next.repeat(arr.e.length).array);
			newRhs=new TypeAnnotationExp(orhs,tty,TypeAnnotationType.coercion);
			newRhs.type=tty;
			newRhs.loc=orhs.loc;
		}
		return lowerDefine!flags(newLhs,newRhs,loc,sc,unchecked);
	}
	if(auto tpll=cast(TupleExp)olhs){
		auto tplr=new TupleExp(iota(tpll.e.length).map!(delegate Expression(i){ auto id=new Identifier(freshName); id.loc=orhs.loc; return id; }).array);
		tplr.loc=orhs.loc;
		auto d1=lowerDefine!(flags&~LowerDefineFlags.createFresh)(tplr,rhs,loc,sc,unchecked);
		enforce(tpll.e.length==tplr.e.length);
		Expression[] es;
		foreach_reverse(i;0..tpll.e.length){
			es~=lowerDefine!flags(tpll.e[i],moveExp(tplr.e[i]),loc,sc,unchecked); // TODO: evaluation order of rhs okay?
		}
		if(es.any!(x=>!x)) return null;
		auto d2=new CompoundExp(es);
		d2.loc=loc;
		return res=new CompoundExp([d1,d2]);
	}
	if(isLiftedBuiltIn(lhs)) return forget();
	if(auto tae=cast(TypeAnnotationExp)olhs){
		static if(reverseMode){
			if(olhs.type){
				if(!orhs.type||orhs.type!=tae.e.type){
					auto newRhs=new TypeAnnotationExp(rhs,tae.e.type,TypeAnnotationType.coercion);
					newRhs.loc=orhs.loc;
					return lowerDefine!flags(tae.e,newRhs,loc,sc,unchecked);
				}else return lowerDefine!flags(tae.e,orhs,loc,sc,unchecked);
			}
		}
		// TOOD: only do this if lhs is variable
		auto newRhs=new TypeAnnotationExp(rhs,tae.t,tae.annotationType);
		newRhs.loc=orhs.loc;
		return lowerDefine!flags(tae.e,newRhs,loc,sc,unchecked);
	}
	if(auto ce=cast(CatExp)olhs){
		Expression knownLength(Expression e){
			Expression res;
			scope(exit) if(res) res.loc=e.loc;
			if(auto arr=cast(ArrayExp)e) return res=constantExp(arr.e.length);
			if(auto tpl=cast(TupleExp)e) return res=constantExp(tpl.e.length);
			if(auto tae=cast(TypeAnnotationExp)e){
				if(auto vec=cast(VectorTy)tae.t)
					return vec.num.copy();
				if(auto pow=cast(PowExp)tae.t)
					return pow.e2.copy();
				return knownLength(tae.e);
			}
			if(e.type){
				if(auto vec=cast(VectorTy)e.type)
					return vec.num.copy();
			}
			return null;
		}
		auto l1=knownLength(ce.e1),l2=knownLength(ce.e2);
		if(!l1&&!l2){
			sc.error("concatenation of arrays of unknown length not supported as definition left-hand side",ce.loc);
			return error();
		}
		auto tmp=new Identifier(freshName);
		tmp.loc=olhs.loc;
		auto tmpLen(){
			auto id=new Identifier("length");
			id.loc=tmp.loc;
			return new FieldExp(tmp.copy(),id);
		}
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
		// TODO: nicer runtime error message for inconsistent array lengths?
		auto d1=lowerDefine!flags(tmp,orhs,loc,sc,unchecked);
		auto z=constantExp(0);
		z.loc=olhs.loc;
		auto l=tmpLen();
		l.loc=olhs.loc;
		auto tmp1=tmp.copy();
		tmp1.loc=orhs.loc;
		Expression s1=new SliceExp(tmp1,z,l1);
		s1.loc=tmp1.loc;
		auto tmp2=tmp.copy();
		tmp2.loc=orhs.loc;
		Expression s2=new SliceExp(tmp1,l1.copy(),l);
		s2.loc=tmp2.loc;
		auto tmpl=cast(Identifier)ce.e1?ce.e1:new Identifier(freshName);
		if(tmpl!is ce.e1){
			tmpl.loc=ce.e1.loc;
			static if(reverseMode) tmpl.type=ce.e1.type;
		}
		auto d2=lowerDefine!flags(tmpl.copy(),s1,loc,sc,unchecked);
		d2.loc=loc;
		auto tmpr=cast(Identifier)ce.e2?ce.e2:new Identifier(freshName);
		if(tmpr!is ce.e2){
			tmpr.loc=ce.e2.loc;
			static if(reverseMode) tmpr.type=ce.e2.type;
		}
		auto d3=lowerDefine!flags(tmpr.copy(),s2,loc,sc,unchecked);
		d3.loc=loc;
		auto tmp3=tmp.copy();
		tmp3.loc=orhs.loc;
		auto cat=new CatExp(tmpl.copy(),tmpr.copy());
		cat.loc=ce.loc;
		auto fe=new ForgetExp(tmp3,cat);
		fe.loc=loc;
		auto stmts=[d1,d2,d3,fe];
		if(ce.e1 !is tmpl){
			auto d4=lowerDefine!flags(ce.e1,tmpl,loc,sc,unchecked);
			d4.loc=loc;
			stmts~=d4;
		}
		if(ce.e2 !is tmpr){
			auto d5=lowerDefine!flags(ce.e2,tmpr,loc,sc,unchecked);
			d5.loc=loc;
			stmts~=d5;
		}
		return res=new CompoundExp(stmts);
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
		auto def=lowerDefine!flags(fe.var,nval,loc,sc,unchecked);
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
	if(auto ce=cast(CallExp)olhs){
		if(!ce.e.type){
			ce.e=expressionSemantic(ce.e,expSemContext(sc,ConstResult.yes,InType.no));
		}
		if(auto ft=cast(FunTy)ce.e.type){
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
				return error;
			}
			if(!unchecked&&!needWrapper&&!ft.isClassical){
				sc.error("quantum function call not supported as definition left-hand side",ce.loc); // TODO: support within reversed functions
				return error();
			}
			auto f=ce.e;
			auto r=reverseCallRewriter(ft,f.loc);
			bool simplify=r.innerNeeded;
			if(!unchecked&&!needWrapper&&r.movedType.hasClassicalComponent()){
				sc.error("reversed function cannot have classical components in 'moved' arguments", f.loc);
				return error();
			}
			if(!unchecked&&!needWrapper&&r.returnType.hasClassicalComponent()){
				sc.error("reversed function cannot have classical components in return value", f.loc);
				return error();
			}
			Expression newstm=null;
			Expression newlhs,newarg;
			if(ft.isConstForReverse.all!(x=>x==ft.isConstForReverse[0])){
				if(!ft.isConstForReverse.any){
					if(cast(TupleExp)ce.arg){
						auto tmp=new Identifier(freshName);
						newlhs=new CallExp(ce.e,tmp,ce.isSquare,ce.isClassical);
						newlhs.loc=loc;
						auto def=lowerDefine!flags(newlhs,rhs,loc,sc,unchecked);
						auto argUnpack=lowerDefine!flags(ce.arg,tmp,loc,sc,unchecked);
						return res=new CompoundExp([def,argUnpack]);
					}else{
						newlhs=ce.arg;
						newarg=orhs;
					}
				}else{
					newlhs=new TupleExp([]);
					newlhs.loc=ce.arg.loc;
					if(r.returnType==unit){
						auto tpl=new TupleExp([]);
						tpl.loc=orhs.loc;
						newstm=new DefineExp(tpl,orhs);
						newstm.loc=orhs.loc;
						newarg=ce.arg;
					}else{
						newarg=new TupleExp([ce.arg,orhs]);
						newarg.loc=ce.arg.loc.to(orhs.loc);
					}
				}
			}else if(auto tpl=cast(TupleExp)ce.arg){
				assert(ft.isTuple);
				if(ft.nargs==tpl.length){
					auto constMovedArgs=r.reorderArguments(tpl); // note: this changes order of assertion failures. ok?
					newlhs=constMovedArgs[1];
					if(simplify&&r.constIndices.empty){
						newarg=constMovedArgs[1];
					}else if(simplify&&r.returnType==unit){
						newarg=constMovedArgs[0];
					}else{
						newarg=new TupleExp([constMovedArgs[0],orhs]);
						newarg.loc=constMovedArgs[0].loc.to(orhs.loc);
					}
				}else{
					sc.error(format("wrong number of arguments to reversed function call (%s instead of %s)",tpl.length,ft.nargs),ce.loc);
					return error();
				}
			}else{
				sc.error("cannot match single tuple to function with mixed 'const' and consumed parameters",ce.loc);
				return error();
			}
			Expression reversed=null,newrhs=null;
			static if(language==silq) {
				auto op = isPrimitive(cast(CallExp)unwrap(ce.e));
				switch(op) {
					case null:
						break;
					case "dup":
						auto tpl=cast(TupleExp)newarg;
						enforce(tpl&&tpl.length==2);
						newrhs=new ForgetExp(tpl.e[1],tpl.e[0]);
						break;
					case "H", "X", "Y", "Z":
						reversed=ce.e;
						break;
					case "P":
						reversed=ce.e;
						// note: this ignores side-effects of rhs, if any
						auto negated=new UMinusExp(newarg);
						negated.loc=newarg.loc;
						newarg=negated;
						break;
					case "rX","rY","rZ":
						reversed=ce.e;
						auto tpl=cast(TupleExp)newarg;
						enforce(tpl&&tpl.length==2);
						auto negated=new UMinusExp(tpl.e[0]);
						negated.loc=tpl.e[0].loc;
						auto newtpl=new TupleExp([negated,tpl.e[1]]);
						newtpl.loc=newarg.loc;
						newarg=newtpl;
						break; // DMD bug: does not detect if this is missing
					default:
						sc.error(format("cannot reverse primitive '%s'",op),ce.e.loc);
						return error();
				}
			}
			if(!reversed&&!newrhs){
				auto checked=!unchecked;
				auto rev=getReverse(ce.e.loc,sc,Annotation.mfree,checked);
				if(rev.sstate!=SemState.completed) return error();
				reversed=new CallExp(rev,ce.e,false,false);
				reversed.loc=ce.e.loc;
			}
			if(!newrhs) newrhs=new CallExp(reversed,newarg,ce.isSquare,ce.isClassical_);
			newrhs.loc=newarg.loc;
			return lowerDefine!flags(newlhs,newrhs,loc,sc,unchecked);
		}
	}
	sc.error("not supported as definition left-hand side",olhs.loc);
	return error();
}
// rev(x:=y;) ⇒ y:=x;
// rev(x:=H(y);) ⇒ H(y):=x; ⇒ y:=reverse(H)(x);
// rev(x:=dup(y);) ⇒ dup(y):=x; ⇒ ():=reverse(dup)(x,y) ⇒ ():=forget(x=dup(y));
// rev(x:=CNOT(a,b);) ⇒ CNOT(a,b):=x; ⇒ a:=reverse(CNOT)(x,b);

Expression lowerDefine(LowerDefineFlags flags)(DefineExp e,Scope sc,bool unchecked){
	if(e.sstate==SemState.error) return e;
	if(validDefLhs!flags(e.e1,sc)) return null;
	return lowerDefine!flags(e.e1,e.e2,e.loc,sc,unchecked);
}

static if(language==silq)
FunctionDef reverseFunction(FunctionDef fd)in{
	assert(fd.scope_&&fd.ftype&&fd.ftype.isClassical()&&fd.ftype.annotation>=Annotation.mfree);
}do{
	enum flags=LowerDefineFlags.createFresh|LowerDefineFlags.reverseMode;
	enum unchecked=true; // TODO: ok?
	if(fd.reversed) return fd.reversed;
	auto sc=fd.scope_, ft=fd.ftype;
	auto asc=sc;
	foreach(meaning,ids;fd.captures){ // TODO: this is a bit hacky
		assert(ids.length&&ids.front.meaning is meaning);
		if(meaning&&meaning.scope_&&!meaning.scope_.lookup(ids.front,true,true,Lookup.probing)){
			auto scope_=meaning.scope_;
			meaning.scope_=null;
			meaning.rename=null;
			if(!scope_.insert(meaning,true))
				fd.sstate=SemState.error;
		}
	}
	auto r=reverseCallRewriter(fd.ftype,fd.loc);
	// enforce(!argTypes.any!(t=>t.hasClassicalComponent()),"reversed function cannot have classical components in consumed arguments"); // lack of classical components may not be statically known at the point of function definition due to generic parameters
	bool simplify=r.innerNeeded;
	auto ret=fd.body_.s.length?cast(ReturnExp)fd.body_.s[$-1]:null;
	if(!ret){
		sc.error("reversing early returns not supported yet",fd.loc);
		enforce(0,text("errors while reversing function"));
	}
	string cpname=null,rpname;
	bool retDefReplaced=false;
	if(auto id=cast(Identifier)ret.e){
		if(validDefLhs!flags(id,sc)){
			retDefReplaced=true;
			rpname=(id.meaning&&id.meaning.name?id.meaning.name:id).name;
		}
	}
	if(!retDefReplaced) rpname=freshName();
	Expression dom, cod;
	bool isTuple;
	bool[] isConst;
	string[] pnames;
	Expression constUnpack=null;
	if(simplify&&r.constIndices.empty){
		dom=r.returnType;
		cod=r.movedType;
		isTuple=false;
		isConst=[false];
		pnames=[rpname];
	}else if(simplify&&r.returnType==unit){
		dom=r.constType;
		cod=r.movedType;
		isTuple=r.constTuple;
		isConst=r.constIndices.map!(_=>true).array;
		pnames=r.constIndices.map!(i=>fd.params[i].name.name).array;
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
			cpname=id.name;
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
	if(simplify&&r.returnType==unit) retRhs=new TupleExp([]);
	else retRhs=new Identifier(rpname);
	retRhs.loc=ret.loc;
	retRhs.type=r.returnType;
	retRhs.loc=ret.loc;
	auto body_=new CompoundExp([]);
	body_.loc=fd.body_.loc;
	auto result=new FunctionDef(null,params,isTuple,cod,body_);
	result.isSquare=fd.isSquare;
	result.annotation=fd.annotation;
	result.scope_=sc;
	result=cast(FunctionDef)presemantic(result,sc);
	assert(!!result);
	if(fd.annotation>=Annotation.qfree && r.movedIndices.empty){
		Expression argExp;
		bool needCall=true;
		if(r.constType==unit) argExp=new TupleExp([]);
		else if(simplify&&r.returnType==unit){
			needCall=false;
		}else{
			assert(cpname!is null);
			argExp=new Identifier(cpname);
		}
		Expression call=null;
		if(needCall){
			argExp.loc=fd.loc; // TODO: use precise parameter locations
			argExp.type=r.constType;
			auto nfd=fd.copy();
			auto fun=new LambdaExp(nfd);
			fun.loc=fd.loc;
			call=new CallExp(fun,argExp,fd.isSquare,false);
			call.loc=fd.loc;
		}
		auto fe=New!ForgetExp(retRhs,call);
		fe.loc=argExp.loc;
		body_.s=[fe];
	}else{
		bool retDefNecessary=!(r.returnType==unit&&cast(TupleExp)ret.e||retDefReplaced);
		auto retDef=retDefNecessary?lowerDefine!flags(ret.e,retRhs,ret.loc,result.fscope_,unchecked):null;
		auto movedNames=r.movedIndices.map!(i=>fd.params[i].name.name).array;
		Expression[] movedTypes;
		if(r.movedTuple){
			auto tt=r.movedType.isTupleTy();
			assert(!!tt);
			movedTypes=iota(tt.length).map!(i=>tt[i]).array;
		}else movedTypes=[r.movedType];
		auto makeMoved(size_t i){
			Expression r;
			if(movedTypes[i]==unit) r=new TupleExp([]); // TODO: use last-use analysis instead
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
		body_.s=mergeCompound((constUnpack?[constUnpack]:[])~(retDef?[retDef]:[])~reverseStatements(fd.body_.s[0..$-1],fd.fscope_,unchecked)~[argRet]);
	}
	import options;
	static if(__traits(hasMember,opt,"dumpReverse")) if(opt.dumpReverse){
		writeln(fd);
		writeln("-reverse→");
		writeln(result);
	}
	result=functionDefSemantic(result,sc);
	enforce(result.sstate==SemState.completed,text("semantic errors while reversing function"));
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
		if(auto de=cast(DefExp)e){
			assert(!!de.initializer);
			return classifyStatement(de.initializer);
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
				if(e.blscope_&&e.blscope_.forgottenVars.length) return unsupported;
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

Expression[] reverseStatements(Expression[] statements,Scope sc,bool unchecked){
	statements=mergeCompound(statements);
	Expression[] classicalStatements=statements.filter!(s=>classifyStatement(s)==ComputationClass.classical).array;
	foreach(ref e;classicalStatements){
		if(auto de=cast(DefExp)e) e=de.initializer.copy();
		else e=e.copy();
	}
	Expression[] quantumStatements=statements.retro.filter!(s=>classifyStatement(s)!=ComputationClass.classical).array;
	foreach(ref e;quantumStatements) e=reverseStatement(e,sc,unchecked);
	return classicalStatements~quantumStatements;
}

Expression reverseStatement(Expression e,Scope sc,bool unchecked){
	enum flags=LowerDefineFlags.createFresh|LowerDefineFlags.reverseMode;
	if(!e) return e;
	Expression error(){
		auto res=e.copy();
		res.sstate=SemState.error;
		return res;
	}
	if(auto ce=cast(CallExp)e){
		auto te=new TupleExp([]);
		te.type=unit;
		te.loc=ce.loc;
		static if(language==silq){
			if(auto id=cast(Identifier)unwrap(ce.e)){
				if(isBuiltIn(id)){
					switch(id.name){
						case "__show","__query":
							return lowerDefine!flags(te,te,ce.loc,sc,unchecked);
						default:
							break;
					}
				}
			}
		}
		return lowerDefine!flags(ce,te,ce.loc,sc,unchecked);
	}
	if(auto ce=cast(CompoundExp)e){
		auto res=new CompoundExp(reverseStatements(ce.s,sc,unchecked));
		res.loc=ce.loc;
		static if(language==silq){
			if(ce.blscope_&&ce.blscope_.forgottenVars.length){
				sc.error("reversal of implicit forget not supported yet",ce.loc);
				res.sstate=SemState.error;
			}
		}
		return res;
	}
	if(auto ite=cast(IteExp)e){
		auto then=cast(CompoundExp)reverseStatement(ite.then,sc,unchecked);
		assert(!!then);
		auto othw=cast(CompoundExp)reverseStatement(ite.othw,sc,unchecked);
		assert(!!othw==!!ite.othw);
		auto res=new IteExp(ite.cond.copy(),then,othw);
		res.loc=ite.loc;
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
		return lowerDefine!flags(de.e2,nrhs,de.loc,sc,unchecked);
	}
	if(auto de=cast(DefExp)e){
		assert(!!de.initializer);
		return reverseStatement(de.initializer,sc,unchecked);
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
			return lowerDefine!flags(nlhs,nrhs,ae.loc,sc,unchecked);
		}
		if(auto ae=cast(BitXorAssignExp)e) return ae.copy();
		sc.error("reversal not supported yet",e.loc);
		return error();
	}
	if(auto fe=cast(ForExp)e){
		auto bdy=cast(CompoundExp)reverseStatement(fe.bdy,sc,unchecked);
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
		auto bdy=cast(CompoundExp)reverseStatement(re.bdy,sc,unchecked);
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
		return lowerDefine!flags(fe,tpl,fe.loc,sc,unchecked);
	}
	sc.error("reversal unsupported",e.loc);
	return error();
}

