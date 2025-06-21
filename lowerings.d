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
		return intTy.isSigned ? type.isClassical()?"S":"s" : type.isClassical?"U":"u";
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
}

string getSuffix(R)(OperatorBehavior behavior,string name,R types){ // TODO: replace with some sort of language-level overloading support
	if(types.length==1) return getSuffix(types[0].eval());
	if(types.length==2){
		auto t0=types[0].eval(),t1=types[1].eval();
		auto num0=isNumericTy(t0), num1=isNumericTy(t1);
		final switch(behavior)with(OperatorBehavior){
			case default_:
				if(num0 && num1 && !(num0 == NumericType.Bool && num1 == NumericType.Bool)){
					return getSuffix(num0>num1?t0:t1);
				}
				break;
			case comparison, mul, div:
				if(num0 && num1 && t0 != Bool(false) && t1 != Bool(false)){
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
		}
		auto s0=getSuffix(t0);
		auto s1=getSuffix(t1);
		final switch(behavior)with(OperatorBehavior){
			case default_,nsub,mul,andb:
				if(s0.among("s","S","u","U")&&s1=="N") s1="Z";
				if(s1.among("s","S","u","U")&&s0=="N") s0="Z";
				break;
			case comparison,div,mod:
				break;
			case pow:
				if(s0=="B"&&!s1.among("b","B","N")) s0="N";
				break;
			case cat:
				break;
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
	auto e0=args[0],e1=args[1];
	if(!cast(TupleTy)e0.type&&!cast(ArrayTy)e0.type&&!cast(VectorTy)e0.type){
		assert(!cast(TupleTy)e1.type&&!cast(ArrayTy)e1.type&&!cast(VectorTy)e1.type);
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
	Parameter makeParam(Expression arg){
		auto name=new Identifier(freshName());
		name.loc=arg.loc;
		auto dtype=arg.type.copy(cargs);
		dtype.loc=arg.loc;
		auto r=new Parameter(true,name,dtype);
		r.loc=arg.loc;
		return r;
	}
	auto params=[makeParam(e0),makeParam(e1)];
	auto p0=params[0].name.copy(cargs),p1=params[1].name.copy(cargs);
	p0.type=e0.type,p1.type=e1.type;
	Expression[] body_;
	auto doneName=new Identifier(freshName());
	doneName.loc=loc;
	auto ddef=new DefineExp(doneName,makeConst(false));
	ddef.loc=loc;
	body_~=ddef;
	auto resultName=new Identifier(freshName());
	resultName.loc=loc;
	auto rdef=new DefineExp(resultName,makeConst(false));
	rdef.loc=loc;
	body_~=rdef;
	void checkDone(ref Expression[] s,Expression e){
		auto cond=new UNotExp(doneName.copy(cargs));
		cond.loc=e.loc;
		CompoundExp then;
		if(auto ce=cast(CompoundExp)e){
			then=ce;
		}else{
			then=new CompoundExp([e]);
			then.loc=e.loc;
		}
		auto r=new IteExp(cond,then,null);
		r.loc=e.loc;
		s~=r;
	}
	void stm(ref Expression[] s,Expression e){
		// s~=e;
		checkDone(s,e);
	}
	void ret(ref Expression[] s,Expression e,bool check=false){
		/+auto r=new ReturnExp(e);
		r.loc=e.loc;
		stm(s,r);+/
		auto cond=new UNotExp(doneName.copy(cargs));
		cond.loc=e.loc;
		auto sdone=new AssignExp(doneName.copy(cargs),makeConst(true));
		sdone.loc=e.loc;
		if(!check) s~=sdone;
		auto sret=new AssignExp(resultName.copy(cargs),e);
		sret.loc=e.loc;
		if(!check) s~=sret;
		else{
			auto ce=new CompoundExp([sdone,sret]);
			ce.loc=e.loc;
			checkDone(s,ce);
		}
	}
	void iterate(ref Expression[] body_,Expression p0,Expression p1){
		Expression[] r;
		static Expression makeIndex(Expression p,Expression t,Expression i){
			auto r=new IndexExp(p,i);
			r.loc=p.loc;
			r.type=indexType(t,i);
			assert(!!r.type,text(p," ",t," ",i," ",r," ",r.type));
			return r;
		}
		auto tt0=p0.type.isTupleTy(),tt1=p1.type.isTupleTy();
		if(tt0&&tt1&&(cast(TupleTy)tt0||cast(TupleTy)tt1)){
			foreach(i;0..min(tt0.length,tt1.length)){
				auto i0=LiteralExp.makeInteger(i);
				i0.loc=loc;
				auto i1=LiteralExp.makeInteger(i);
				i1.loc=loc;
				auto np0=makeIndex(p0.copy(cargs),p0.type,i0),np1=makeIndex(p1.copy(cargs),p1.type,i1);
				iterate(body_,np0,np1);
			}
			return;
		}
		Expression next0=null,next1=null;
		if(auto vt0=cast(VectorTy)p0.type) next0=vt0.next;
		else if(auto at0=cast(ArrayTy)p0.type) next0=at0.next;
		if(auto vt1=cast(VectorTy)p1.type) next1=vt1.next;
		else if(auto at1=cast(ArrayTy)p1.type) next1=at1.next;
		void doComparison(ref Expression[] body_,Expression p0,Expression p1){
			auto cond=new NeqExp(p0.copy(cargs),p1.copy(cargs));
			cond.loc=loc;
			Expression[] bdy;
			ret(bdy,makeMismatch(p0,p1));
			auto then=new CompoundExp(bdy);
			then.loc=loc;
			auto ite=new IteExp(cond,then,null);
			ite.loc=loc;
			stm(body_,ite);
		}
		if((next0||tt0)&&(next1||tt1)){
			auto lenName=new Identifier(Id.s!"length");
			lenName.loc=loc;
			auto len0=new FieldExp(p0.copy(cargs),lenName);
			len0.loc=loc;
			auto len1=new FieldExp(p1.copy(cargs),lenName.copy(cargs));
			len1.loc=loc;
			Expression len;
			if(cast(EqExp)original||cast(NeqExp)original){
				auto cond=new NeqExp(len0,len1);
				cond.loc=loc;
				Expression[] s;
				ret(s,makeConst(!!cast(NeqExp)original));
				auto then=new CompoundExp(s);
				then.loc=loc;
				auto ite=new IteExp(cond,then,null);
				ite.loc=loc;
				stm(body_,ite);
				len=len0.copy(cargs);
			}else if(next0&&next1){
				auto cond=new LeExp(len0.copy(cargs),len1.copy(cargs));
				cond.loc=loc;
				auto then=new CompoundExp([len0.copy(cargs)]),othw=new CompoundExp([len1.copy(cargs)]);
				then.loc=loc,othw.loc=loc;
				auto minExp=new IteExp(cond,then,othw);
				minExp.loc=loc;
				len=minExp;
			}else{
				assert(!!tt0^!!tt1);
				len=tt0?len1.copy(cargs):len0.copy(cargs);
			}
			if(next0&&next1){
				auto i0=new Identifier(freshName());
				i0.loc=loc;
				i0.type=ℤt(true);
				auto i1=new Identifier(i0.id);
				i1.loc=loc;
				i1.type=ℤt(true);
				// TODO: in principle runtime indexing could fail for tuples even if comparable to non-tuple
				auto np0=makeIndex(p0.copy(cargs),p0.type,i0),np1=makeIndex(p1.copy(cargs),p1.type,i1);
				Expression[] s;
				iterate(s,np0,np1);
				auto forBdy=new CompoundExp(s);
				forBdy.loc=loc;
				auto for_=new ForExp(i0.copy(cargs),false,makeConst(0),null,true,len,forBdy);
				for_.loc=loc;
				stm(body_,for_);
			}else{
				assert(!!tt0^!!tt1);
				auto clen=tt0?tt0.length:tt1.length;
				foreach(i;0..clen){
					auto bound=LiteralExp.makeInteger(i);
					bound.loc=loc;
					auto cond=new LtExp(bound,len.copy(cargs));
					cond.loc=loc;
					Expression[] s;
					auto i0=LiteralExp.makeInteger(i);
					i0.loc=loc;
					auto i1=LiteralExp.makeInteger(i);
					i1.loc=loc;
					auto np0=makeIndex(p0.copy(cargs),p0.type,i0),np1=makeIndex(p1.copy(cargs),p1.type,i1);
					iterate(s,np0,np1);
					auto then=new CompoundExp(s);
					then.loc=loc;
					auto ite=new IteExp(cond,then,null);
					ite.loc=loc;
					body_~=ite;
				}
			}
			if(!(cast(EqExp)original||cast(NeqExp)original))
				doComparison(body_,len0.copy(cargs),len1.copy(cargs));
		}else doComparison(body_,p0,p1);
	}
	iterate(body_,p0,p1);
	ret(body_,makeMismatch(null,null),true);
	auto r=new ReturnExp(resultName.copy(cargs));
	r.loc=loc;
	body_~=r;
	auto fbdy=new CompoundExp(body_);
	fbdy.loc=loc;
	auto fd=new FunctionDef(null,params,true,null,fbdy);
	fd.annotation=Annotation.qfree;
	fd.loc=loc;
	auto lambda=new LambdaExp(fd);
	lambda.fd=lambda.orig.copy(cargs); // TODO: this is a hack, also, need to insert captures
	lambda.loc=loc;
	auto arg=new TupleExp(args);
	arg.loc=loc;
	auto ce=new CallExp(lambda,arg,false,false);
	ce.loc=loc;
	return expressionSemantic(ce,context);
}

Expression makeFunctionCall(OperatorBehavior behavior,string name,Expression original,Expression[] args,Location loc,ExpSemContext context){
	foreach(arg;args){
		if(isEmpty(arg.type)){
			arg.constLookup=context.constResult;
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
		fullName=name~"_"~getSuffix(behavior,name,args.map!(x=>x.type));
		fun=getOperatorSymbol(fullName,loc,sc);
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
Expression getLowering(AndExp ae,ExpSemContext context){
	auto false_=LiteralExp.makeBoolean(false);
	false_.loc=ae.loc;
	false_.sstate=SemState.initial;
	auto ne2=ae.e2;
	if(!cast(AssertExp)ne2) ne2=dupExp(ne2,ne2.loc,context);
	else ne2=ne2.copy();
	return expressionSemantic(new IteExp(ae.e1,toCompound(ne2),toCompound(false_)),context);
}
Expression getLowering(OrExp oe,ExpSemContext context){
	auto true_=LiteralExp.makeBoolean(true);
	true_.loc=oe.loc;
	true_.sstate=SemState.initial;
	auto ne2=oe.e2;
	if(!cast(AssertExp)ne2) ne2=dupExp(ne2,ne2.loc,context);
	else ne2=ne2.copy();
	return expressionSemantic(new IteExp(oe.e1,toCompound(true_),toCompound(ne2)),context);
}


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
		static if([Tok!"+←",Tok!"-←",Tok!"sub←",Tok!"⊕←",Tok!"~←"].canFind(op)){
			if(e.e1.type.isClassical()&&op!=Tok!"~←") return toAssign();
			auto id1=cast(Identifier)e.e1;
			if(!id1) return null; // TODO: lower via `with x:=a do x op= b`
			static if(op==Tok!"+←") enum name="__add_assign", ob=OB.default_;
			else static if(op==Tok!"-←") enum name="__sub_assign", ob=OB.default_;
			else static if(op==Tok!"sub←") enum name="__nsub_assign", ob=OB.nsub;
			else static if(op==Tok!"⊕←") enum name="__xorb_assign", ob=OB.mul;
			else static if(op==Tok!"~←") enum name="__cat", ob=OB.cat;
			else static assert(0);
			auto fc=makeFunctionCall(ob,name,e,[id1,e.e2],e.loc,ExpSemContext(sc,ConstResult.no,InType.no));
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
		}else return toAssign();
	}
}
