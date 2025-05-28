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
	res.meaning=sc.lookup(res,false,false,Lookup.constant);
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
	final switch(whichNumeric(type))with(NumericType){
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
		final switch(behavior)with(OperatorBehavior){
			case default_,comparison,mul,div:
				if(isNumeric(t0)&&isNumeric(t1)&&(behavior==default_?!(cast(BoolTy)t0&&cast(BoolTy)t1):t0!=Bool(false)&&t1!=Bool(false))){
					return getSuffix(whichNumeric(t0)>whichNumeric(t1)?t0:t1);
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
	auto fullName=name~"_"~getSuffix(behavior,name,args.map!(x=>x.type));
	Expression fun=getOperatorSymbol(fullName,loc,sc);
	enforce(!!fun,text("function prototype for lowering not found: ",fullName));
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
		if(args[0].constLookup) args[0]=dupExp(args[0],args[0].loc,context.sc);
		if(args[1].constLookup) args[1]=dupExp(args[1],args[1].loc,context.sc);
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

Expression getLowering(LtExp lt,ExpSemContext context){ return makeFunctionCall(OB.comparison,"__lt",lt,[lt.e1,lt.e2],lt.loc,context); }
Expression getLowering(LeExp le,ExpSemContext context){ return makeFunctionCall(OB.comparison,"__le",le,[le.e1,le.e2],le.loc,context); }
Expression getLowering(GtExp gt,ExpSemContext context){ return makeFunctionCall(OB.comparison,"__gt",gt,[gt.e1,gt.e2],gt.loc,context); }
Expression getLowering(GeExp ge,ExpSemContext context){ return makeFunctionCall(OB.comparison,"__ge",ge,[ge.e1,ge.e2],ge.loc,context); }
Expression getLowering(EqExp eq,ExpSemContext context){ return makeFunctionCall(OB.comparison,"__eq",eq,[eq.e1,eq.e2],eq.loc,context); }
Expression getLowering(NeqExp neq,ExpSemContext context){ return makeFunctionCall(OB.comparison,"__neq",neq,[neq.e1,neq.e2],neq.loc,context); }

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
	if(!cast(AssertExp)ne2) ne2=dupExp(ne2,ne2.loc,context.sc);
	else ne2=ne2.copy();
	return expressionSemantic(new IteExp(ae.e1,toCompound(ne2),toCompound(false_)),context);
}
Expression getLowering(OrExp oe,ExpSemContext context){
	auto true_=LiteralExp.makeBoolean(true);
	true_.loc=oe.loc;
	true_.sstate=SemState.initial;
	auto ne2=oe.e2;
	if(!cast(AssertExp)ne2) ne2=dupExp(ne2,ne2.loc,context.sc);
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
