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
	comparison,
	mul,
}

string getSuffix(R)(OperatorBehavior behavior,string name,R types){ // TODO: replace with some sort of language-level overloading support
	if(types.length==1) return getSuffix(types[0]);
	if(types.length==2){
		auto t0=types[0],t1=types[1];
		final switch(behavior)with(OperatorBehavior){
			case default_,comparison,mul:
				if(isNumeric(t0)&&isNumeric(t1)&&(behavior==default_?!(cast(BoolTy)t0&&cast(BoolTy)t1):t0!=Bool(false)&&t1!=Bool(false))){
					return getSuffix(whichNumeric(t0)>whichNumeric(t1)?t0:t1);
				}
				break;
		}
		auto s0=getSuffix(t0);
		auto s1=getSuffix(t1);
		final switch(behavior)with(OperatorBehavior){
			case default_,mul:
				if(s0.among("s","S","u","U")&&s1=="N") s1="Z";
				if(s1.among("s","S","u","U")&&s0=="N") s0="Z";
				break;
			case comparison:
				break;
		}
		return s0==s1?s0:s0~s1;
	}
	enforce(0,text("unsupported lowering arity: ",types));
	assert(0);
}

Expression makeFunctionCall(OperatorBehavior behavior,string name,Expression[] args,Location loc,ExpSemContext context){
	auto sc=context.sc;
	Expression arg;
	if(args.length!=1){
		arg=new TupleExp(args);
		arg.loc=loc;
	}else arg=args[0];
	auto fullName=name~"_"~getSuffix(behavior,name,args.map!(x=>x.type));
	auto fun=getOperatorSymbol(fullName,loc,sc);
	enforce(!!fun,text("function prototype for lowering not found: ",fullName));
	bool isSquare=false,isClassical=false;
	auto ce=new CallExp(fun,arg,isSquare,isClassical);
	ce.loc=loc;
	return expressionSemantic(ce,context);
}

private alias OB=OperatorBehavior;
Expression getLowering(UMinusExp ume,ExpSemContext context){ return makeFunctionCall(OB.default_,"__uminus",[ume.e],ume.loc,context); }
Expression getLowering(UNotExp une,ExpSemContext context){ return makeFunctionCall(OB.default_,"__not",[une.e],une.loc,context); }
Expression getLowering(UBitNotExp ubne,ExpSemContext context){ return makeFunctionCall(OB.default_,"__bitnot",[ubne.e],ubne.loc,context); }

Expression getLowering(AddExp ae,ExpSemContext context){ return makeFunctionCall(OB.default_,"__add",[ae.e1,ae.e2],ae.loc,context); }
Expression getLowering(SubExp se,ExpSemContext context){ return makeFunctionCall(OB.default_,"__sub",[se.e1,se.e2],se.loc,context); }
Expression getLowering(NSubExp nse,ExpSemContext context){ return makeFunctionCall(OB.default_,"__nsub",[nse.e1,nse.e2],nse.loc,context); }

Expression getLowering(MulExp me,ExpSemContext context){ return makeFunctionCall(OB.mul,"__mul",[me.e1,me.e2],me.loc,context); }

Expression getLowering(LtExp lt,ExpSemContext context){ return makeFunctionCall(OB.comparison,"__lt",[lt.e1,lt.e2],lt.loc,context); }
Expression getLowering(LeExp le,ExpSemContext context){ return makeFunctionCall(OB.comparison,"__le",[le.e1,le.e2],le.loc,context); }
Expression getLowering(GtExp gt,ExpSemContext context){ return makeFunctionCall(OB.comparison,"__gt",[gt.e1,gt.e2],gt.loc,context); }
Expression getLowering(GeExp ge,ExpSemContext context){ return makeFunctionCall(OB.comparison,"__ge",[ge.e1,ge.e2],ge.loc,context); }
Expression getLowering(EqExp eq,ExpSemContext context){ return makeFunctionCall(OB.comparison,"__eq",[eq.e1,eq.e2],eq.loc,context); }
Expression getLowering(NeqExp neq,ExpSemContext context){ return makeFunctionCall(OB.comparison,"__neq",[neq.e1,neq.e2],neq.loc,context); }
