module ast.lowerings;

import std.algorithm, std.conv,std.exception;

import astopt;
import ast.lexer,ast.scope_,ast.error;
import ast.type,ast.expression,ast.semantic_;

static if(operatorLowering):

TopScope opsc=null;
Scope getOperatorScope(Location loc,ErrorHandler err){
	if(opsc) return opsc;
	import ast.parser,ast.declaration:getActualPath;
	Expression[] exprs;
	if(auto r=parseFile(getActualPath(operatorsPath),err,exprs,loc))
		return null;
	opsc=new TopScope(err);
	enforce(!!prsc);
	opsc.import_(prsc);
	int nerr=err.nerrors;
	exprs=semantic(exprs,opsc);
	return opsc;
}

Identifier getOperatorSymbol(string name,Location loc,Scope isc){
	auto sc=getOperatorScope(loc,isc.handler);
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
	if(isInt(type)) return "s";
	if(isUint(type)) return "u";
	final switch(whichNumeric(type))with(NumericType){
		case none: enforce(0, text("unsupported lowering type: ",type)); assert(0);
		case Bool: return "𝔹";
		case ℕt: return "ℕ";
		case ℤt: return "ℤ";
		case ℚt: return "ℚ";
		case ℝ: return "ℝ";
		case ℂ: return "ℂ";
	}
}

string getSuffix(R)(R types){
	if(types.length==1) return getSuffix(types[0]);
	if(types.length==2){
		auto s0=getSuffix(types[0]);
		auto s1=getSuffix(types[1]);
		return s0==s1?s0:s0~s1;
	}
	enforce(0,text("unsupported lowering arity: ",types));
	assert(0);
}

Expression makeFunctionCall(string name,Expression[] args,Location loc,ExpSemContext context){
	auto sc=context.sc;
	Expression arg;
	if(args.length!=1){
		arg=new TupleExp(args);
		arg.loc=loc;
	}else arg=args[0];
	auto fullName=name~"_"~getSuffix(args.map!(x=>x.type));
	auto fun=getOperatorSymbol(fullName,loc,sc);
	enforce(!!fun,text("function prototype for lowering not found: ",fullName));
	bool isSquare=false,isClassical=false;
	auto ce=new CallExp(fun,arg,isSquare,isClassical);
	ce.loc=loc;
	return expressionSemantic(ce,context);
}

pragma(inline,true)
void addLowering(T)(T e,ExpSemContext context){ e.lowering=getLowering(e,context); }

Expression getLowering(UMinusExp ume,ExpSemContext context){ return makeFunctionCall("__uminus",[ume.e],ume.loc,context); }
Expression getLowering(UNotExp une,ExpSemContext context){ return makeFunctionCall("__not",[une.e],une.loc,context); }
Expression getLowering(UBitNotExp ubne,ExpSemContext context){ return makeFunctionCall("__bitnot",[ubne.e],ubne.loc,context); }