// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.conversion;
import ast.expression,ast.type;
import ast.declaration:Variance;
import ast.lexer:Tok;
import util;

import std.conv, std.range, std.algorithm;


alias Ret(bool witness:true)=Conversion;
alias Ret(bool witness:false)=bool;

abstract class Conversion{
	Expression from,to; // types
	override string toString(){ return text(typeid(this),from,",",to); }
	this(Expression from,Expression to)in{
		assert(isType(from)&&isType(to));
	}do{
		this.from=from;
		this.to=to;
	}

	NoOpConversion isNoOp(){ return null; }
}

bool isNoOpConversion(Expression from,Expression to)in{
	assert(isType(from)&&isType(to));
}do{
	if(from is to) return true;
	if(from!=to) return false;
	if(auto pt1=cast(ProductTy)from)
		if(auto pt2=cast(ProductTy)to)
			if(pt1.isTuple!=pt2.isTuple)
				return false;
	return true;
}

class NoOpConversion: Conversion{
	this(Expression type){
		super(type,type);
	}
	this(Expression from,Expression to)in{
		isNoOpConversion(from,to);
	}do{
		super(from,to);
	}
	override NoOpConversion isNoOp(){ return this; }
}

class TransitiveConversion: Conversion{
	Conversion a,b;
	this(Conversion a,Conversion b)in{
		assert(a&&b&&a.to==b.from);
	}do{
		super(a.from,b.to);
	}
}

Conversion trans(Conversion a,Conversion b)in{
	assert(a&&b&&a.to==b.from);
}do{
	if(!a||!b) return null;
	if(a.from==a.to) return b;
	if(b.from==b.to) return a;
	return new TransitiveConversion(a,b);
}

pragma(inline,true)
private Ret!witness refl(bool witness)(Expression from,Expression to,TypeAnnotationType annotationType){
	if(isNoOpConversion(from,o)){
		static if(witness) return new NoOpConversion(from,to);
		else return true;
	}else return typeof(return).init;
}

class QuantumPromotion: Conversion{
	this(Expression from,Expression to)in{
		assert(from.isClassical());
		assert(!to.isClassical());
		auto cto=to.getClassical();
		assert(isNoOpConversion(from,cto));
	}do{
		super(from,to);
	}
}

class NumericConversion: Conversion{
	this(Expression from,Expression to)in{
		auto wf=whichNumeric(from);
		auto wt=whichNumeric(to);
		assert(wf&&wt&&wf<=wt);
	}do{
		super(from,to);
	}
}

class NumericCoercion: Conversion{
	bool needsCheck;
	this(Expression from,Expression to,bool needsCheck)in{
		auto wf=whichNumeric(from);
		auto wt=whichNumeric(to);
		assert(wf&&wt&&wt<wf);
	}do{
		this.needsCheck=needsCheck;
		super(from,to);
	}
}

pragma(inline,true)
Ret!witness numericToNumeric(bool witness)(Expression from,Expression to,TypeAnnotationType annotationType){
	auto wf=whichNumeric(from);
	auto wt=whichNumeric(to);
	if(wf&&wt){
		if(wf<=wt) return new NumericConversion(from,to);
		if(annotationType==TypeAnnotationType.coercion) return new NumericCoercion(from,to,true);
	}
	return typeof(return).init;
}

class TupleConversion: Conversion{ // constant-length vectors or tuples
	Conversion[] elements;
	this(Expression from,Expression to,Conversion[] elements)in{
		auto tpfrom=from.isTupleTy();
		auto tpto=to.isTupleTy();
		assert(tpfrom&&tpto);
		assert(tpfrom.length==elements.length);
		assert(tpto.length==elements.length);
		assert(iota(elements.length)
		       .all!(i=>isNoOpConversion(tpfrom[i],elements[i].from)&&
		                isNoOpConversion(elements[i].to,tpto[i])));
	}do{
		this.elements=elements;
		super(from,to);
	}
}

class VectorConversion: Conversion{
	Conversion next;
	bool checkLength;
	this(VectorTy from,VectorTy to,Conversion next,bool checkLength)in{
		assert(isNoOpConversion(from.next,next.from));
		assert(isNoOpConversion(next.to,to.next));
	}do{
		this.next=next;
		this.checkLength=checkLength;
		super(from,to);
	}
}

class VectorToArrayConversion: Conversion{
	this(VectorTy from,ArrayTy to)in{
		assert(isNoOpConversion(from.next,to.next));
	}do{
		super(from,to);
	}
}

class ArrayToVectorConversion: Conversion{
	bool checkLength;
	this(ArrayTy from,VectorTy to,bool checkLength)in{
		assert(isNoOpConversion(from.next,to.next));
	}do{
		this.checkLength=checkLength;
		super(from,to);
	}
}

class ArrayConversion: Conversion{
	Conversion next;
	this(ArrayTy from,ArrayTy to,Conversion next)in{
		assert(isNoOpConversion(from.next,next.from));
		assert(isNoOpConversion(next.to,to.next));		
	}do{
		super(from,to);
	}
}

Ret!witness tupleToTuple(bool witness)(Expression from,Expression to,TypeAnnotationType annotationType){
	auto tpl1=from.isTupleTy(), tpl2=to.isTupleTy();
	if(tpl1&&tpl2&&tpl1.length==tpl2.length){
		auto rec=iota(tpl1.length).map!(i=>typeExplicitConversion!witness(tpl1[i],tpl2[i],annotationType));
		static if(witness){
			auto elements=rec.array;
			if(!elements.all!(x=>!!x)) return null;
			return new TupleConversion(from,to,elements);
		}else return rec.all;
	}
	auto arr1=cast(ArrayTy)from, arr2=cast(ArrayTy)to;
	if(arr1&&arr2){
		auto next=typeExplicitConversion!witness(arr1.next,arr2.next,annotationType);
		if(!next) return typeof(return).init;
		static if(witness) return new ArrayConversion(arr1,arr2,next);
		else return true;
	}
	auto vec1=cast(VectorTy)from, vec2=cast(VectorTy)to;
	if(vec1&&vec2&&vec1.num.eval()==vec2.num.eval()&&typeExplicitConversion(vec1.next,vec2.next,annotationType))
		return true;
	if(vec1&&arr2&&typeExplicitConversion(vec1.next,arr2.next,annotationType))
		return true;
	if(tpl1&&vec2&&LiteralExp.makeInteger(tpl1.length)==vec2.num.eval()
	   &&iota(tpl1.length).all!(i=>typeExplicitConversion(tpl1[i],vec2.next,annotationType))
	) return true;
	if(vec1&&tpl2&&vec1.num.eval()==LiteralExp.makeInteger(tpl2.length)
	   &&iota(tpl2.length).all!(i=>typeExplicitConversion(vec1.next,tpl2[i],annotationType))
	) return true;
	if(annotationType==TypeAnnotationType.coercion){
		if((arr1||vec1)&&to==unit) return true;
		if(vec1&&vec2&&typeExplicitConversion(vec1.next,vec2.next,annotationType))
			return true;
		if(arr1&&vec2&&typeExplicitConversion(arr1.next,vec2.next,annotationType))
			return true;
		if(vec1&&tpl2&&iota(tpl2.length).all!(i=>typeExplicitConversion(vec1.next,tpl2[i],annotationType)))
			return true;
		if(tpl1&&vec2&&iota(tpl1.length).all!(i=>typeExplicitConversion(tpl1[i],vec2.next,annotationType)))
			return true;
		if(from.isClassical()&&isSubtype(to.getClassical(),from)&&from.isNumeric) return true;
	}
	return typeof(return).init;
}

class IsTupleConversion: Conversion{
	this(ProductTy from,ProductTy to)in{
		assert(from.isTuple!=to.isTuple);
		assert(isNoOpConversion(from,to.setTuple(from.isTuple)));
	}do{
		super(from,to);
	}
}

class FunctionConversion: Conversion{
	Conversion dom,cod;;
	this(ProductTy from,ProductTy to)in{
		assert(isNoOpConversion(to.dom,dom.from)&&isNoOpConversion(dom.to,from.dom));
		assert(isNoOpConversion(from.cod,cod.from)&&isNoOpConversion(cod.to,to.cod));
		assert(equal(from.isConstForSubtyping,to.isConstForSubtyping));
		assert(from.isTuple==to.isTuple);
		assert(from.annotation>=to.annotation);
		assert(from.isClassical==to.isClassical);
	}do{
		super(from,to);
	}
}

class AnnotationPun: Conversion{
	this(ProductTy from,ProductTy to)in{
		assert(isNoOpConversion(from.setAnnotation(to.annotation),to));
	}do{
		super(from,to);
	}
}

pragma(inline,true)
Ret!witness annotationPun(bool witness)(Expression from,Expression to,TypeAnnotationType annotationType)in{
	assert(annotationType==TypeAnnotationType.punning);
}do{
	auto ft1=cast(ProductTy)from, ft2=cast(ProductTy)to;
	if(ft1&&ft2){
		auto nft1=ft1.setAnnotation(ft2.annotation);
		static if(witness){
			return trans(new AnnotationPun(ft1,nft1),typeExplicitConversion!true(nft1,ft2,annotationType));
		}else return nft1==ft2;
	}
	return typeof(return).init;
}

class ℤtoIntConversion: Conversion{
	this(ℤTy from,CallExp to)in{
		assert(from.isClassical);
		assert(isInt(to));
	}do{
		super(from,to);
	}
}
class ℤtoUintConversion: Conversion{
	this(ℤTy from,CallExp to)in{
		assert(from.isClassical);
		assert(isUint(to));
	}do{
		super(from,to);
	}
}

pragma(inline,true)
Ret!witness ℤtoFixed(bool witness)(Expression from,Expression to,TypeAnnotationType annotationType){
	if(annotationType<TypeAnnotationType.conversion) return typeof(return).init;
	if(isSubtype(from,ℤt(true))){
		if(isUint(to)){
			static if(witness) return trans(new NumericConversion(from,ℤt(true)),new ℤtoUintConversion(ℤt(true),cast(CallExp)to));
			else return true;
		}
		if(isInt(to)){
			static if(witness) return trans(new NumericConversion(from,ℤt(true)),new ℤtoIntConversion(ℤt(true),cast(CallExp)to));
			else return true;
		}
	}
	return typeof(return).init;
}

class UintToℕConversion: Conversion{
	this(CallExp from,ℕTy to)in{
		assert(isUint(from));
		assert(to.isClassical());
	}do{
		super(from,to);
	}	
}

class IntToℤConversion: Conversion{
	this(CallExp from,ℤTy to)in{
		assert(isInt(from));
		assert(to.isClassical());
	}do{
		super(from,to);
	}
}

pragma(inline, true)
Ret!witness fixedToNumeric(bool witness)(Expression from,Expression to,TypeAnnotationType annotationType){
	if(annotationType<TypeAnnotationType.conversion) return typeof(return).init;
	if(!from.isClassical()) return typeof(return).init;
	if(isUint(from)&&isSubtype(ℕt(true),to)){
		static if(witness) return trans(new UintToℕConversion(cast(CallExp)from,ℕt(true)),new NumericConversion(ℕt(true),to));
		else return true;
	}
	if(isInt(from)&&isSubtype(ℤt(true),to)){
		static if(witness) return trans(new IntToℤConversion(cast(CallExp)from,ℤt(true)),new NumericConversion(ℤt(true),to));
		else return true;
	}
	/+if((isRat(from)||isFloat(from))&&isSubtype(ℚt(from.isClassical()),to))
		return true;+/
	return typeof(return).init;
}

class IntToVectorConversion: Conversion{
	bool checkLength;
	this(CallExp from,VectorTy to,bool checkLength)in{
		assert(isInt(from));
		assert(isNoOpConversion(Bool(from.isClassical()),to.next));
	}do{
		this.checkLength=checkLength;
		super(from,to);
	}
}

class UintToVectorConversion: Conversion{
	bool checkLength;
	this(CallExp from,VectorTy to,bool checkLength)in{
		assert(isUint(from));
		assert(isNoOpConversion(Bool(from.isClassical()),to.next));
	}do{
		this.checkLength=checkLength;
		super(from,to);
	}
}

pragma(inline,true)
Ret!witness fixedToVector(bool witness)(Expression from,Expression to,TypeAnnotationType type){
	if(type<TypeAnnotationType.conversion) return typeof(return).init;
	auto ce1=cast(CallExp)from;
	if(ce1&&(isInt(ce1)||isUint(ce1))){
		if(isSubtype(vectorTy(Bool(ce1.isClassical()),ce1.arg),to)||isSubtype(arrayTy(Bool(ce1.isClassical())),to)){
			static if(witness){
				auto vec=vectorTy(Bool(ce1.isClassical()),ce1.arg);
				Conversion direct=null;
				enum checkLength=false;
				if(isInt(ce1)) direct=new IntToVectorConversion(ce1,vec,checkLength);
				if(isUint(ce1)) direct=new UintToVectorConversion(ce1,vec,checkLength);
				return trans(direct,typeExplicitConversion!true(vec,to,type));
			}else return true;
		}
	}
	return typeof(return).init;
}

class VectorToIntConversion: Conversion{
	bool checkLength;
	this(VectorTy from,CallExp to,bool checkLength)in{
		assert(isNoOpConversion(Bool(to.isClassical()),from.next));
		assert(isInt(to));
	}do{
		this.checkLength=checkLength;
		super(from,to);
	}
}

class VectorToUintConversion: Conversion{
	bool checkLength;
	this(VectorTy from,CallExp to,bool checkLength)in{
		assert(isNoOpConversion(Bool(to.isClassical()),from.next));
		assert(isUint(to));
	}do{
		this.checkLength=checkLength;
		super(from,to);
	}
}

pragma(inline,true)
Ret!witness vectorToFixed(bool witness)(Expression from,Expression to,TypeAnnotationType annotationType){
	if(annotationType<TypeAnnotationType.conversion) return typeof(return).init;
	auto ce2=cast(CallExp)to;
	if(ce2&&(isInt(ce2)||isUint(ce2))){
		if(isSubtype(from,vectorTy(Bool(ce2.isClassical()),ce2.arg))||annotationType==TypeAnnotationType.coercion&&isSubtype(from,arrayTy(Bool(ce2.isClassical())))){
			static if(witness){
				auto vec=vectorTy(Bool(ce2.isClassical()),ce2.arg);
				Conversion direct=null;
				enum checkLength=false;
				if(isInt(ce2)) direct=new VectorToIntConversion(vec,ce2,checkLength);
				if(isUint(ce2)) direct=new VectorToUintConversion(vec,ce2,checkLength);
				return trans(typeExplicitConversion!true(from,vec,annotationType),direct);
			}else return true;
		}
	}
	return typeof(return).init;
}

class ParameterizedSubtypeConversion: Conversion{
	struct ParameterConversion{
		Variance variance;
		Conversion conversion;
	}
	ParameterConversion[] parameters;
	this(CallExp from,CallExp to,ParameterConversion[] parameters)in{
		// TODO
	}do{
		this.parameters=parameters;
		super(from,to);
	}
}

class TypeSubypeConversion: Conversion{
	this(Expression from,Expression to)in{
		assert(isTypeTy(from)&&isTypeTy(to));
		assert(isSubtype(from,to));
	}do{
		super(from,to);
	}
}

Ret!witness typeExplicitConversion(bool witness=false)(Expression from,Expression to,TypeAnnotationType annotationType){
	static if(witness){
		if(auto r=numericToNumeric!true(from,to,annotationType)) return r;
		if(isNoOpConversion(from,to)) return new NoOpConversion(from,to);
	}else if(isSubtype(from,to)) return true;
	if(annotationType==TypeAnnotationType.punning)
		return annotationPun!witness(from,to,annotationType);
	if(annotationType>=annotationType.conversion){
		if(auto r=ℤtoFixed!witness(from,to,annotationType)) return r;
		if(auto r=fixedToNumeric!witness(from,to,annotationType)) return r;
		if(auto r=fixedToVector!witness(from,to,annotationType)) return r;
		if(auto r=vectorToFixed!witness(from,to,annotationType)) return r;
	}
	if(auto r=tupleToTuple!witness(from,to,annotationType)) return r;
	return false;
}
bool annotateLiteral(Expression expr, Expression type){
	auto lit=cast(LiteralExp)expr, negLit=cast(UMinusExp)expr?cast(LiteralExp)(cast(UMinusExp)expr).e:null;
	if(!lit&&!negLit) return false;
	bool check(){
		if(isSubtype(expr.type,ℕt(false))&&(isUint(type)||isInt(type)))
			return true;
		if(isSubtype(expr.type,ℤt(false))&&isInt(type))
			return true;
		if(isSubtype(expr.type,ℝ(false))&&isSubtype(ℚt(true),type))
			return true;
		if(isSubtype(expr.type,ℝ(false))&&(isRat(type)||isFloat(type)))
			return true;
		if(lit&&cast(BoolTy)type&&lit.lit.type==Tok!"0"){
			auto val=ℤ(lit.lit.str);
			if(val==0||val==1) return true;
		}
		return false;
	}
	if(!check()) return false;
	auto ltype=type.getClassical();
	if(negLit){
		import ast.semantic_:minusType;
		assert(minusType(ltype)==ltype);
		negLit.type=ltype;
	}
	expr.type=ltype;
	return true;
}
Ret!witness explicitConversion(bool witness=false)(Expression expr,Expression type,TypeAnnotationType annotationType){
	if(annotationType==TypeAnnotationType.punning) return typeExplicitConversion!witness(expr.type,type,annotationType);
	if(annotateLiteral(expr,type)) return true;
	if(typeExplicitConversion(expr.type,type,annotationType)) return true;
	if(auto tpl1=cast(TupleExp)expr){
		scope(success) expr.type=tupleTy(tpl1.e.map!(e=>e.type).array);
		if(auto tpl2=type.isTupleTy()){
			return tpl1.e.length==tpl2.length&&iota(tpl1.e.length).all!(i=>explicitConversion(tpl1.e[i],tpl2[i],annotationType));
		}
		if(auto arr=cast(ArrayTy)type){
			return iota(tpl1.e.length).all!(i=>explicitConversion(tpl1.e[i],arr.next,annotationType));
		}
		if(auto vec2=cast(VectorTy)type){
			bool ok=annotationType==TypeAnnotationType.coercion;
			if(!ok){
				auto len=LiteralExp.makeInteger(tpl1.e.length);
				len.loc=expr.loc;
				auto eq=new EqExp(len,vec2.num);
				eq.loc=expr.loc;
				ok=eq.eval()==LiteralExp.makeBoolean(1);
			}
			if(ok){
				return iota(tpl1.e.length).all!(i=>explicitConversion(tpl1.e[i],vec2.next,annotationType));
			}
		}
	}
	return false;
 }
