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
	override string toString(){ return text(typeid(this),"(",from,",",to,")"); }
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
	if(from!=to){
		from=from.eval();
		to=to.eval();
		if(from!=to) return false;
	}
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
	override string toString(){ return text(typeid(this),"{",a,"; ",b,"}"); }
	this(Conversion a,Conversion b)in{
		assert(a&&b&&a.to==b.from);
	}do{
		this.a=a;
		this.b=b;
		super(a.from,b.to);
	}
}

Conversion trans(Conversion a,Conversion b)in{
	assert(a&&b&&a.to==b.from);
}do{
	if(!a||!b) return null;
	if(isNoOpConversion(a.from,a.to)) return b;
	if(isNoOpConversion(b.from,b.to)) return a;
	return new TransitiveConversion(a,b);
}

Conversion refl(Expression from,Expression to=null){
	if(!to) to=from;
	if(isNoOpConversion(from,to))
		return new NoOpConversion(from,to);
	return null;
}

class TypeConversion: Conversion{
	this(Expression from,Expression to)in{
		assert(from.isTypeTy&&to.isTypeTy);
		assert(isSubtype(from,to));
	}do{
		super(from,to);
	}
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
		assert(wf&&wt&&wf<wt);
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
		if(wf<=wt){
			static if(witness) {
				if(wf==wt) return new NoOpConversion(from,to);
				return new NumericConversion(from,to);
			}
			else return true;
		}
		if(annotationType==TypeAnnotationType.coercion&&from.isClassical()&&isSubtype(to.getClassical(),from)){
			static if(witness) return new NumericCoercion(from,to,true);
			else return true;
		}
	}
	return typeof(return).init;
}

class TupleConversion: Conversion{ // constant-length vectors or tuples
	Conversion[] elements;
	override string toString(){ return text(typeid(this),"[",elements.map!(e=>e.toString()).join(","),"]"); }
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
	override string toString(){ return text(typeid(this),"(",next,")"); }
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
	override string toString(){ return text(typeid(this),"(",next,")"); }
	this(ArrayTy from,ArrayTy to,Conversion next)in{
		assert(isNoOpConversion(from.next,next.from));
		assert(isNoOpConversion(next.to,to.next));
	}do{
		this.next=next;
		super(from,to);
	}
}

Ret!witness tupleToTuple(bool witness)(Expression from,Expression to,TypeAnnotationType annotationType){
	auto tpl1=from.isTupleTy(), tpl2=to.isTupleTy();
	if(tpl1&&tpl2&&tpl1.length==tpl2.length){
		auto next=iota(tpl1.length).map!(i=>typeExplicitConversion!witness(tpl1[i],tpl2[i],annotationType));
		static if(witness){
			auto elements=next.array;
			if(elements.all!(x=>!!x)) return new TupleConversion(from,to,elements);
		}else if(next.all) return true;
	}
	auto arr1=cast(ArrayTy)from, arr2=cast(ArrayTy)to;
	if(arr1&&arr2){
		if(auto next=typeExplicitConversion!witness(arr1.next,arr2.next,annotationType)){
			static if(witness) return new ArrayConversion(arr1,arr2,next);
			else return true;
		}
	}
	if(tpl1&&arr2){
		auto next=iota(tpl1.length).map!(i=>typeExplicitConversion!witness(tpl1[i],arr2.next,annotationType));
		static if(witness){
			auto elements=next.array;
			if(elements.all!(x=>!!x)){
				auto nvec2=vectorTy(arr2.next,LiteralExp.makeInteger(tpl1.length));
				return trans(new TupleConversion(from,nvec2,elements),new VectorToArrayConversion(nvec2,arr2));
			}
		}else if(next.all) return true;
	}
	auto vec1=cast(VectorTy)from, vec2=cast(VectorTy)to;
	if(vec1&&vec2&&vec1.num.eval()==vec2.num.eval()){
		if(auto next=typeExplicitConversion!witness(vec1.next,vec2.next,annotationType)){
			static if(witness){
				enum checkLength=false;
				return new VectorConversion(vec1,vec2,next,false);
			}else return true;
		}
	}
	if(vec1&&arr2){
		if(auto next=typeExplicitConversion(vec1.next,arr2.next,annotationType)){
			static if(witness) return new VectorToArrayConversion(vec1,arr2);
			else return true;
		}
	}
	if(tpl1&&vec2&&LiteralExp.makeInteger(tpl1.length)==vec2.num.eval()){ // TODO: redundant?
		auto next=iota(tpl1.length).map!(i=>typeExplicitConversion!witness(tpl1[i],vec2.next,annotationType));
		static if(witness){
			auto elements=next.array;
			if(elements.all!(x=>!!x)) return new TupleConversion(from,to.eval(),elements);
		}else if(next.all) return true;
	}
	if(vec1&&tpl2&&vec1.num.eval()==LiteralExp.makeInteger(tpl2.length)){ // TODO: redundant?
		auto next=iota(tpl2.length).map!(i=>typeExplicitConversion!witness(vec1.next,tpl2[i],annotationType));
		static if(witness){
			auto elements=next.array;
			if(elements.all!(x=>!!x)) return new TupleConversion(from.eval(),to,elements);
		}else if(next.all) return true;
	}
	if(annotationType==TypeAnnotationType.coercion){
		enum checkLength=true;
		if((arr1||vec1)&&to==unit){ // TODO: redundant?
			static if(witness){
				if(arr1){
					auto nvec1=vectorTy(arr1.next,LiteralExp.makeInteger(0));
					return trans(new ArrayToVectorConversion(arr1,nvec1,checkLength),new TupleConversion(nvec1,unit,[]));
				}
				if(vec1){
					auto nvec1=vectorTy(vec1.next,LiteralExp.makeInteger(0));
					return trans(new VectorConversion(vec1,nvec1,refl(vec1.next),checkLength),new TupleConversion(nvec1,unit,[]));
				}
			}else return true;
		}
		if(vec1&&vec2){
			if(auto next=typeExplicitConversion!witness(vec1.next,vec2.next,annotationType)){
				static if(witness) return new VectorConversion(vec1,vec2,next,checkLength);
				else return true;
			}
		}
		if(arr1&&vec2){
			if(auto next=typeExplicitConversion!witness(arr1.next,vec2.next,annotationType)){
				static if(witness){
					auto nvec1=vectorTy(arr1.next,vec2.num);
					return trans(new ArrayToVectorConversion(arr1,nvec1,checkLength),new VectorConversion(nvec1,vec2,next,false));
				}else return true;
			}
		}
		if(vec1&&tpl2){
			auto next=iota(tpl2.length).map!(i=>typeExplicitConversion!witness(vec1.next,tpl2[i],annotationType));
			static if(witness){
				auto elements=next.array;
				if(elements.all!(x=>!!x)){
					auto nvec1=vectorTy(vec1.next,LiteralExp.makeInteger(tpl2.length));
					return trans(new VectorConversion(vec1,nvec1,refl(vec1.next),checkLength),new TupleConversion(nvec1,to,elements));
				}
			}else if(next.all) return true;
		}
		if(tpl1&&vec2){
			auto next=iota(tpl1.length).map!(i=>typeExplicitConversion!witness(tpl1[i],vec2.next,annotationType));
			static if(witness){
				auto elements=next.array;
				if(elements.all!(x=>!!x)){
					auto nvec2=vectorTy(vec2.next,LiteralExp.makeInteger(tpl1.length));
					return trans(new TupleConversion(from,nvec2,elements),new VectorConversion(nvec2,vec2,refl(vec2.next),checkLength));
				}
			}else if(next.all) return true;
		}
		if(arr1&&tpl2){
			auto next=iota(tpl2.length).map!(i=>typeExplicitConversion!witness(arr1.next,tpl2[i],annotationType));
			static if(witness){
				auto elements=next.array;
				if(elements.all!(x=>!!x)){
					auto nvec1=vectorTy(arr1.next,LiteralExp.makeInteger(tpl2.length));
					return trans(new ArrayToVectorConversion(arr1,nvec1,checkLength),new TupleConversion(nvec1,to,elements));
				}
			}else if(next.all) return true;
		}
	}
	return typeof(return).init;
}

class FunctionConversion: Conversion{
	Id[] names;
	Conversion dom,cod;
	this(ProductTy from,ProductTy to,Id[] names,Conversion dom,Conversion cod)in{
		assert(isNoOpConversion(to.dom,dom.from)&&isNoOpConversion(dom.to,from.dom));
		assert(from.names==names&&to.names==names);
		assert(isNoOpConversion(cod.from,from.cod)&&isNoOpConversion(to.cod,cod.to),text(to.cod," ",cod.to));
		assert(equal(from.isConstForSubtyping,to.isConstForSubtyping)); // TODO: explicit isConst conversion for classical parameters?
		assert(from.isTuple==to.isTuple);
		assert(from.annotation>=to.annotation);
		assert(from.isClassical==to.isClassical);
	}do{
		super(from,to);
		this.names=names;
		this.dom=dom;
		this.cod=cod;
	}
}

pragma(inline,true)
Ret!witness functionToFunction(bool witness)(Expression from,Expression to,TypeAnnotationType annotationType){
	if(from.isClassical!=to.isClassical) return typeof(return).init;
	auto ft1=cast(ProductTy)from,ft2=cast(ProductTy)to;
	if(!ft1||!ft2) return typeof(return).init;
	if(!(ft1.annotation>=ft2.annotation)) return typeof(return).init;
	if(ft1.isTuple!=ft2.isTuple){
		if(!ft1.isTuple){
			auto nft1=ft1.setTuple(true);
			assert(!!nft1);
			static if(witness) return typeExplicitConversion!witness(nft1,ft2,annotationType);
			else return typeExplicitConversion!witness(nft1,ft2);
		}
		if(!ft2.isTuple){
			auto nft2=ft2.setTuple(true);
			assert(!!nft2);
			static if(witness) return typeExplicitConversion!witness(ft1,nft2,annotationType);
			else return typeExplicitConversion!witness(ft1,nft2);
		}
	}
	if(!equal(ft1.isConstForSubtyping,ft2.isConstForSubtyping)) return typeof(return).init;
	if(ft1.names.length!=ft2.names.length) return typeof(return).init;
	Id[] names;
	if(ft1.names!=ft2.names){
		names=ft1.freshNames(ft2);
	}else names=ft1.names;
	ft1=ft1.relabelAll(names);
	ft2=ft2.relabelAll(names);
	// TODO: support non-subtyping conversions in dom and cod?
	auto dom=typeExplicitConversion!witness(ft2.dom,ft1.dom,TypeAnnotationType.annotation);
	if(!dom) return typeof(return).init;
	auto cod=typeExplicitConversion!witness(ft1.cod,ft2.cod,TypeAnnotationType.annotation);
	if(!cod) return typeof(return).init;
	return new FunctionConversion(ft1,ft2,names,dom,cod);
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

class ℤtoFixedConversion: Conversion{
	this(ℤTy from,Expression to)in{
		assert(from.isClassical);
		auto toInt=isFixedIntTy(to);
		assert(toInt);
		assert(toInt.isClassical);
	}do{
		super(from,to);
	}
}

pragma(inline,true)
Ret!witness ℤtoFixed(bool witness)(Expression from,Expression to,TypeAnnotationType annotationType){
	if(annotationType<TypeAnnotationType.conversion) return typeof(return).init;
	if(isSubtype(from,ℤt(true))){
		if(isFixedIntTy(to)){
			static if(witness) return trans(numericToNumeric!witness(from,ℤt(true),TypeAnnotationType.annotation),new ℤtoFixedConversion(ℤt(true),to));
			else return true;
		}
	}
	return typeof(return).init;
}

class UintToℕConversion: Conversion{
	this(Expression from,ℕTy to)in{
		assert(isUint(from));
		assert(to.isClassical());
	}do{
		super(from,to);
	}
}

class IntToℤConversion: Conversion{
	this(Expression from,ℤTy to)in{
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
	if(auto fromInt=isFixedIntTy(from)){
		if(!fromInt.isSigned && isSubtype(ℕt(true),to)){
			static if(witness) return trans(new UintToℕConversion(from,ℕt(true)),numericToNumeric!witness(ℕt(true),to,TypeAnnotationType.annotation));
			else return true;
		}
		if(fromInt.isSigned && isSubtype(ℤt(true),to)){
			static if(witness) return trans(new IntToℤConversion(from,ℤt(true)),numericToNumeric!witness(ℤt(true),to,TypeAnnotationType.annotation));
			else return true;
		}
	}
	/+if((isRat(from)||isFloat(from))&&isSubtype(ℚt(from.isClassical()),to))
		return true;+/
	return typeof(return).init;
}

class FixedToVectorConversion: Conversion{
	bool checkLength;
	this(Expression from,VectorTy to,bool checkLength)in{
		assert(isFixedIntTy(from));
		assert(isNoOpConversion(Bool(from.isClassical()),to.next));
	}do{
		this.checkLength=checkLength;
		super(from,to);
	}
}

pragma(inline,true)
Ret!witness fixedToVector(bool witness)(Expression from,Expression to,TypeAnnotationType type){
	if(type<TypeAnnotationType.conversion) return typeof(return).init;
	if(auto fromInt=isFixedIntTy(from)){
		if(isSubtype(vectorTy(Bool(fromInt.isClassical),fromInt.bits),to)||isSubtype(arrayTy(Bool(fromInt.isClassical)),to)){
			static if(witness){
				auto vec=vectorTy(Bool(fromInt.isClassical),fromInt.bits);
				Conversion direct=null;
				enum checkLength=false;
				direct=new FixedToVectorConversion(from,vec,checkLength);
				return trans(direct,typeExplicitConversion!true(vec,to,type));
			}else return true;
		}
	}
	return typeof(return).init;
}

class VectorToFixedConversion: Conversion{
	bool checkLength;
	this(VectorTy from,Expression to,bool checkLength)in{
		assert(isNoOpConversion(Bool(to.isClassical()),from.next));
		assert(isFixedIntTy(to));
	}do{
		this.checkLength=checkLength;
		super(from,to);
	}
}

pragma(inline,true)
Ret!witness vectorToFixed(bool witness)(Expression from,Expression to,TypeAnnotationType annotationType){
	if(annotationType<TypeAnnotationType.conversion) return typeof(return).init;
	if(auto toInt=isFixedIntTy(to)){
		if(isSubtype(from,vectorTy(Bool(toInt.isClassical),toInt.bits))||annotationType==TypeAnnotationType.coercion&&isSubtype(from,arrayTy(Bool(toInt.isClassical)))){
			static if(witness){
				auto vec=vectorTy(Bool(toInt.isClassical),toInt.bits);
				Conversion direct=null;
				enum checkLength=false;
				direct=new VectorToFixedConversion(vec,to,checkLength);
				return trans(typeExplicitConversion!true(from,vec,annotationType),direct);
			}else return true;
		}
	}
	return typeof(return).init;
}

/+
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
+/

Ret!witness typeExplicitConversion(bool witness=false)(Expression from,Expression to,TypeAnnotationType annotationType){
	static if(witness){
		if(isNoOpConversion(from,to)) return new NoOpConversion(from,to);
		if(isTypeTy(from)&&isTypeTy(to)&&isSubtype(from,to)) return new TypeConversion(from,to);
		if(from.isClassical()&&!to.isClassical()){
			auto cto=to.getClassical();
			if(auto r=typeExplicitConversion!true(from,cto,annotationType))
				return trans(r,new QuantumPromotion(cto,to));
		}
		if(auto r=functionToFunction!true(from,to,annotationType)) return r;
	}else if(isSubtype(from,to)) return true;
	if(auto r=numericToNumeric!witness(from,to,annotationType)) return r;
	if(annotationType==TypeAnnotationType.punning)
		return annotationPun!witness(from,to,annotationType);
	if(annotationType>=annotationType.conversion){
		if(auto r=ℤtoFixed!witness(from,to,annotationType)) return r;
		if(auto r=fixedToNumeric!witness(from,to,annotationType)) return r;
		if(auto r=fixedToVector!witness(from,to,annotationType)) return r;
		if(auto r=vectorToFixed!witness(from,to,annotationType)) return r;
	}
	if(auto r=tupleToTuple!witness(from,to,annotationType)) return r;
	return typeof(return).init;
}
bool isLiteral(Expression expr){
	auto lit=cast(LiteralExp)expr, negLit=cast(UMinusExp)expr?cast(LiteralExp)(cast(UMinusExp)expr).e:null;
	return lit||negLit;
}
bool annotateLiteral(Expression expr, Expression type){
	auto lit=cast(LiteralExp)expr, negLit=cast(UMinusExp)expr?cast(LiteralExp)(cast(UMinusExp)expr).e:null;
	if(!lit&&!negLit) return false;
	bool check(){
		if(isSubtype(expr.type,ℕt(false))&&isFixedIntTy(type))
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
	if(annotateLiteral(expr,type)){
		static if(witness) return refl(type);
		else return true;
	}
	if(auto r=typeExplicitConversion!witness(expr.type,type,annotationType)) return r;
	if(auto tpl1=cast(TupleExp)expr){
		void update(){ expr.type=tupleTy(tpl1.e.map!(e=>e.type).array); }
		if(auto tpl2=type.isTupleTy()){
			if(tpl1.e.length!=tpl2.length) return typeof(return).init;
			auto next=iota(tpl1.e.length).map!(i=>explicitConversion!witness(tpl1.e[i],tpl2[i],annotationType));
			static if(witness){
				auto elements=next.array;
				update();
				if(elements.all!(x=>!!x)){
					if(elements.all!(x=>!!cast(NoOpConversion)x)) return new NoOpConversion(expr.type);
					return new TupleConversion(expr.type,type,elements);
				}
			}else{ scope(exit) update(); return next.all; }
		}
		if(auto arr2=cast(ArrayTy)type){
			auto next=iota(tpl1.e.length).map!(i=>explicitConversion!witness(tpl1.e[i],arr2.next,annotationType));
			static if(witness){
				auto elements=next.array;
				update();
				if(elements.all!(x=>!!x)){
					auto nvec2=vectorTy(arr2.next,LiteralExp.makeInteger(tpl1.e.length));
					return trans(new TupleConversion(expr.type,nvec2,elements),new VectorToArrayConversion(nvec2,arr2));
				}
			}else{ scope(exit) update(); return next.all; }
		}
		if(auto vec2=cast(VectorTy)type){
			bool checkLength=annotationType==TypeAnnotationType.coercion;
			bool ok=checkLength;
			if(witness||!ok){
				auto len=LiteralExp.makeInteger(tpl1.e.length);
				len.loc=expr.loc;
				auto eq=new EqExp(len,vec2.num);
				eq.loc=expr.loc;
				bool proven=eq.eval()==LiteralExp.makeBoolean(1);
				if(proven) checkLength=false;
				ok|=proven;
			}
			if(ok){
				auto next=iota(tpl1.e.length).map!(i=>explicitConversion!witness(tpl1.e[i],vec2.next,annotationType));
				static if(witness){
					auto elements=next.array;
					update();
					if(elements.all!(x=>!!x)){
						auto nvec2=vectorTy(vec2.next,LiteralExp.makeInteger(tpl1.e.length));
						return trans(new TupleConversion(expr.type,nvec2,elements),new VectorConversion(nvec2,vec2,refl(vec2.next),checkLength));
					}
				}else{ scope(exit) update(); return next.all; }

			}
		}
	}
	return typeof(return).init;
 }
