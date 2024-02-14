// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.conversion;
import ast.expression,ast.type;
import ast.declaration:Variance;

import std.conv, std.range, std.algorithm;

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
	this(Expression from,Expression to)in{
		auto wf=whichNumeric(from);
		auto wt=whichNumeric(to);
		assert(wf&&wt&&wt<wf);
	}do{
		super(from,to);
	}
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
	this(ArrayTy from,VectorTy to)in{
		assert(isNoOpConversion(from.next,to.next));
	}do{
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

class IntToVectorConversion: Conversion{
	this(CallExp from,VectorTy to,bool checkLength)in{
		assert(isInt(from));
		assert(isNoOpConversion(Bool(from.isClassical()),to.next));
	}do{
		super(from,to);
	}
}

class UintToVectorConversion: Conversion{
	this(CallExp from,VectorTy to,bool checkLength)in{
		assert(isUint(from));
		assert(isNoOpConversion(Bool(from.isClassical()),to.next));
	}do{
		super(from,to);
	}
}

class VectorToIntConversion: Conversion{
	this(VectorTy from,CallExp to,bool checkLength)in{
		assert(isNoOpConversion(Bool(to.isClassical()),from.next));
		assert(isInt(to));
	}do{
		super(from,to);
	}
}

class VectorToUintConversion: Conversion{
	this(VectorTy from,CallExp to,bool checkLength)in{
		assert(isNoOpConversion(Bool(to.isClassical()),from.next));
		assert(isUint(to));
	}do{
		super(from,to);
	}
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
