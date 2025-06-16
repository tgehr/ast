// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.consteval;

import ast.lexer: Location, Tok, TokenType;
import ast.expression;
import ast.type;

import util;
import util.maybe;

private Expression make(ℤ v){
	return LiteralExp.makeInteger(v);
}

private Expression make(int v){
	return make(ℤ(v));
}

private Expression make(TokenType subop)(Location loc, Expression sub1) {
	import ast.semantic_: minusType;

	assert(isNumericTy(sub1.type));
	Expression subty;
	static if(subop == Tok!"-") {
		subty = minusType(sub1.type);
	} else {
		static assert(0);
	}
	assert(subty);
	assert(isNumericTy(subty));
	auto r = new UnaryExp!subop(sub1);
	r.loc = loc;
	r.type = subty;
	r.setSemCompleted();
	return r.eval();
}

private Expression make(TokenType subop)(Location loc, Expression sub1, Expression sub2) {
	import ast.semantic_: arithmeticType, subtractionType, nSubType, cmpType;

	assert(isNumericTy(sub1.type));
	assert(isNumericTy(sub2.type));
	Expression subty;
	static if(subop == Tok!"+") {
		subty = arithmeticType!false(sub1.type, sub2.type);
	} else static if(subop == Tok!"-") {
		subty = subtractionType(sub1.type, sub2.type);
	} else static if(subop == Tok!"sub") {
		subty = nSubType(sub1.type, sub2.type);
	} else static if(subop == Tok!"·") {
		subty = arithmeticType!true(sub1.type, sub2.type);
	} else static if(subop == Tok!"=" || subop == Tok!"≠") {
		subty = cmpType(sub1.type, sub2.type);
	} else {
		static assert(0);
	}
	assert(subty);
	assert(isNumericTy(subty));
	auto r = new BinaryExp!subop(sub1, sub2);
	r.loc = loc;
	r.type = subty;
	r.setSemCompleted();
	return r.eval();
}

Expression evalNumericBinop(TokenType op: Tok!"+")(Location loc, Expression ne1, Maybe!ℤ v1, Expression ne2, Maybe!ℤ v2) {
	if(v1 && v2) return make(v1.get() + v2.get());
	if(v1 && v1.get() == 0) return ne2;
	if(v2 && v2.get() == 0) return ne1;
	if(v1 && !v2) return make!(Tok!"+")(loc, ne2, ne1);
	if(v2 && v2.get() < 0) {
		return make!(Tok!"-")(loc, ne1, make(-v2.get()));
	}
	static foreach(sub1;[Tok!"-",Tok!"sub"]){
		if(auto se1 = cast(BinaryExp!sub1)ne1){
			static foreach(sub2;[Tok!"-",Tok!"sub"]){
				if(auto se2 = cast(BinaryExp!sub2)ne2){
					auto nb0 = make!(Tok!"+")(loc, se1.e1, se2.e2);
					auto nb1 = make!sub1(loc, nb0, se1.e2);
					auto nb2 = make!sub2(loc, nb1, se2.e2);
					return nb2;
				}
			}
			auto v12 = se1.e2.asIntegerConstant();
			if(v12 && v2) {
				return make!sub1(loc, se1.e1, make(v12.get() - v2.get()));
			}
			if(se1.e2 == ne2) return se1.e1;
		}
	}
	if(v2) {
		if(auto ae1 = cast(BinaryExp!(Tok!"+"))ne1){
			auto v12 = ae1.e2.asIntegerConstant();
			if(v12) {
				return make!op(loc, ae1.e1, make(v12.get() + v2.get()));
			}
		}
	}
	if(auto ae2 = cast(BinaryExp!(Tok!"+"))ne2){
		return make!(Tok!"+")(loc, make!(Tok!"+")(loc, ne1, ae2.e1), ae2.e2);
	}
	if(ne1.isDeterministic()) {
		if(ne1 == ne2){
			return make!(Tok!"·")(loc, make(2), ne2);
		}
		static foreach(sub2;[Tok!"-",Tok!"sub"]){
			if(auto se2 = cast(BinaryExp!sub2)ne2){
				if(se2.e2 == ne1) return se2.e1;
			}
		}
	}
	return evalNumericSum!op(loc, ne1, ne2);
}

Expression evalNumericBinop(TokenType op)(Location loc, Expression ne1, Maybe!ℤ v1, Expression ne2, Maybe!ℤ v2) if(op == Tok!"-" || op == Tok!"sub") {
	if(v1 && v2) return make(v1.get() - v2.get());
	if(ne1 == ne2) return make(0);
	if(v2 && v2.get() == 0) return ne1;
	if(v1 && v1.get() == 0) return make!(Tok!"-")(loc, ne2);
	// if(auto se2 = cast(UnaryExp!(Tok!"-")) ne2) {
	// 	return make!(Tok!"+")(loc, ne1, se2.e);
	// }
	if(ne2.isDeterministic()) {
		if(auto ae1 = cast(BinaryExp!(Tok!"+"))ne1){
			if(ae1.e1 == ne2) return ae1.e2;
			if(ae1.e2 == ne2) return ae1.e1;
			if(auto ae2 = cast(BinaryExp!(Tok!"+"))ne2){
				if(ae1.e1 == ae2.e1)
					return make!op(loc, ae1.e2, ae2.e2);
			}
		}
		static foreach(sub;[Tok!"-",Tok!"sub"]){
			if(auto se1 = cast(BinaryExp!sub)ne1){
				if(se1.e1 == ne2) return make!(Tok!"-")(loc, se1.e2);
				// TODO: if(se1.e2 == -ne2)
			}
		}
	}
	if(ne1.isDeterministic()) {
		if(auto ae2 = cast(BinaryExp!(Tok!"+"))ne2){
			if(ae2.e1 == ne1) return make!(Tok!"-")(loc, ae2.e2);
			if(ae2.e2 == ne1) return make!(Tok!"-")(loc, ae2.e1);
		}
		static foreach(sub;[Tok!"-",Tok!"sub"]){
			if(auto se2 = cast(BinaryExp!sub)ne2){
				if(se2.e1 == ne1) return se2.e2.eval();
				// TODO: if(se2.e2==-ne1
			}
		}
	}
	static foreach(sub2;[Tok!"-",Tok!"sub"]){
		if(auto se2 = cast(BinaryExp!sub2)ne2){
			return make!(Tok!"-")(loc, make!(Tok!"+")(loc, ne1, se2.e2), se2.e1);
		}
	}
	return evalNumericSum!op(loc, ne1, ne2);
}

Expression evalNumericBinop(TokenType op: Tok!"·")(Location loc, Expression ne1, Maybe!ℤ v1, Expression ne2, Maybe!ℤ v2) {
	if(v1 && v2) return make(v1.get() * v2.get());
	if(v1 && v1.get() == 0) return ne1;
	if(v2 && v2.get() == 0) return ne2;
	if(v1 && v1.get() == 1) return ne2;
	if(v2 && v2.get() == 1) return ne1;
	if(cast(LiteralExp)ne2 && !cast(LiteralExp)ne1) {
		return make!op(loc, ne2, ne1);
	}
	return null;
}

Expression evalNumericBinop(TokenType op: Tok!"^")(Location loc, Expression ne1, Maybe!ℤ v1, Expression ne2, Maybe!ℤ v2) {
	if(v2 && v2.get() == 0) return make(1);
	if(v2 && v2.get() == 1) return ne1;
	if(v1 && v1.get() == 1) return make(1);
	if(v1 && v2 && v2.get() >= 0) {
		return make(pow(v1.get(), v2.get()));
	}
	return null;
}

Expression evalNumericSum(TokenType op)(Location loc, Expression ne1, Expression ne2) if(op == Tok!"+" || op == Tok!"-" || op == Tok!"sub") {
	if(auto me1=cast(BinaryExp!(Tok!"·"))ne1){
		if(auto le1=cast(LiteralExp)me1.e1){
			if(me1.e2==ne2){
				auto a = make!op(loc, le1, make(1));
				return make!(Tok!"·")(loc, a, me1.e2);
			}
			if(auto me2=cast(BinaryExp!(Tok!"·"))ne2){
				if(auto le2=cast(LiteralExp)me2.e1){
					if(me1.e2==me2.e2){
						auto a = make!op(loc, le1, le2);
						return make!(Tok!"·")(loc, a, me1.e2);
					}
				}
			}
		}
	}
	if(auto me2=cast(BinaryExp!(Tok!"·"))ne2){
		if(auto le2=cast(LiteralExp)me2.e1){
			if(me2.e2==ne1){
				auto a = make!op(loc, make(1), le2);
				return make!(Tok!"·")(loc, a, ne1);
			}
		}
	}
	return null;
}

Expression evalNumericBinop(TokenType op)(Location loc, Expression ne1, Maybe!ℤ v1, Expression ne2, Maybe!ℤ v2) if(op == Tok!"=" || op == Tok!"≠") {
	if(v1 && v2) {
		return make((v1.get() == v2.get()) ^ (op != Tok!"="));
	}
	if(ne1.isDeterministic() && ne1 == ne2) {
		return make(op == Tok!"=");
	}
	if(cast(LiteralExp)ne1 && !cast(LiteralExp)ne2) {
		return make!op(loc, ne2, ne1);
	}
	if(!v2) {
		import ast.semantic_: subtractionType;
		if(subtractionType(ne1.type, ne2.type)) {
			return make!op(loc, make!(Tok!"-")(loc, ne1, ne2), make(0));
		}
	}
	return null;
}
