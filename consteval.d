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

	if(isEmpty(sub1.type)) return sub1; // (the operand diverges, e.g., `x coerce ⊥`)
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

	if(isEmpty(sub1.type)) return sub1; // (an operand diverges, e.g., `x coerce ⊥`)
	if(isEmpty(sub2.type)) return sub2;
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
		subty = cmpType!true(sub1.type, sub2.type);
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

private bool isNumericSum(Expression e){
	if(cast(BinaryExp!(Tok!"+"))e) return true;
	if(cast(BinaryExp!(Tok!"-"))e) return true;
	if(cast(BinaryExp!(Tok!"sub"))e) return true;
	return false;
}

private void collectSummands(Expression e, ref Expression[] summands){
	if(auto ae = cast(BinaryExp!(Tok!"+"))e){
		collectSummands(ae.e1, summands);
		collectSummands(ae.e2, summands);
	}else summands ~= e;
}

private Expression negatedSummand(Location loc, Expression s){
	if(auto u = cast(UnaryExp!(Tok!"-"))s) return u.e;
	if(auto v = s.asIntegerConstant()) if(v.get() < 0) return make(-v.get());
	return null;
}

private bool nonNeg(Expression e){ return isSubtype(e.type, ℕt(false)); }

private bool soundCommonFactor(TokenType op)(Expression factor){
	static if(op == Tok!"sub") return nonNeg(factor);
	else return true;
}

private bool factorInnerOK(TokenType op)(Expression inner){
	if(isNumericSum(inner)) return false;
	static if(op == Tok!"sub"){
		if(cast(UnaryExp!(Tok!"-"))inner) return false;
		if(auto v = inner.asIntegerConstant()) if(v.get() < 0) return false;
	}
	return true;
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
					auto nb0 = make!(Tok!"+")(loc, se1.e1, se2.e1);
					auto nb1 = make!sub1(loc, nb0, se1.e2);
					auto nb2 = make!sub2(loc, nb1, se2.e2);
					return nb2;
				}
			}
			auto v12 = se1.e2.asIntegerConstant();
			if(v12 && v2) {
				return make!sub1(loc, se1.e1, make(v12.get() - v2.get()));
			}
			if(ne2.isDeterministic() && se1.e2 == ne2) return se1.e1;
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
	if(v1 && v2){
		static if(op == Tok!"-") return make(v1.get() - v2.get());
		else if(v1.get() >= v2.get()) return make(v1.get() - v2.get());
	}
	if(ne1.isDeterministic() && ne1 == ne2) return make(0);
	if(v2){
		if(v2.get() == 0){
			static if(op == Tok!"-") return ne1;
			else if(nonNeg(ne1)) return ne1;
		}
		static if(op == Tok!"-")
		if(v2.get() < 0){
			return make!(Tok!"+")(loc, ne1, make(-v2.get()));
		}
	}
	static if(op == Tok!"-")
	if(v1 && v1.get() == 0) return make!(Tok!"-")(loc, ne2);
	static if(op == Tok!"-")
	if(auto se2 = cast(UnaryExp!(Tok!"-")) ne2) {
		return make!(Tok!"+")(loc, ne1, se2.e);
	}
	if(ne2.isDeterministic()) {
		if(auto ae1 = cast(BinaryExp!(Tok!"+"))ne1){
			if(ae1.e1 == ne2) return ae1.e2;
			if(ae1.e2 == ne2) return ae1.e1;
			auto v12 = ae1.e2.asIntegerConstant();
			if(v12 && v2 && !(op == Tok!"sub" && v2.get() == 0 && v12.get() > 0)){ // (not `(a + 1) sub 0` into `a sub -1`, which becomes `(a + 1) sub 0` again below)
				return make!op(loc, ae1.e1, make(v2.get() - v12.get()));
			}
			if(auto ae2 = cast(BinaryExp!(Tok!"+"))ne2){
				if(ae1.e1 == ae2.e1)
					return make!op(loc, ae1.e2, ae2.e2);
			}
		}
		static foreach(sub;[Tok!"-",Tok!"sub"]){
			if(auto se1 = cast(BinaryExp!sub)ne1){
				if(se1.e1 == ne2){
					auto mY = make!(Tok!"-")(loc, se1.e2);
					static if(op == Tok!"-" && sub == Tok!"-") return mY;
					else static if(op == Tok!"sub" && sub == Tok!"-"){ if(nonNeg(mY)) return mY; }
					else { if(nonNeg(ne2) && nonNeg(mY)) return mY; }
				}
			}
		}
	}
	if(ne1.isDeterministic()) {
		if(auto ae2 = cast(BinaryExp!(Tok!"+"))ne2){
			static if(op == Tok!"-"){
				if(ae2.e1 == ne1) return make!(Tok!"-")(loc, ae2.e2);
				if(ae2.e2 == ne1) return make!(Tok!"-")(loc, ae2.e1);
			}else{
				if(ae2.e1 == ne1) return make!(Tok!"sub")(loc, make(0), ae2.e2);
				if(ae2.e2 == ne1) return make!(Tok!"sub")(loc, make(0), ae2.e1);
			}
		}
		static foreach(sub;[Tok!"-",Tok!"sub"]){
			if(auto se2 = cast(BinaryExp!sub)ne2){
				if(se2.e1 == ne1){
					auto Y = se2.e2;
					auto mY = make!(Tok!"-")(loc, Y);
					static if(op == Tok!"-" && sub == Tok!"-") return Y.eval();
					else static if(op == Tok!"sub" && sub == Tok!"-"){ if(nonNeg(Y)) return Y.eval(); }
					else static if(op == Tok!"-" && sub == Tok!"sub"){ if(nonNeg(ne1) && nonNeg(mY)) return Y.eval(); }
					else { if(nonNeg(ne1) && nonNeg(mY) && nonNeg(Y)) return Y.eval(); }
				}
			}
		}
	}
	static foreach(sub1;[Tok!"-",Tok!"sub"]){
		if(auto se1 = cast(BinaryExp!sub1)ne1){
			if(auto ae = cast(BinaryExp!(Tok!"+"))se1.e1){
				if(ne2.isDeterministic()){
					bool ok = true; // TODO: assumes se1.e1 >= se1.e2 for sub1==Tok!"sub"
					// static if(sub1==Tok!"sub") ok = nonNeg(make!(Tok!"-")(loc, se1.e1, se1.e2));
					if(ok){
						if(ae.e1 == ne2) return make!op(loc, ae.e2, se1.e2);
						if(ae.e2 == ne2) return make!op(loc, ae.e1, se1.e2);
					}
				}
			}
		}
	}
	static foreach(sub2;[Tok!"-",Tok!"sub"]){
		if(auto se2 = cast(BinaryExp!sub2)ne2){
			bool ok = true; // TODO: assumes `se2.e1 >= se2.e2` for sub2==Tok!"sub"
			// static if(sub2==Tok!"sub") ok = nonNeg(make!(Tok!"-")(loc, se2.e1, se2.e2));
			if(ok) return make!op(loc, make!(Tok!"+")(loc, ne1, se2.e2), se2.e1);
		}
	}
	Expression[] ls, rs;
	collectSummands(ne1, ls);
	collectSummands(ne2, rs);
	bool moved = false;
	static if(op == Tok!"sub"){
		Expression[] L, R;
		foreach(s; ls){ if(auto neg = negatedSummand(loc, s)){ R ~= neg; moved = true; } else L ~= s; }
		foreach(s; rs){ if(auto neg = negatedSummand(loc, s)){ L ~= neg; moved = true; } else R ~= s; }
		ls = L; rs = R;
	}
	bool any = false;
	auto usedR = new bool[rs.length];
	auto keepL = new bool[ls.length];
	foreach(i, l; ls){
		keepL[i] = true;
		if(!l.isDeterministic()) continue;
		foreach(j, r; rs){
			if(!usedR[j] && l == r){
				usedR[j] = true; keepL[i] = false; any = true; break;
			}
		}
	}
	if(moved || any){
		Expression lhs = null, rhs = null;
		foreach(i, l; ls) if(keepL[i]) lhs = lhs ? make!(Tok!"+")(loc, lhs, l) : l;
		foreach(j, r; rs) if(!usedR[j]) rhs = rhs ? make!(Tok!"+")(loc, rhs, r) : r;
		return make!op(loc, lhs ? lhs : make(0), rhs ? rhs : make(0));
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
	if(v1){
		static foreach(sop;[Tok!"+",Tok!"-",Tok!"sub"]){
			if(auto se2 = cast(BinaryExp!sop)ne2){
				if(auto v = se2.e2.asIntegerConstant()){
					return make!sop(loc,
					                make!(Tok!"·")(loc, ne1, se2.e1),
					                make(v1.get() * v.get()));
				}
			}
		}
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
			if(ne2.isDeterministic() && me1.e2==ne2){
				auto a = make!op(loc, le1, make(1));
				return make!(Tok!"·")(loc, a, me1.e2);
			}
			if(auto me2=cast(BinaryExp!(Tok!"·"))ne2){
				if(auto le2=cast(LiteralExp)me2.e1){
					if(me1.e2.isDeterministic() && me1.e2==me2.e2){
						auto a = make!op(loc, le1, le2);
						return make!(Tok!"·")(loc, a, me1.e2);
					}
				}
			}
		}
	}
	if(auto me2=cast(BinaryExp!(Tok!"·"))ne2){
		if(auto le2=cast(LiteralExp)me2.e1){
			if(ne1.isDeterministic() && me2.e2==ne1){
				auto a = make!op(loc, make(1), le2);
				return make!(Tok!"·")(loc, a, ne1);
			}
		}
	}
	if(auto me1=cast(BinaryExp!(Tok!"·"))ne1){
		if(auto me2=cast(BinaryExp!(Tok!"·"))ne2){
			static foreach(i;0..2){
				static foreach(j;0..2){{
					auto f1 = i ? me1.e1 : me1.e2;
					auto r1 = i ? me1.e2 : me1.e1;
					auto f2 = j ? me2.e1 : me2.e2;
					auto r2 = j ? me2.e2 : me2.e1;
					if(!cast(LiteralExp)f1 && f1.isDeterministic() && f1==f2 && soundCommonFactor!op(f1)){
						auto inner = make!op(loc, r1, r2);
						if(factorInnerOK!op(inner))
							return make!(Tok!"·")(loc, f1, inner);
					}
				}}
			}
		}
	}
	if(auto me1=cast(BinaryExp!(Tok!"·"))ne1){
		if(ne2.isDeterministic()){
			static foreach(i;0..2){{
				auto f1 = i ? me1.e1 : me1.e2;
				auto r1 = i ? me1.e2 : me1.e1;
				if(!cast(LiteralExp)f1 && f1==ne2 && soundCommonFactor!op(f1)){
					auto inner = make!op(loc, r1, make(1));
					if(factorInnerOK!op(inner))
						return make!(Tok!"·")(loc, inner, f1);
				}
			}}
		}
	}
	if(auto me2=cast(BinaryExp!(Tok!"·"))ne2){
		if(ne1.isDeterministic()){
			static foreach(j;0..2){{
				auto f2 = j ? me2.e1 : me2.e2;
				auto r2 = j ? me2.e2 : me2.e1;
				if(!cast(LiteralExp)f2 && f2==ne1 && soundCommonFactor!op(f2)){
					auto inner = make!op(loc, make(1), r2);
					if(factorInnerOK!op(inner))
						return make!(Tok!"·")(loc, inner, f2);
				}
			}}
		}
	}
	return null;
}

Expression evalNumericBinop(TokenType op)(Location loc, Expression ne1, Maybe!ℤ v1, Expression ne2, Maybe!ℤ v2) if(op == Tok!"<" || op == Tok!"≤" || op == Tok!">" || op == Tok!"≥") {
	if(v1 && v2) {
		static if(op == Tok!"<") return make(v1.get() < v2.get());
		else static if(op == Tok!"≤") return make(v1.get() <= v2.get());
		else static if(op == Tok!">") return make(v1.get() > v2.get());
		else return make(v1.get() >= v2.get());
	}
	if(ne1.isDeterministic() && ne1 == ne2) {
		return make(op == Tok!"≤" || op == Tok!"≥");
	}
	return null;
}

Expression evalNumericBinop(TokenType op)(Location loc, Expression ne1, Maybe!ℤ v1, Expression ne2, Maybe!ℤ v2) if(op == Tok!"div" || op == Tok!"%" || op == Tok!"&" || op == Tok!"|" || op == Tok!"⊕") {
	if(!v1 || !v2) return null;
	static if(op == Tok!"div" || op == Tok!"%") if(v2.get() == 0) return null; // (division by zero fails at run time)
	static if(op == Tok!"div") return make(floordiv(v1.get(), v2.get()));
	else static if(op == Tok!"%") return make(floormod(v1.get(), v2.get()));
	else static if(op == Tok!"&") return make(v1.get() & v2.get());
	else static if(op == Tok!"|") return make(v1.get() | v2.get());
	else return make(v1.get() ^ v2.get());
}

Expression evalNumericBinop(TokenType op)(Location loc, Expression ne1, Maybe!ℤ v1, Expression ne2, Maybe!ℤ v2) if(op == Tok!"∧" || op == Tok!"∨" || op == Tok!"⊻" || op == Tok!"&&" || op == Tok!"||") {
	static if(op == Tok!"&&" || op == Tok!"||") {
		if(v1) { // (the right operand is only evaluated if needed)
			static if(op == Tok!"&&") return v1.get() != 0 ? ne2 : make(0);
			else return v1.get() != 0 ? make(1) : ne2;
		}
		return null;
	} else {
		if(!v1 || !v2) return null;
		bool b1 = v1.get() != 0, b2 = v2.get() != 0;
		static if(op == Tok!"∧") return make(b1 && b2);
		else static if(op == Tok!"∨") return make(b1 || b2);
		else return make(b1 != b2);
	}
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

// the exact value of a classical constant of a numeric type whose operations the evaluation computes exactly (`𝔹`, `ℕ`, `ℤ` and `ℚ`, but not `ℝ`, which it approximates with floating point), for the evaluation of built-in functions (see `exactBuiltinCall`); it follows the expression as its evaluation at run time does, not its result of `eval`, which omits conversions to `ℝ` (e.g., in `floor((2^53+1):!ℝ)`), apart from the values of top-level constants, which the evaluation at run time also takes from `eval`
Maybe!ℚ exactValue(Expression e){
	static bool isExactTy(Expression t){
		if(!t||isEmpty(t)||!t.isClassical()) return false;
		auto nt=isNumericTy(t);
		return nt==NumericType.Bool||nt==NumericType.ℕt||nt==NumericType.ℤt||nt==NumericType.ℚt;
	}
	if(!e||!e.isSemCompleted()||!isExactTy(e.type)) return none!ℚ;
	if(auto v=e.asRationalConstant()){
		if(v.get[3]>4096||v.get[3]< -4096) return none!ℚ;
		auto r=ℚ(v.get[0],v.get[1]);
		if(v.get[3]!=0) r=r*pow(ℚ(ℤ(v.get[2])),ℤ(v.get[3]));
		return just(r);
	}
	if(auto id=cast(Identifier)e){
		auto init=id.getInitializer();
		return init&&init !is e?exactValue(init):none!ℚ;
	}
	if(auto fe=cast(FieldExp)e){ // (e.g., the length of a vector)
		auto v=fe.eval();
		return v !is fe?exactValue(v):none!ℚ;
	}
	if(auto idx=cast(IndexExp)e){
		auto c=constantComponent(idx);
		return c?exactValue(c):none!ℚ;
	}
	if(auto ue=cast(UnaryExp!(Tok!"-"))e){
		if(auto v=exactValue(ue.e)) return just(-v.get);
		return none!ℚ;
	}
	static foreach(op;["+","-","·","/","div","%","^"]){
		if(auto be=cast(BinaryExp!(Tok!op))e){
			auto v1=exactValue(be.e1),v2=exactValue(be.e2);
			if(!v1||!v2) return none!ℚ;
			auto a=v1.get,b=v2.get;
			static if(op=="+") return just(a+b);
			else static if(op=="-") return just(a-b);
			else static if(op=="·") return just(a*b);
			else static if(op=="/"||op=="div"||op=="%"){
				if(b==0) return none!ℚ;
				static if(op=="/") return just(a/b);
				else{
					auto q=a/b,f=ℚ(floordiv(q.num,q.den));
					static if(op=="div") return just(f);
					else return just(a-f*b);
				}
			}else{
				if(b.den!=1||a==0&&b.num<0||(a.num.ulongLength+a.den.ulongLength)*abs(b.num)>1024) return none!ℚ; // (at most about 2^16 bits)
				return just(pow(a,b.num));
			}
		}
	}
	if(auto tae=cast(TypeAnnotationExp)e){ // (a conversion that does not change the value)
		auto v=exactValue(tae.e);
		if(!v) return none!ℚ;
		switch(isNumericTy(e.type)){
			case NumericType.Bool: return v.get==0||v.get==1?v:none!ℚ;
			case NumericType.ℕt: return v.get.den==1&&v.get>=0?v:none!ℚ;
			case NumericType.ℤt: return v.get.den==1?v:none!ℚ;
			default: return v;
		}
	}
	if(auto ce=cast(CallExp)e) if(auto v=exactBuiltinCall(ce)) return just(ℚ(v.get));
	return none!ℚ;
}
private Expression constantComponent(IndexExp idx){ // (the component that a constant index selects from a tuple or vector literal, or from the value of a top-level constant)
	auto agg=idx.e;
	if(auto id=cast(Identifier)agg) agg=id.getInitializer();
	else if(auto inner=cast(IndexExp)agg) agg=constantComponent(inner);
	if(!agg) return null;
	Expression[] es;
	if(auto tpl=cast(TupleExp)agg) es=tpl.e;
	else if(auto vec=cast(VectorExp)agg) es=vec.e;
	else return null;
	auto i=idx.a.isSemCompleted()?idx.a.asIntegerConstant(true):none!ℤ;
	if(!i||i.get<0||i.get>=es.length) return null;
	return es[cast(size_t)i.get];
}
private string builtinName(Expression callee){ // (of a built-in function of the prelude that `exactBuiltinCall` evaluates)
	import ast.declaration: FunctionDef;
	import ast.semantic_: isPrimitive;
	import ast.modules: isInPrelude;
	auto id=cast(Identifier)callee;
	if(!id) return null;
	auto fd=cast(FunctionDef)id.meaning;
	if(!fd||!fd.name||!isInPrelude(fd)) return null;
	switch(isPrimitive(fd)){
		case "real.floor": return "floor";
		case "real.ceil": return "ceil";
		case "real.log2": return "log2";
		case "real.log10": return "log10";
		case "real.sqrt": return "sqrt";
		case "real.cbrt": return "cbrt";
		case "real.exp2": return "exp2";
		case "int.gcd": return "gcd";
		default: break;
	}
	if(fd.getName=="log₂") return "log2";
	if(fd.getName=="round") return "round";
	return null;
}
private ℤ floorLog(ℚ v,ℤ base)in{ assert(v>0&&base>1); }do{ // (the largest `k` with `base^k ≤ v`)
	ℤ k=0;
	if(v>=1){
		for(auto p=ℚ(base);p<=v;p=p*ℚ(base)) k+=1;
	}else{
		k=-1;
		for(auto p=ℚ(1)/ℚ(base);p>v;p=p/ℚ(base)) k-=1;
	}
	return k;
}
private ℤ iroot(ℤ n,int d)in{ assert(n>=0&&(d==2||d==3)); }do{ // (the largest `k` with `k^d ≤ n`)
	if(n<2) return n;
	ℤ lo=0,hi=1;
	while(pow(hi,ℤ(d))<=n) hi*=2;
	while(hi-lo>1){
		auto mid=(lo+hi)/2;
		if(pow(mid,ℤ(d))<=n) lo=mid;
		else hi=mid;
	}
	return lo;
}
private bool floatExact(alias f)(ℚ x,ℚ r){ // (the evaluation of `f(x)` in floating point computes exactly `r`, with either precision, see `QState.Value.realFunction`)
	import std.math: isFinite;
	import std.meta: AliasSeq;
	static foreach(T;AliasSeq!(double,real)){{
		static if(is(T==double)) T a=toDouble(x);
		else T a=toReal(x);
		T v=f(a);
		if(!isFinite(v)||toℚ(v)!=r) return false;
	}}
	return true;
}
private Maybe!ℚ realArgument(Expression arg){ // (the exact value of the argument of a function with a real result, within the range of floating point, which the function converts it to also without an annotation)
	if(auto tae=cast(TypeAnnotationExp)arg) if(isNumericTy(tae.type)==NumericType.ℝ) arg=tae.e;
	auto v=exactValue(arg);
	if(!v) return none!ℚ;
	auto bound=pow(ℤ(2),ℤ(1000));
	if(abs(v.get.num)>bound||v.get.den>bound) return none!ℚ;
	return v;
}
private Maybe!ℤ roundedValue(Expression arg,bool up){ // (`floor(arg)` or `ceil(arg)` where its evaluation computes it exactly; for a function with a real result, where floating point resolves it: a rational result must be computed exactly, an irrational one must not be within a relative distance of 2^-40 of an integer)
	import util.math: log2,log10,sqrt,cbrt,exp2;
	auto ce=cast(CallExp)arg;
	auto name=ce&&!ce.isSquare?builtinName(ce.e):null;
	if(!util.among(name,"log2","log10","sqrt","cbrt","exp2")){
		auto v=exactValue(arg);
		if(!v) return none!ℤ;
		return just(up?ceildiv(v.get.num,v.get.den):floordiv(v.get.num,v.get.den));
	}
	auto xv=realArgument(ce.arg);
	if(!xv) return none!ℤ;
	auto x=xv.get;
	static ℚ eta(ℤ k){ return ℚ(abs(k)+1,pow(ℤ(2),ℤ(40))); } // (the distance from an integer that floating point resolves for a result of magnitude below |k|+1)
	Maybe!ℚ exact; // (the result, if it is rational)
	ℤ k; // (otherwise, its floor)
	switch(name){
		case "log2","log10":{
			if(x<=0) return none!ℤ;
			auto base=ℤ(name=="log2"?2:10);
			k=floorLog(x,base);
			auto p=pow(ℚ(base),k);
			if(x==p){
				if(name=="log2"?!floatExact!log2(x,ℚ(k)):!floatExact!log10(x,ℚ(k))) return none!ℤ;
				exact=just(ℚ(k));
			}else{
				auto μ=ℚ(4)*eta(k);
				if(x<p*(ℚ(1)+μ)||x>p*ℚ(base)*(ℚ(1)-μ)) return none!ℤ;
			}
			break;
		}
		case "sqrt","cbrt":{
			auto d=name=="sqrt"?2:3;
			if(x<0&&d==2) return none!ℤ;
			auto w=x<0?-x:x;
			auto rn=iroot(w.num,d),rd=iroot(w.den,d);
			if(pow(rn,ℤ(d))==w.num&&pow(rd,ℤ(d))==w.den){
				auto r=ℚ(x<0?-rn:rn,rd);
				if(d==2?!floatExact!sqrt(x,r):!floatExact!cbrt(x,r)) return none!ℤ;
				exact=just(r);
			}else{
				auto m=iroot(floordiv(w.num,w.den),d);
				auto η=eta(m);
				if(w<pow(ℚ(m)+η,ℤ(d))||w>pow(ℚ(m+1)-η,ℤ(d))) return none!ℤ;
				k=x<0?-m-1:m;
			}
			break;
		}
		case "exp2":{
			if(x.den!=1||abs(x.num)>1000) return none!ℤ;
			auto r=pow(ℚ(2),x.num);
			if(!floatExact!exp2(x,r)) return none!ℤ;
			exact=just(r);
			break;
		}
		default: assert(0);
	}
	if(exact) return just(up?ceildiv(exact.get.num,exact.get.den):floordiv(exact.get.num,exact.get.den));
	return just(up?k+1:k);
}
Maybe!ℤ exactBuiltinCall(CallExp ce){ // (the integer result of a call of a built-in function where its evaluation computes it exactly, e.g., `floor(1.5)`, `ceil(log₂(5))` or `gcd(12,18)`; functions with real results are only evaluated in the argument of `floor` and `ceil`, see `roundedValue`)
	if(ce.isSquare||!ce.arg) return none!ℤ;
	switch(builtinName(ce.e)){
		case "floor": return roundedValue(ce.arg,false);
		case "ceil": return roundedValue(ce.arg,true);
		case "round":{
			auto v=exactValue(ce.arg);
			if(!v) return none!ℤ;
			auto w=v.get+ℚ(1,2);
			return just(floordiv(w.num,w.den));
		}
		case "gcd":{
			auto tpl=cast(TupleExp)ce.arg;
			if(!tpl||tpl.e.length!=2) return none!ℤ;
			auto a=exactValue(tpl.e[0]),b=exactValue(tpl.e[1]);
			if(!a||!b||a.get.den!=1||b.get.den!=1) return none!ℤ;
			return just(gcd(a.get.num,b.get.num));
		}
		default: return none!ℤ;
	}
}
