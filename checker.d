module ast.checker;
static if(imported!"astopt".language==imported!"astopt".silq):

import std.array: Appender, appender, array;
import std.format: format;
import std.algorithm: map, all;
import std.range: repeat;

import util.io: stderr;

import ast_sem = ast.semantic_;
import ast_low = ast.lowerings;
import ast_exp = ast.expression;
import ast_ty = ast.type;
import ast_decl = ast.declaration;
import ast_scope = ast.scope_;
import ast.lexer: Tok;

alias typeForDecl = ast_sem.typeForDecl;
alias Unit = void[0];
enum unit = Unit.init;

alias Id = ast_exp.Id;
alias IdMap(T) = T[Id];
alias IdSet=IdMap!Unit;

ast_exp.Identifier[] uniqueIds(ast_exp.Identifier[] ids) {
	static if(false) {
		return ids;
	} else {
	auto r = appender!(ast_exp.Identifier[]);
	IdSet seen;
	foreach(id; ids) {
		if(id.id in seen) continue;
		seen[id.id] = unit;
		r.put(id);
	}
	return r[];}
}

struct AssignOp {
	string aop;
	string binop;
	bool inplace;

	this(string aop, string binop, bool inplace) scope nothrow {
		this.aop = aop;
		this.binop = binop;
		this.inplace = inplace;
	}
}

static immutable string unopMinus = "-";
static immutable string unopNot = "\u00ac";
static immutable string unopBitNot = "~";

static immutable string binopOr = "||";
static immutable string binopAnd = "&&";
static immutable string binopAdd = "+";
static immutable string binopSub = "-";
static immutable string binopNSub = "sub";
static immutable string binopMul = "\u00b7";
static immutable string binopDiv = "/";
static immutable string binopIDiv = "div";
static immutable string binopMod = "%";
static immutable string binopPow = "^";
static immutable string binopCat = "~";
static immutable string binopBitXor = "\u2295";
static immutable string binopBitOr = "\u2228";
static immutable string binopBitAnd = "\u2227";
static immutable string binopCmpEq = "=";
static immutable string binopCmpNe = "\u2260";
static immutable string binopCmpLt = "<";
static immutable string binopCmpLe = "\u2264";
static immutable string binopCmpGt = ">";
static immutable string binopCmpGe = "\u2265";
static immutable string binopAssign = "\u2190";

static immutable string[] binops = [
	binopAdd,
	binopSub,
	binopNSub,
	binopMul,
	binopDiv,
	binopIDiv,
	binopMod,
	binopPow,
	binopBitXor,
	binopBitOr,
	binopBitAnd,
];

static immutable string[] boolops = [
	binopOr,
	binopAnd,
];

static immutable string[] cmpops = [
	binopCmpEq,
	binopCmpNe,
	binopCmpLt,
	binopCmpLe,
	binopCmpGt,
	binopCmpGe,
];

static immutable string[] unops = [
	unopMinus,
	unopNot,
	unopBitNot,
];

static immutable AssignOp[] assignOps = [
	AssignOp(binopAssign, null, false),
	AssignOp(binopCat ~ binopAssign, binopAssign, false),
] ~ (binops ~ boolops).map!(op => AssignOp(op ~ binopAssign, op, op == binopAdd || op == binopSub || op == binopNSub || op == binopBitXor)).array;

bool isBinop(string op) pure {
	foreach(r; binops) {
		if(r == op) return true;
	}
	return false;
}

AssignOp getAssignOp(string op) pure {
	foreach(r; assignOps) {
		if(r.aop == op) return r;
	}
	assert(0);
}

class Checker {
	this(ast_scope.NestedScope nscope, Checker parent = null) {
		this.nscope = nscope;
		this.parent = parent;
	}

	void visExpr(ast_exp.Expression e) {
		if(cast(ast_ty.Type) e) {
			if(auto te = cast(ast_ty.VectorTy) e) {
				return this.implTy(te);
			}
			if(auto te = cast(ast_ty.ArrayTy) e) {
				return this.implTy(te);
			}
			if(auto te = cast(ast_ty.TupleTy) e) {
				return this.implTy(te);
			}
			if(auto te = cast(ast_ty.ProductTy) e) {
				return this.implTy(te);
			}
			if(auto te = cast(ast_ty.VariadicTy) e) {
				return this.implTy(te);
			}
			if(cast(ast_ty.TypeTy) e || cast(ast_ty.QTypeTy) e || cast(ast_ty.CTypeTy) e || cast(ast_ty.UTypeTy) e) {
				return;
			}
			if(cast(ast_ty.BoolTy) e || cast(ast_ty.ℕTy) e || cast(ast_ty.ℤTy) e || cast(ast_ty.ℚTy) e || cast(ast_ty.ℝTy) e || cast(ast_ty.ℂTy) e) {
				return;
			}
			assert(0, format("TODO: type %s: << %s >>", typeid(e).name, e));
		}
		ast_exp.dispatchExp!((auto ref e){
			this.implExpr(e);
		})(e);
	}

	ast_exp.Expression visLoweringExpr(E)(E from) {
		auto to = ast_low.getLowering(from, ast_sem.ExpSemContext(nscope, ast_sem.ConstResult.no, ast_sem.InType.no));
		assert(!!to, format("TODO: lowering for %s (%s): << %s >>", E.stringof, typeid(from).name, from));
		visExpr(to);
		// imported!"util.io".writeln("lowered: ", from, " -> ", to);
		assert(from.type.eval() == to.type.eval());
		return to;
	}

	// Check statement, return true iff it definitely returns
	bool visStmt(ast_exp.Expression e) {
		if(auto et = cast(ast_exp.BinaryExp!(Tok!":=")) e) return implStmt(et);
		static foreach(op; assignOps) {
			if(auto et = cast(ast_exp.BinaryExp!(Tok!(op.aop))) e) {
				return implStmt(et);
			}
		}
		return ast_exp.dispatchStm!((auto ref e)=>this.implStmt(e))(e);
	}

	void visCompoundValue(ast_exp.CompoundExp e, string causeType, bool constLookup) {
		assert(e.blscope_ is nscope);
		assert(e.s.length > 0);
		foreach(stmt; e.s[0..$-1]) {
			bool r = visStmt(stmt);
			assert(!cast(ast_exp.ReturnExp)stmt, "early return in compound expression ("~causeType~")"); // TODO: check is incomplete
		}
		assert(!cast(ast_exp.ReturnExp)e.s[$-1], "early return in compound expression ("~causeType~")"); // TODO: check is incomplete
		if(!ast_sem.definitelyReturns(e.s[$-1])){
			visExpr(e.s[$-1]);
			if(constLookup) {
				expectConst(e.s[$-1], causeType);
			} else {
				expectMoved(e.s[$-1], causeType);
			}
		}

		foreach(decl; e.blscope_.forgottenVars) {
			getVar(decl, false, "forgottenVars ("~causeType~")", e);
		}
	}

	void checkEmpty() {
		foreach(name, val; vars) {
			assert(!val, format("ERROR: Variable %s defined on %s not consumed", name.str, val.loc));
		}
	}

	bool implStmt(ast_exp.CompoundExp e) {
		if(!e.blscope_) {
			return visCompoundStmt(e);
		}

		auto sc = new Checker(e.blscope_, this);
		foreach(decl; sc.nscope.splitVars) {
			assert(decl.scope_ is sc.nscope);
			auto outer = decl.splitFrom;
			assert(outer.scope_ is nscope);
			assert(outer.splitInto == [decl]);
			getVar(outer, false, "splitVars", e);
			sc.defineVar(decl, "splitVars", e);
		}

		bool r = sc.visCompoundStmt(e);

		if(!r) {
			foreach(decl; sc.nscope.mergedVars) {
				assert(decl.scope_ is sc.nscope);
				auto outer = decl.mergedInto;
				assert(outer.scope_ is nscope);
				assert(outer.mergedFrom == [decl]);
				sc.getVar(decl, false, "mergedVars", e);
				defineVar(outer, "mergedVars", e);
			}
			sc.checkEmpty();
		}

		return r;
	}

	bool visCompoundStmt(ast_exp.CompoundExp e) {
		bool r = false;
		foreach(i, sube; e.s) {
			r |= visStmt(sube);
		}
		if(e.blscope_) {
			foreach(decl; e.blscope_.forgottenVars) {
				getVar(decl, false, "forgottenVars", e);
			}
		}
		return r;
	}

	bool implStmt(ast_exp.FunctionDef e) {
		getFunc(e, false, e);
		defineVar(e, "function definition", e);
		return false;
	}

	bool implStmt(ast_exp.CommaExp e) {
		if(visStmt(e.e1)) {
			assert(0, "return in lhs of CommaExp");
		}
		return visStmt(e.e2);
	}

	bool implStmt(ast_exp.ReturnExp e) {
		expectMoved(e.e, "return value");
		visExpr(e.e);
		foreach(decl; e.forgottenVars) {
			getVar(decl, false, "forgottenVars", e);
		}
		checkEmpty();
		return true;
	}

	bool implStmt(ast_exp.AssertExp e) {
		expectConst(e.e, "assert condition");
		visExpr(e.e);
		return ast_sem.isFalse(e.e);
	}

	bool implStmt(ast_exp.IteExp e) {
		visExpr(e.cond);

		Checker ifTrue, ifFalse;
		visSplit(ifTrue, e.then.blscope_, ifFalse, e.othw.blscope_, e);
		visExpr(e.type);

		bool retTrue = ifTrue.visCompoundStmt(e.then);
		bool retFalse = ifFalse.visCompoundStmt(e.othw);

		if(retTrue) {
			assert(!ifTrue.nscope.mergedVars);
		}
		if(retFalse) {
			assert(!ifFalse.nscope.mergedVars);
		}
		if(retTrue && !retFalse) {
			visMerge(ifFalse, e);
		}
		if(!retTrue && retFalse) {
			visMerge(ifTrue, e);
		}
		if(!retTrue && !retFalse) {
			visMerge(ifTrue, ifFalse, e);
		}
		if(!retTrue) ifTrue.checkEmpty();
		if(!retFalse) ifFalse.checkEmpty();
		return retTrue && retFalse;
	}

	bool implStmt(ast_exp.WithExp e) {
		Checker trans, bdy, itrans;

		visSplit(trans, e.trans.blscope_, e);
		auto retTrans = trans.visCompoundStmt(e.trans);
		assert(!retTrans);
		visMerge(trans, e);

		visSplit(bdy, e.bdy.blscope_, e);
		auto retBdy = bdy.visCompoundStmt(e.bdy);
		assert(!retBdy);
		visMerge(bdy, e);

		assert(!!e.itrans);
		visSplit(itrans, e.itrans.blscope_, e);
		auto retItrans = itrans.visCompoundStmt(e.bdy);
		assert(!retItrans);
		visMerge(itrans, e);

		return false;
	}

	bool implStmt(ast_exp.WhileExp e) {
		expectConst(e.cond, "while condition");
		visExpr(e.cond);
		visLoop(e.bdy, null);
		return ast_sem.isTrue(e.cond);
	}

	bool implStmt(ast_exp.RepeatExp e) {
		expectConst(e.num, "repeat count");
		visExpr(e.num);
		auto retBdy = visLoop(e.bdy, null);
		return retBdy && ast_sem.isPositive(e.num);
	}

	bool implStmt(ast_exp.ForExp e) {
		expectConst(e.left, "for-left");
		visExpr(e.left);
		expectConst(e.right, "for-right");
		visExpr(e.right);
		if(e.step) {
			expectConst(e.step, "for-step");
			visExpr(e.step);
		}
		visLoop(e.bdy, e.var);
		return false;
	}

	bool visLoop(ast_exp.CompoundExp bdy, ast_exp.Identifier loopVar) { // (result: loop body definitely returns)
		auto sc = bdy.blscope_;
		assert(sc.parent is nscope);

		ast_decl.Declaration[Id] merged;

		auto sub = new Checker(sc, this);
		if(loopVar) {
			ast_decl.Declaration decl = loopVar.meaning;
			if(!decl) {
				// TODO
				decl = new ast_decl.VarDecl(loopVar);
			}
			sub.vars[loopVar.id] = decl;
		}

		foreach(inner0; sc.splitVars) {
			auto id = inner0.getId;
			auto outer0 = inner0.splitFrom;
			assert(outer0.splitInto.length == 2);
			assert(outer0.splitInto[1] is inner0);
			auto outer1 = outer0.splitInto[0];
			assert(id !in merged, format("ERROR: Duplicate merged variable %s", id.str));
			merged[id] = outer0;
			getVar(outer0, false, "splitVars", bdy);
			sub.defineVar(inner0, "splitVars", bdy);
		}

		bool r = sub.visCompoundStmt(bdy);

		foreach(inner1; sc.mergedVars) {
			auto id = inner1.getId;
			auto outer0 = merged[id];
			auto outer1 = inner1.mergedInto;
			assert(outer1.mergedFrom.length == 2);
			// assert(outer1.mergedFrom[0] is outer0);
			assert(outer1.mergedFrom[0] is inner1);
			sub.getVar(inner1, false, "mergedVars", bdy);
			defineVar(outer1, "mergedVars", bdy);
		}
		assert(merged.length == sc.mergedVars.length);
		return r;
	}

	bool implStmt(ast_exp.BinaryExp!(Tok!":=") e){
		auto lhs = e.e1;
		auto rhs = e.e2;
		visExpr(rhs);
		visLhs(lhs);
		return false;
	}

	void visLhs(ast_exp.Expression e) {
		// expectMoved(e, "definition LHS");
		visExpr(e.type);
		return ast_exp.dispatchExp!((auto ref e) => this.implLhs(e))(e);
	}

	void implLhs(ast_exp.Identifier e) {
		assert(!e.constLookup);
		auto var = e.meaning;
		assert(cast(ast_decl.VarDecl) var, "LHS of assignment not VarDecl");
		defineVar(var, "LHS", e);
	}

	void implLhs(ast_exp.TupleExp e) {
		foreach(ei; e.e) {
			visLhs(ei);
		}
	}

	void implLhs(ast_exp.CallExp e) {
		assert(!e.isSquare);
		assert(!e.isClassical_);
		visCall(e.e, e.arg, true);
	}

	void implLhs(ast_exp.IndexExp e) {
		visExpr(e.a);
		while(true) {
			auto sube = cast(ast_exp.IndexExp) e.e;
			if(sube) {
				e = sube;
				continue;
			}
			break;
		}
		auto sube = cast(ast_exp.Identifier) e.e;
		assert(!!sube, format("TODO: LHS index expression [[ %s ]] on %s bottom not identifier", e, e.loc));
		getVar(sube.meaning, true, "LHS", e);
	}

	void implLhs(ast_exp.Expression e) {
		assert(0, format("TODO: Unsupported LHS type %s: %s", typeid(e).name, e));
	}

	static foreach(op;assignOps)
	bool implStmt(ast_exp.BinaryExp!(Tok!(op.aop)) e) {
		static immutable string binop = op.binop;

		visExpr(e.e2);

		auto lhs = cast(ast_exp.Identifier) e.e1;
		if(lhs) {
			auto decl = cast(ast_decl.VarDecl) lhs.meaning;
			assert(decl, "TODO: assignment LHS Identifier but not VarDecl");
			assert(lhs.type == decl.vtype, format("LHS type %s != decl type %s", lhs.type, decl.vtype));
			getVar(decl, false, "LHS", e);
			strictScope = false;
			defineVar(decl, "assignment LHS", e);
			strictScope = true;
		} else {
			visExpr(e.e1);
			strictScope = false;
			visLhs(e.e1);
			strictScope = true;
		}
		return false;
	}

	bool implStmt(ast_exp.Expression e) {
		expectConst(e, "expression statement");
		visExpr(e);
		return false;
	}

	void implTy(ast_ty.VectorTy e) {
		visExpr(e.next);
		visExpr(e.num);
	}

	void implTy(ast_ty.ArrayTy e) {
		visExpr(e.next);
	}

	void implTy(ast_ty.TupleTy e) {
		foreach(sube; e.types) {
			visExpr(sube);
		}
	}

	void implTy(ast_ty.ProductTy e) {
		visExpr(e.dom);
	}

	void implTy(ast_ty.VariadicTy e) {
		visExpr(e.next);
	}

	void implExpr(ast_exp.Identifier e) {
		switch(ast_sem.isBuiltIn(e)) {
			case ast_sem.BuiltIn.none:
				break;
			default:
				return;
		}

		if(auto init=e.getInitializer()) {
			visExpr(init);
			return;
		}

		auto decl = e.meaning;
		assert(decl);
		// assert(e.type is decl.vtype, format("Different types: %s != %s", e.type, decl.vtype));
		return getVar(decl, e.constLookup, "identifier", e);
	}

	void implExpr(ast_exp.LambdaExp e) {
		getFunc(e.fd, e.constLookup, e);
	}

	void implExpr(ast_exp.SliceExp e) {
		bool isLifted = e.constLookup;
		expectConst(e.l, "slice-left-index");
		expectConst(e.r, "slice-right-index");
		assert(e.e.constLookup, "TODO: non-lifted slicing");
		visExpr(e.e);
		visExpr(e.l);
		visExpr(e.r);
	}

	void implExpr(ast_exp.IndexExp e) {
		bool isLifted = e.constLookup;
		expectConst(e.a, "index");
		assert(e.e.constLookup, "TODO: non-lifted indexing");
		visExpr(e.e);
		visExpr(e.a);
	}

	void getFunc(ast_decl.FunctionDef fd, bool isBorrow, ast_exp.Expression causeExpr) {
		foreach(decl; fd.capturedDecls) {
			auto ty = typeForDecl(decl);
			bool keep = isBorrow || !ast_ty.hasQuantumComponent(ty) || imported!"astopt".allowUnsafeCaptureConst && decl.isConst();
			getVar(decl, keep, "capture", causeExpr);
		}
	}

	void implExpr(ast_exp.ForgetExp e) {
		expectMoved(e.var, "forgotten variable");
		if(e.val) {
			expectConst(e.val, "forget RHS");
			visExpr(e.val);
		}
		visExpr(e.var);
	}

	void implExpr(ast_exp.LiteralExp e) {
	}

	void implExpr(ast_exp.TypeAnnotationExp e) {
		visExpr(e.type);
		visExpr(e.e);
		expectConvertible(e.e, e.type, e.annotationType);
	}

	void implExpr(ast_exp.FieldExp e) {
		assert(e.f.name == "length", format("TODO: field %s", e.f.name));
		visExpr(e.e);
	}

	void visSplit(ref Checker ifTrue, ast_scope.NestedScope scTrue, ref Checker ifFalse, ast_scope.NestedScope scFalse, ast_exp.Expression cause) {
		assert(scTrue is nscope || scTrue.parent is nscope);
		assert(scFalse is nscope || scFalse.parent is nscope);
		ifTrue = new Checker(scTrue, this);
		ifFalse = new Checker(scFalse, this);

		struct Triple {
			ast_decl.Declaration outer, dTrue, dFalse;
		}
		IdMap!Triple splitVars;
		foreach(decl; scTrue.splitVars) {
			assert(decl.scope_ is scTrue);
			auto outer = decl.splitFrom;
			assert(outer.scope_ is nscope);
			splitVars[outer.getId] = Triple(outer, decl, null);
		}
		foreach(decl; scFalse.splitVars) {
			assert(decl.scope_ is scFalse);
			auto name = decl.splitFrom.getId;
			Triple* t = name in splitVars;
			assert(t, format("ERROR: Split variable %s missing in if-true", name.str));
			assert(decl.splitFrom is t.outer, format("ERROR: Split variable %s splitFrom scope mismatch", name.str));
			t.dFalse = decl;
		}

		foreach(name, t; splitVars) {
			assert(t.dFalse, format("ERROR: Split variable %s missing in if-false", name));
			auto vTrue = t.dTrue;
			auto vFalse = t.dFalse;
			auto vtype = ast_sem.typeForDecl(t.outer);
			assert(typeForDecl(vTrue) == vtype, format("ERROR: Split variable %s changed type in if-true", name));
			assert(typeForDecl(vFalse) == vtype, format("ERROR: Split variable %s changed type in if-false", name));
			getVar(t.outer, false, "splitVars", cause);
			ifTrue.defineVar(vTrue, "splitVars-if-true", cause);
			ifFalse.defineVar(vFalse, "splitVars-if-false", cause);
		}

		// Make sure the merged types are evaluated in the outer scope.
		foreach(decl; scTrue.mergedVars ~ scFalse.mergedVars) {
			visExpr(typeForDecl(decl.mergedInto));
		}
	}

	void visMerge(Checker ifTrue, Checker ifFalse, ast_exp.Expression cause) {
		auto scTrue = ifTrue.nscope;
		auto scFalse = ifFalse.nscope;

		struct Triple {
			ast_decl.Declaration outer, dTrue, dFalse;
		}
		IdMap!Triple mergedVars;
		foreach(decl; scTrue.mergedVars) {
			mergedVars[decl.mergedInto.getId] = Triple(decl.mergedInto, decl, null);
		}
		foreach(decl; scFalse.mergedVars) {
			auto name = decl.mergedInto.getId;
			auto t = name in mergedVars;
			assert(t, format("ERROR: Merged variable %s missing in if-true", name));
			assert(decl.mergedInto is t.outer, format("ERROR: Merged variable %s mergedInto mismatch", name));
			t.dFalse = decl;
		}

		foreach(name, t; mergedVars) {
			assert(t.dFalse, format("ERROR: Merged variable %s missing in if-false", name));
			auto outer = t.outer;
			// TODO types as part of merge result?
			visExpr(typeForDecl(outer));
			ifTrue.getVar(t.dTrue, false, "mergedVars-if-true", cause);
			ifFalse.getVar(t.dFalse, false, "mergedVars-if-false", cause);
			defineVar(outer, "mergedVars", cause);
		}
	}

	void visSplit(ref Checker nested, ast_scope.NestedScope scNested, ast_exp.Expression cause) {
		assert(scNested is nscope || scNested.parent is nscope);
		nested = new Checker(scNested, this);

		struct Pair {
			ast_decl.Declaration outer, nested;
		}
		IdMap!Pair splitVars;
		foreach(decl; scNested.splitVars) {
			assert(decl.scope_ is scNested);
			auto outer = decl.splitFrom;
			assert(outer.scope_ is nscope);
			splitVars[outer.getId] = Pair(outer, decl);
		}

		foreach(name, p; splitVars) {
			auto vNested = p.nested;
			auto vtype = ast_sem.typeForDecl(p.outer);
			assert(typeForDecl(vNested) == vtype, format("ERROR: Split variable %s changed type in nested scope", name));
			getVar(p.outer, false, "splitVars", cause);
			nested.defineVar(vNested, "splitVars-nested", cause);
		}

		// Make sure the merged types are evaluated in the outer scope.
		foreach(decl; scNested.mergedVars) {
			visExpr(typeForDecl(decl.mergedInto));
		}
	}

	void visMerge(Checker nested, ast_exp.Expression cause) {
		auto scNested = nested.nscope;

		struct Pair {
			ast_decl.Declaration outer, nested;
		}
		IdMap!Pair mergedVars;
		foreach(decl; scNested.mergedVars) {
			mergedVars[decl.mergedInto.getId] = Pair(decl.mergedInto, decl);
		}

		foreach(name, p; mergedVars) {
			auto outer = p.outer;
			// TODO types as part of merge result?
			visExpr(typeForDecl(outer));
			nested.getVar(p.nested, false, "mergedVars-nested", cause);
			defineVar(outer, "mergedVars", cause);
		}
	}

	void implExpr(ast_exp.IteExp e) {
		expectConst(e.cond, "if-condition");
		assert(cast(ast_ty.BoolTy) e.cond.type);
		visExpr(e.cond);

		if(e.then.blscope_ is null && e.othw.blscope_ is null) {
			visExpr(e.then.s[0]);
			visExpr(e.othw.s[0]);
			return;
		}

		Checker ifTrue, ifFalse;
		visSplit(ifTrue, e.then.blscope_, ifFalse, e.othw.blscope_, e);

		visExpr(e.type);
		ifTrue.visCompoundValue(e.then, "if-true", e.constLookup);
		ifFalse.visCompoundValue(e.othw, "if-false", e.constLookup);

		assert(ifTrue.nscope.mergedVars.length == 0);
		ifTrue.checkEmpty();

		assert(ifFalse.nscope.mergedVars.length == 0);
		ifFalse.checkEmpty();
	}

	void implExpr(ast_exp.TupleExp e) {
		foreach(ei; e.e) {
			visExpr(ei);
		}
	}

	void implExpr(ast_exp.ArrayExp e) {
		foreach(ei; e.e) {
			visExpr(ei);
		}
	}

	void implExpr(ast_exp.CallExp e) {
		if(ast_ty.isFixedIntTy(e)) {
			expectConst(e.arg, "int-bits");
			visExpr(e.arg);
			return;
		}
		assert(!e.isClassical_, format("TODO: isClassical_ call on non-type << %s >> on %s", e, e.loc));
		visCall(e.e, e.arg, false);
	}

	void visCall(ast_exp.Expression targetExpr, ast_exp.Expression argExpr, bool isReversed) {
		if(auto targetId = cast(ast_exp.Identifier) targetExpr) {
			switch(ast_sem.isBuiltIn(targetId)) {
				case ast_sem.BuiltIn.none:
					break;
				case ast_sem.BuiltIn.primitive:
				case ast_sem.BuiltIn.query:
					return;
				case ast_sem.BuiltIn.show:
					expectConst(argExpr, "__show argument");
					visExpr(argExpr);
					return;
				default:
					assert(0, format("TODO: call to built-in %s: << %s >>", targetExpr.loc, targetExpr));
			}
		}

		auto callTy = cast(ast_ty.ProductTy) targetExpr.type;
		assert(!!callTy, format("ERROR: call target not a ProductTy on %s: << %s >>", targetExpr.loc, targetExpr));

		if(!callTy.isClassical_) {
			expectMoved(targetExpr, "quantum call target");
			assert(!isReversed, format("ERROR: Reversed quantum call on %s: << %s >>", targetExpr.loc, targetExpr));
		}

		visExpr(targetExpr);

		bool isTuple;
		ast_exp.Expression[] paramTypes;
		ast_exp.Expression[] argVals;
		if(auto argTuple = cast(ast_exp.TupleExp) argExpr) {
			isTuple = true;
			argVals = argTuple.e;
			if(auto tdom = cast(ast_ty.TupleTy) callTy.dom) {
				paramTypes = tdom.types;
			} else if(auto vdom = cast(ast_ty.VectorTy) callTy.dom) {
				paramTypes = vdom.next.repeat(argVals.length).array;
			} else if(auto adom = cast(ast_ty.ArrayTy) callTy.dom) {
				paramTypes = adom.next.repeat(argVals.length).array;
			} else {
				isTuple = false;
			}
		}
		if(!isTuple) {
			argVals = [argExpr];
			paramTypes = [callTy.dom];
		}

		size_t n = paramTypes.length;
		assert(argVals.length == n);

		bool[] isConstForReverse = callTy.isConstForReverse().array;
		if(isTuple && !callTy.isTuple) {
			assert(isConstForReverse.length == 1);
			isConstForReverse = isConstForReverse[0].repeat(n).array;
		} else if(!isTuple && callTy.isTuple) {
			isConstForReverse = [isConstForReverse.all!(c => c)];
			// assert(isConstForReverse[0] || !isReversed, "TODO: reverse with all-const arguments");
		}
		assert(isConstForReverse.length == n);

		if(!isReversed) {
			foreach(i, arg; argVals) {
				auto pTy = paramTypes[i];
				if(!isConstForReverse[i]) {
					expectMoved(arg, "argument");
				} else if(ast_ty.hasQuantumComponent(pTy)) {
					expectConst(arg, "argument");
				}
				visExpr(arg);
				expectConvertible(arg, pTy, ast_exp.TypeAnnotationType.annotation);
			}
			return;
		}

		foreach(i, arg; argVals) {
			auto pTy = paramTypes[i];
			if(!isConstForReverse[i]) {
				// expectMoved(arg, "reversed argument");
				assert(!ast_ty.hasClassicalComponent(pTy), "reversed non-const classical parameter");
			} else if(ast_ty.hasQuantumComponent(pTy)) {
				// expectConst(arg, "non-reversed argument");
			}
			if(!isReversed) {
				visExpr(arg);
			}
		}
		foreach(i, arg; argVals) {
			if(!isConstForReverse[i]) {
				visLhs(arg);
			}
		}
	}

	void implExpr(ast_exp.BinaryExp!(Tok!binopCat) e) {
		if(e.constLookup) {
			expectConst(e.e1, "concat LHS");
			expectConst(e.e2, "concat RHS");
		} else {
			expectMoved(e.e1, "concat LHS");
			expectMoved(e.e2, "concat RHS");
		}
		//if(visLoweringExpr(e)) return; // TODO
		visExpr(e.e1);
		visExpr(e.e2);
	}

	static foreach(op;binops ~ cmpops ~ boolops)
	void implExpr(ast_exp.BinaryExp!(Tok!op) e) {
		expectConst(e.e1, "BinaryExp!\""~op~"\" LHS");
		expectConst(e.e2, "BinaryExp!\""~op~"\" RHS");
		import std.algorithm : canFind;
		static if(["+","-","sub"].canFind(op)) if(visLoweringExpr(e)) return;
		visExpr(e.e1);
		visExpr(e.e2);
	}

	static foreach(op;unops)
	void implExpr(ast_exp.UnaryExp!(Tok!op) e) {
		expectConst(e.e, "UnaryExp!\""~op~"\" argument");
		if(visLoweringExpr(e)) return;
		visExpr(e.e);
	}

	void implExpr(ast_exp.Expression e) {
		assert(0, typeid(e).name);
	}

	void defineVar(ast_decl.Declaration d, string causeType, ast_exp.Expression causeExpr) {
		auto id = d.getId;
		assert(!strictScope || d.scope_ is nscope, format("ERROR: Variable %s defined in wrong scope: %s on %s << %s >>", id.str, causeType, causeExpr.loc, causeExpr));
		auto p = id in vars;
		if(p && *p) {
			// Allow classical redefinition in assignment LHS
			assert(!strictScope && !ast_ty.hasQuantumComponent(typeForDecl(d)), format("ERROR: Variable %s already defined: %s on %s << %s >>", id.str, causeType, causeExpr.loc, causeExpr));
		}
		vars[id] = d;
	}

	void getVar(ast_decl.Declaration decl, bool isBorrow, string causeType, ast_exp.Expression causeExpr) {
		if(cast(ast_decl.DatDecl) decl) {
			// assert(isBorrow, "moved DatDecl");
			return;
		}

		auto id = decl.getId;
		auto fd = cast(ast_decl.FunctionDef) decl;
		auto vd = cast(ast_decl.VarDecl) decl;
		assert(fd || vd, format("TODO: Unsupported declaration type %s: %s on %s << %s >>", typeid(decl).name, causeType, causeExpr.loc, causeExpr));
		assert(!vd || isBorrow || !vd.isConst, format("ERROR: Consuming const variable %s: %s on %s << %s >>", id, causeType, causeExpr.loc, causeExpr));

		if(fd && (!fd.scope_.getFunction() || nscope.isNestedIn(fd.fscope_))) {
			getFunc(fd, isBorrow, causeExpr);
			return;
		}

		ast_decl.Declaration v;

		if(!isBorrow) {
			auto p = id in vars;
			assert(p, format("ERROR: Variable %s %s: %s on %s << %s >>", id.str, parent && id in parent.vars ? "not split from parent scope" : "undefined", causeType, causeExpr.loc, causeExpr));
			v = *p;
			*p = null;
		} else {
			auto cur = this;
			auto p = id in vars;
			while(!p) {
				cur = cur.parent;
				assert(cur, format("ERROR: Variable %s undefined: %s on %s << %s >>", id.str, causeType, causeExpr.loc, causeExpr));
				p = id in cur.vars;
			}
			v = *p;
		}
		assert(v, format("ERROR: Variable %s use-after-consume: %s on %s << %s >>", id.str, causeType, causeExpr.loc, causeExpr));
		// assert(v is decl, format("Declaration mismatch: expected to consume << %s >> on %s, got << %s >> on %s", decl, decl.loc, v, v.loc));
	}

	void expectConst(ast_exp.Expression e, string why) {
		if(e.constLookup) return;
		assert(0, format("ERROR: Expected const %s on %s: << %s >>", why, e.loc, e));
	}

	void expectMoved(ast_exp.Expression e, string why) {
		if(!e.constLookup) return;
		assert(0, format("ERROR: Expected moved %s on %s: << %s >>", why, e.loc, e));
	}

	void expectConvertible(ast_exp.Expression e, ast_exp.Expression ty, ast_ty.TypeAnnotationType annotationType) {
		import ast.conversion;
		if(typeExplicitConversion!true(e.type, ty, annotationType)) return; // check witness generation
		assert(0, format("ERROR: Expected %s of type %s to be convertible to type %s", e, e.type, ty));
	}

	Checker parent;
	ast_scope.NestedScope nscope;
	IdMap!(ast_decl.Declaration) vars;
	bool strictScope = true;
}

void checkFunction(ast_decl.FunctionDef fd) {
	auto sc = new Checker(fd.fscope_, null);

	sc.strictScope = false;
	foreach(decl; fd.capturedDecls) {
		sc.defineVar(decl, "capture", decl.name);
	}
	sc.strictScope = true;
	foreach(decl; fd.params) {
		sc.visExpr(decl.vtype);
		sc.defineVar(decl, "param", decl.name);
	}
	sc.visExpr(fd.ret);
	if(fd.body_) {
		bool r = sc.visStmt(fd.body_);
		assert(r, format("ERROR: Function doesn't definitely return: << %s >>", fd));
	}
}
