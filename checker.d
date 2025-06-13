module ast.checker;
static if(imported!"astopt".language==imported!"astopt".silq):

import std.array: Appender, appender, array;
import std.format: format;
import std.algorithm: map, all, any;
import std.range: repeat;

import util.io: stderr;

import ast_sem = ast.semantic_;
import ast_low = ast.lowerings;
import ast_exp = ast.expression;
import ast_ty = ast.type;
import ast_decl = ast.declaration;
import ast_scope = ast.scope_;
import ast_conv = ast.conversion;
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
	AssignOp(binopCat ~ binopAssign, binopCat, false),
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

enum StmtResult {
	Diverges = 0, // abort or infinite loop
	MayPass = 1,
	MayReturn = 2,
	PassOrReturn = 3,
}

class Checker {
	this(ast_scope.NestedScope nscope, Checker parent = null) {
		this.nscope = nscope;
		this.parent = parent;
	}

	void visExpr(ast_exp.Expression e) {
		assert(e.isSemCompleted());
		assert(e.type && ast_ty.isType(e.type), format("expression type not a type: << %s >> of type %s", e, e.type));
		visType(e.type);
		ast_exp.dispatchExp!((auto ref e){
			this.implExpr(e);
		})(e);
	}

	void visType(ast_exp.Expression e) {
		assert(ast_ty.isType(e) || ast_ty.isQNumeric(e), format("expected type: %s", e));
		visExprOnce(e);
	}

	void visExprOnce(ast_exp.Expression e) {
		auto p = cast(void*)e;
		if(p in checked) return;
		checked[p] = unit;
		for(auto sc = parent; sc; sc = sc.parent) {
			if(p in sc.checked) return;
		}
		visExpr(e);
	}

	ast_exp.Expression visLoweringExpr(E)(E from) {
		auto constResult = from.constLookup?ast_sem.ConstResult.yes:ast_sem.ConstResult.no;
		auto to = ast_low.getLowering(from, ast_sem.ExpSemContext(nscope, constResult, ast_sem.InType.no));
		assert(!!to, format("TODO: lowering for %s (%s): << %s >>", E.stringof, typeid(from).name, from));
		visExpr(to);
		// imported!"util.io".writeln("lowered ", from, " → ", to, " ", from.type, " ", to.type);
		assert(to.type && from.type == to.type);
		return to;
	}

	// Check statement, return true iff it definitely returns
	StmtResult visStmt(ast_exp.Expression e) {
		if(auto et = cast(ast_exp.BinaryExp!(Tok!":=")) e) return implStmt(et);
		static foreach(op; assignOps) {
			if(auto et = cast(ast_exp.BinaryExp!(Tok!(op.aop))) e) {
				return implStmt(et);
			}
		}
		return ast_exp.dispatchStm!((auto ref e)=>this.implStmt(e))(e);
	}

	ast_exp.Expression lowerStmt(E)(E from) {
		auto constResult = from.constLookup?ast_sem.ConstResult.yes:ast_sem.ConstResult.no;
		auto to = ast_low.getLowering(from, nscope);
		if(!to) {
			// assert(!!cast(ast_exp.AssignExp)from, format("TODO: lowering for %s (%s): << %s >>", E.stringof, typeid(from).name, from)); // TODO
			return null;
		}
		// imported!"util.io".writeln("lowered ", from, " → ", to);
		assert(to.type && from.type == to.type);
		return to;
	}

	void visCompoundValue(ast_exp.CompoundExp e, string causeType, bool constLookup) {
		assert(e.blscope_ is nscope);
		assert(e.s.length > 0);
		foreach(stmt; e.s[0..$-1]) {
			StmtResult r = visStmt(stmt);
			assert(!(r & StmtResult.MayReturn), "early return in compound expression ("~causeType~")");
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

	StmtResult implStmt(ast_exp.CompoundExp e) {
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

		StmtResult r = sc.visCompoundStmt(e);

		if(r & StmtResult.MayPass) {
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

	StmtResult visCompoundStmt(ast_exp.CompoundExp e) {
		StmtResult r = StmtResult.MayPass;
		foreach(i, sube; e.s) {
			StmtResult sub = visStmt(sube);
			if(sub & StmtResult.MayReturn) r |= StmtResult.MayReturn;
			if(!(sub & StmtResult.MayPass)) return r & ~StmtResult.MayPass;
		}
		if(e.blscope_) {
			foreach(decl; e.blscope_.forgottenVars) {
				getVar(decl, false, "forgottenVars", e);
			}
		}
		return r;
	}

	StmtResult implStmt(ast_exp.FunctionDef e) {
		getFunc(e, e.capturedDecls, false, e);
		defineVar(e, "function definition", e);
		return StmtResult.MayPass;
	}

	StmtResult implStmt(ast_exp.CommaExp e) {
		if(visStmt(e.e1) & StmtResult.MayReturn) {
			assert(0, "return in lhs of CommaExp");
		}
		return visStmt(e.e2);
	}

	StmtResult implStmt(ast_exp.ReturnExp e) {
		expectMoved(e.e, "return value");
		visExpr(e.e);
		auto fd=nscope.getFunction();
		assert(!!fd && fd.ret);
		expectConvertible(e.e, fd.ret, ast_exp.TypeAnnotationType.annotation);
		// TODO: check that quantum-controlled ReturnExp does not return a classical value
		foreach(decl; e.forgottenVars) {
			getVar(decl, false, "forgottenVars", e);
		}
		checkEmpty();
		return StmtResult.MayReturn;
	}

	StmtResult implStmt(ast_exp.AssertExp e) {
		expectConst(e.e, "assert condition");
		visExpr(e.e);
		if(ast_sem.isFalse(e.e)) return StmtResult.Diverges;
		return StmtResult.MayPass;
	}

	StmtResult implStmt(ast_exp.IteExp e) {
		visExpr(e.cond);

		Checker ifTrue, ifFalse;
		visSplit(ifTrue, e.then.blscope_, ifFalse, e.othw.blscope_, e);
		visType(e.type);

		StmtResult retTrue = ifTrue.visCompoundStmt(e.then);
		StmtResult retFalse = ifFalse.visCompoundStmt(e.othw);

		if(!(retTrue & StmtResult.MayPass)) {
			assert(!ifTrue.nscope.mergedVars);
		}
		if(!(retFalse & StmtResult.MayPass)) {
			assert(!ifFalse.nscope.mergedVars);
		}
		if(!(retTrue & StmtResult.MayPass) && (retFalse & StmtResult.MayPass)) {
			visMerge(ifFalse, e);
		}
		if((retTrue & StmtResult.MayPass) && !(retFalse & StmtResult.MayPass)) {
			visMerge(ifTrue, e);
		}
		if((retTrue & StmtResult.MayPass) && (retFalse & StmtResult.MayPass)) {
			visMerge(ifTrue, ifFalse, e);
		}
		if(retTrue & StmtResult.MayPass) ifTrue.checkEmpty();
		if(retFalse & StmtResult.MayPass) ifFalse.checkEmpty();
		return retTrue | retFalse;
	}

	StmtResult implStmt(ast_exp.WithExp e) {
		Checker trans, bdy, itrans;

		if(e.trans.blscope_) {
			visSplit(trans, e.trans.blscope_, e);
		} else {
			trans = this;
		}
		auto retTrans = trans.visCompoundStmt(e.trans);
		assert(!(retTrans & StmtResult.MayReturn));
		if(!(retTrans & StmtResult.MayPass)) return retTrans;
		if(trans !is this) {
			visMerge(trans, e);
		}

		if(e.bdy.blscope_) {
			visSplit(bdy, e.bdy.blscope_, e);
		} else {
			bdy = this;
		}
		auto retBdy = bdy.visCompoundStmt(e.bdy);
		assert(!(retBdy & StmtResult.MayReturn));
		if(!(retBdy & StmtResult.MayPass)) return retBdy;
		if(bdy !is this) {
			visMerge(bdy, e);
		}

		if(e.isIndices) { // TODO
			auto oldDecl = e.aggregate(true);
			assert(!!oldDecl);
			getVar(oldDecl, false, "consumed aggregate for component replacement", e);
			auto newDecl = e.aggregate(false);
			defineVar(newDecl, "new aggregate for component replacement", e);
		}

		assert(!!e.itrans);
		if(e.itrans.blscope_) {
			visSplit(itrans, e.itrans.blscope_, e);
		} else {
			itrans = this;
		}
		auto retItrans = itrans.visCompoundStmt(e.itrans);
		assert(!(retItrans & StmtResult.MayReturn));
		if(itrans !is this) {
			visMerge(itrans, e);
		}

		return retItrans;
	}

	StmtResult implStmt(ast_exp.WhileExp e) {
		expectConst(e.cond, "while condition");
		auto retBdy = visLoop(e.bdy, null, e.cond);
		if(ast_sem.isTrue(e.cond)) return StmtResult.Diverges;
		return retBdy;
	}

	StmtResult implStmt(ast_exp.RepeatExp e) {
		expectConst(e.num, "repeat count");
		visExpr(e.num);
		auto retBdy = visLoop(e.bdy, null);
		if(!ast_sem.isPositive(e.num)) retBdy |= StmtResult.MayPass;
		return retBdy;
	}

	StmtResult implStmt(ast_exp.ForExp e) {
		expectConst(e.left, "for-left");
		visExpr(e.left);
		expectConst(e.right, "for-right");
		visExpr(e.right);
		if(e.step) {
			expectConst(e.step, "for-step");
			visExpr(e.step);
		}
		auto retBdy = visLoop(e.bdy, e.loopVar);
		return retBdy | StmtResult.MayPass;
	}

	StmtResult visLoop(ast_exp.CompoundExp bdy, ast_exp.Declaration loopVar, ast_exp.Expression condition = null) { // (result: loop body definitely returns)
		auto sc = bdy.blscope_;
		assert(sc.parent is nscope);

		ast_decl.Declaration[Id] merged;

		auto sub = new Checker(sc, this);
		if(loopVar) {
			sub.vars[loopVar.getId] = loopVar;
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

		if(condition) {
			sub.visExpr(condition); // TODO: treat `while cond { ... }` like `if cond { do { ... } until cond; }` instead.
		}

		StmtResult r = sub.visCompoundStmt(bdy);
		if(!(r & StmtResult.MayPass)) return r;

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

		if(condition) {
			visExpr(condition); // TODO: treat `while cond { ... }` like `if cond { do { ... } until cond; }` instead.
		}

		return r;
	}

	StmtResult implStmt(ast_exp.BinaryExp!(Tok!":=") e){
		auto lhs = e.e1;
		auto rhs = e.e2;
		if(auto idx = cast(ast_exp.IndexExp)rhs) {
			if(idx.byRef) {
				auto id = ast_sem.getIdFromIndex(idx);
				assert(id && id.meaning && id.meaning.scope_ is nscope);
			}
		}
		visExpr(rhs);
		visLhs(lhs);
		if(ast_ty.isEmpty(e.type)) return StmtResult.Diverges;
		return StmtResult.MayPass;
	}

	void visLhs(ast_exp.Expression e) {
		// expectMoved(e, "definition LHS");
		visType(e.type);
		return ast_exp.dispatchExp!((auto ref e) => this.implLhs(e))(e);
	}

	void implLhs(ast_exp.Identifier e) {
		assert(!e.constLookup);
		auto var = e.meaning;
		assert(cast(ast_decl.VarDecl) var, "LHS of assignment not VarDecl");
		assert(e.type == typeForDecl(var), format("LHS identifier type mismatch: [[ %s ]] on %s; type %s != decl type %s", e, e.loc, e.type, typeForDecl(var)));
		defineVar(var, "LHS", e);
	}

	void implLhs(ast_exp.TupleExp e) {
		foreach(ei; e.e) {
			visLhs(ei);
		}
	}

	void implLhs(ast_exp.CatExp e) {
		import ast.reverse: knownLength;
		auto l1=knownLength(e.e1,false);
		auto l2=knownLength(e.e2,false);
		assert(l1||l2);
		expectMoved(ast_sem.unwrap(e.e1), "concat LHS");
		expectMoved(ast_sem.unwrap(e.e2), "concat RHS");
		visLhs(ast_sem.unwrap(e.e1));
		visLhs(ast_sem.unwrap(e.e2));
	}

	void implLhs(ast_exp.CallExp e) {
		assert(!e.isSquare);
		assert(!e.isClassical_);
		visCall(e.e, e.arg, true);
	}

	void implLhs(ast_exp.IndexExp e) {
		visExpr(e.a);
		auto expectedType = ast_sem.indexType(e.e.type, e.a);
		assert(e.type == expectedType, format("index type mismatch: %s has type %s, indexed with %s results in %s instead of %s at %s", e.e, e.e.type, e.a, expectedType, e.type, e.loc));
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
		auto decl = sube.meaning;
		// assert(sube.type == typeForDecl(decl), format("LHS indexed identifier type mismatch: [[ %s ]] on %s; type %s != decl type %s", e, e.loc, sube.type, typeForDecl(decl))); // (can mismatch due to multiple updates)
		if(decl.getId !in vars || vars[decl.getId] is null) {
			defineVar(decl, "LHS", e);
		} else {
			getVar(decl, true, "LHS", e);
		}
	}

	void implLhs(ast_exp.Expression e) {
		assert(0, format("TODO: Unsupported LHS type %s: %s", typeid(e).name, e));
	}

	static foreach(op;assignOps)
	StmtResult implStmt(ast_exp.BinaryExp!(Tok!(op.aop)) e) {
		static immutable string binop = op.binop;
		static if(binop != binopCat) {
			if(auto ns = lowerStmt(e)) return visStmt(ns);
		}

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
		foreach(r; e.replacements) {
			assert(r.previous && r.new_);
			getVar(r.previous, false, "consumed variable for assignment", e);
			defineVar(r.new_, "new variable after assignment", e);
		}
		return StmtResult.MayPass;
	}

	StmtResult implStmt(ast_exp.Expression e) {
		expectConst(e, "expression statement");
		visExpr(e);
		if(ast_ty.isEmpty(e.type)) return StmtResult.Diverges;
		return StmtResult.MayPass;
	}

	void implExpr(ast_exp.Identifier e) {
		switch(ast_sem.isBuiltIn(e)) {
			case ast_sem.BuiltIn.none:
				break;
			default:
				return;
		}

		if(auto init=e.getInitializer()) {
			visExprOnce(init);
			return;
		}

		auto decl = e.meaning;
		if(!decl) return; // TODO
		// assert(e.type is decl.vtype, format("Different types: %s != %s", e.type, decl.vtype));
		return getVar(decl, e.constLookup||e.implicitDup, "identifier", e);
	}

	void implExpr(ast_exp.LambdaExp e) {
		getFunc(e.fd, e.fd.capturedDecls, e.constLookup, e);
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
		auto expectedType = ast_sem.indexType(e.e.type, e.a);
		assert(e.type == expectedType, format("index type mismatch: %s has type %s, indexed with %s results in %s instead of %s at %s", e.e, e.e.type, e.a, expectedType, e.type, e.loc));
	}

	void getFunc(ast_decl.FunctionDef fd, ast_decl.Declaration[] capturedDecls, bool isBorrow, ast_exp.Expression causeExpr) {
		assert(fd.sstate == ast_exp.SemState.completed);
		foreach(decl; capturedDecls) {
			auto ty = typeForDecl(decl);
			bool keep = isBorrow || !fd.isConsumedCapture(decl);
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
		visExpr(e.e);
		visExpr(e.t);
		visType(e.type);
		expectConvertible(e.e, e.type, e.annotationType);
	}

	void implExpr(ast_exp.FieldExp e) {
		assert(e.f.name == "length", format("TODO: field %s", e.f.name));
		visExpr(e.e);
	}

	void visSplit(ref Checker ifTrue, ast_scope.NestedScope scTrue, ref Checker ifFalse, ast_scope.NestedScope scFalse, ast_exp.Expression cause) {
		assert(scTrue.parent is nscope);
		assert(scFalse.parent is nscope);
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

		foreach(decl; scTrue.splitVars) {
			auto name = decl.splitFrom.getId;
			Triple* t = name in splitVars;
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
		assert(scTrue.parent is nscope);
		assert(scFalse.parent is nscope);

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

		foreach(decl; scTrue.mergedVars) {
			auto name = decl.mergedInto.getId;
			auto t = name in mergedVars;
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

		foreach(vNested; scNested.splitVars) {
			assert(vNested.scope_ is scNested);
			auto outer = vNested.splitFrom;
			auto name = outer.getId;
			assert(outer.scope_ is nscope);
			auto vtype = ast_sem.typeForDecl(outer);
			assert(typeForDecl(vNested) == vtype, format("ERROR: Split variable %s changed type in nested scope", name));
			getVar(outer, false, "splitVars", cause);
			nested.defineVar(vNested, "splitVars-nested", cause);
		}
	}

	void visMerge(Checker nested, ast_exp.Expression cause) {
		auto scNested = nested.nscope;

		foreach(vNested; scNested.mergedVars) {
			auto outer = vNested.mergedInto;
			// TODO types as part of merge result?
			visExpr(typeForDecl(outer));
			nested.getVar(vNested, false, "mergedVars-nested", cause);
			defineVar(outer, "mergedVars", cause);
		}

		// Make sure the merged types are evaluated in the outer scope.
		foreach(decl; scNested.mergedVars) {
			visExpr(typeForDecl(decl.mergedInto));
		}
	}

	void implExpr(ast_exp.IteExp e) {
		expectConst(e.cond, "if-condition");
		assert(ast_ty.isNumericTy(e.cond.type) == ast_ty.NumericType.Bool);
		visExpr(e.cond);

		if(e.then.blscope_ is null && e.othw.blscope_ is null) {
			visExpr(e.then.s[0]);
			visExpr(e.othw.s[0]);
			return;
		}

		Checker ifTrue, ifFalse;
		visSplit(ifTrue, e.then.blscope_, ifFalse, e.othw.blscope_, e);

		visType(e.type);
		ifTrue.visCompoundValue(e.then, "if-true", e.constLookup);
		ifFalse.visCompoundValue(e.othw, "if-false", e.constLookup);

		assert(ifTrue.nscope.mergedVars.length == 0);
		ifTrue.checkEmpty();

		assert(ifFalse.nscope.mergedVars.length == 0);
		ifFalse.checkEmpty();
	}

	void implExpr(ast_exp.AssertExp e) {
		expectConst(e.e, "assert condition");
		visExpr(e.e);
	}

	void implExpr(ast_exp.TupleExp e) {
		foreach(ei; e.e) {
			visExpr(ei);
		}
	}

	void implExpr(ast_exp.VectorExp e) {
		foreach(ei; e.e) {
			visExpr(ei);
		}
	}

	void implExpr(ast_exp.CallExp e) {
		assert(!e.isClassical_ || ast_ty.isType(e), format("TODO: isClassical_ call on non-type << %s >> on %s", e, e.loc));
		visCall(e.e, e.arg, false);
	}

	void implExpr(ast_exp.ClassicalTy e) {
		assert(ast_ty.isType(e));
		visExpr(e.inner);
	}

	void implExpr(ast_exp.TupleTy e) {
		assert(ast_ty.isTypeTy(e.type) || ast_ty.isQNumericTy(e.type));
		foreach(sub; e.types) {
			assert(ast_ty.isTypeTy(sub.type) || ast_ty.isQNumericTy(sub.type));
			visExpr(sub);
		}
	}

	void implExpr(ast_exp.VectorTy e) {
		assert(ast_ty.isTypeTy(e.type) || ast_ty.isQNumericTy(e.type));
		assert(ast_ty.isTypeTy(e.next.type) || ast_ty.isQNumericTy(e.next.type));
		visExpr(e.next);
		assert(ast_ty.isSubtype(e.num.type, ast_ty.ℕt()));
		visExpr(e.num);
	}

	void implExpr(ast_exp.ArrayTy e) {
		assert(ast_ty.isTypeTy(e.type) || ast_ty.isQNumericTy(e.type));
		assert(ast_ty.isTypeTy(e.next.type) || ast_ty.isQNumericTy(e.next.type));
		visExpr(e.next);
	}

	void implExpr(ast_ty.VariadicTy e) {
		visExpr(e.next);
	}

	void implExpr(ast_exp.TypeTy e) {}
	void implExpr(ast_exp.QNumericTy e) {}
	void implExpr(ast_exp.BottomTy e) {}
	void implExpr(ast_exp.NumericTy e) {}
	void implExpr(ast_exp.StringTy e) {}

	void implExpr(ast_ty.ProductTy e) {
		visType(e.dom);
		auto sc = new Checker(nscope, this);
		sc.strictScope = false;
		foreach(i, p; e.params) {
			if(p.name) sc.defineVar(p, "product type parameter", p.name);
		}
		sc.strictScope = true;
		sc.visType(e.cod);
	}

	void visCall(ast_exp.Expression targetExpr, ast_exp.Expression argExpr, bool isReversed) {
		if(auto targetId = cast(ast_exp.Identifier) targetExpr) {
			switch(ast_sem.isBuiltIn(targetId)) {
				case ast_sem.BuiltIn.none:
					break;
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
		// if(visLoweringExpr(e)) return;
		visExpr(e.e1);
		visExpr(e.e2);
	}

	static foreach(op;binops ~ cmpops ~ boolops)
	void implExpr(ast_exp.BinaryExp!(Tok!op) e) {
		expectConst(e.e1, "BinaryExp!\""~op~"\" LHS");
		expectConst(e.e2, "BinaryExp!\""~op~"\" RHS");
		import std.algorithm : canFind;
		static if(cmpops.canFind(op)) {
			if((ast_ty.isFixedIntTy(e.e1.type) || ast_ty.isNumericTy(e.e1.type))
			   && (ast_ty.isFixedIntTy(e.e2.type) || ast_ty.isNumericTy(e.e2.type)))
				if(visLoweringExpr(e)) return;
		}else if(visLoweringExpr(e)) return;
		visExpr(e.e1);
		if(boolops.canFind(op)){
			if(ast_sem.definitelyReturns(e.e2))
				return;
		}
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
		assert(!decl.splitInto.any!(d=>nscope.isNestedIn(d.scope_)), format("ERROR: variable access %s does not refer to maximally split version: %s on %s << %s >>", id, causeType, causeExpr.loc, causeExpr));

		if(fd && (!fd.scope_.getFunction() || nscope.isNestedIn(fd.fscope_))) {
			auto capturedDecls = fd.capturedDecls;
			if(auto lookup = cast(ast_exp.Identifier)causeExpr) {
				if(lookup.recaptures) {
					capturedDecls = lookup.recaptures;
				}
			}
			getFunc(fd, capturedDecls, isBorrow, causeExpr);
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
		auto conv = typeExplicitConversion!true(e.type, ty, annotationType);
		// check witness generation
		assert(conv, format("ERROR: Expected %s of type %s to be convertible to type %s", e, e.type, ty));
		visConv(conv);
	}

	void visConv(ast_conv.Conversion conv) {
		visType(conv.from);
		visType(conv.to);
		if(auto c = cast(ast_conv.TransitiveConversion)conv) {
			visConv(c.a);
			visConv(c.b);
		} else if(auto c = cast(ast_conv.TupleConversion)conv) {
			foreach(sub; c.elements) {
				visConv(sub);
			}
		} else if(auto c = cast(ast_conv.VectorConversion)conv) {
			visConv(c.next);
		} else if(auto c = cast(ast_conv.ArrayConversion)conv) {
			visConv(c.next);
		} else if(auto c = cast(ast_conv.FunctionConversion)conv) {
			visConv(c.dom);
			auto to = cast(ast_ty.ProductTy) c.to;
			auto sc = new Checker(nscope, this);
			sc.strictScope = false;
			foreach(p; to.params) {
				if(p.name && p.isConst) sc.defineVar(p, "product type parameter", p.name);
			}
			sc.strictScope = true;
			sc.visConv(c.cod);
		}
	}

	Checker parent;
	ast_scope.NestedScope nscope;
	IdMap!(ast_decl.Declaration) vars;
	bool strictScope = true;
	Unit[void*] checked;
}

void checkFunction(ast_decl.FunctionDef fd) {
	assert(fd.sstate == ast_exp.SemState.completed);
	auto sc = new Checker(fd.fscope_, null);

	sc.strictScope = false;
	foreach(decl; fd.capturedDecls) {
		sc.defineVar(decl, "capture", decl.name);
	}
	sc.strictScope = true;
	foreach(decl; fd.params) {
		sc.visExpr(decl.dtype);
		sc.visExpr(decl.vtype);
		sc.defineVar(decl, "param", decl.name);
	}
	if(fd.rret) sc.visExpr(fd.rret);
	sc.visExpr(fd.ret);
	if(fd.body_) {
		StmtResult r = sc.visStmt(fd.body_);
		assert(!(r & StmtResult.MayPass), format("ERROR: Function doesn't definitely return: << %s >>", fd));
	}
}
