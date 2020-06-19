module ast.ad;

import ast.scope_, ast.declaration, ast.expression, ast.type, ast.lexer, ast.semantic_;

import std.stdio, std.conv, std.format, std.algorithm.iteration, std.range, std.array;
import std.typecons : Tuple;
import std.algorithm.mutation;

import ast.transformations;

private Parameter[] paramsFromType(ProductTy productTy) {
    Expression[] paramTypes;
    if (productTy.isTuple) {
        auto tt = cast(TupleTy)productTy.dom;
        assert(!!tt);
        paramTypes = tt.types;
    } else {
        paramTypes = [productTy.dom];
    }

    return zip(productTy.isConst, productTy.names, paramTypes)
        .map!((Tuple!(bool, string, Expression) p){
            return new Parameter(p[0], new Identifier(p[1]), p[2]);
        }).array;
}

Manifold getManifoldOf(Expression t, Scope sc, string context) {
    if (auto ty = cast(Type)t) {
        return ty.manifold(sc);
    }

    sc.error(format("%s type %s is not differentiable (no manifold capabilities)", context, t.toString), t.loc);
    return null;
}

// prepends the given type 'first' to a ProductTy domain as given by 'dom'
private Expression prependingToDomain(Expression first, Expression dom) {
    if (TupleTy tup = cast(TupleTy)dom) {
        return tupleTy([first] ~ tup.types);
    }
    if (VectorTy vec = cast(VectorTy)dom) {
        if (LiteralExp vecSize = cast(LiteralExp)vec.num) {
            auto intVal = to!int(vecSize.lit.str);
            if(intVal > 0 && vecSize.lit.type==Tok!"0") {
                return tupleTy([first] ~ repeat(vec.next, intVal).array);
            }
        }
    }
    return tupleTy([first, dom]);
}

ProductTy pullbackTy(FunctionDef primal, Manifold manifoldDom, Manifold manifoldCod) {
    auto pullbackParamNames = ["v"] ~ primal.params.map!(p => p.name.name).array;
	auto pullbackParamTypes = prependingToDomain(manifoldDom.tangentVecTy, primal.ftype.dom);
	auto pullbackReturnType = manifoldCod.tangentVecTy;
	auto isConst = [true] ~ primal.ftype.isConst;

	return productTy(isConst, pullbackParamNames, pullbackParamTypes, pullbackReturnType, 
		false, true, Annotation.none, true);
}

FunctionDef generatePullback(FunctionDef fd, Scope sc) {
    Parameter[] params = fd.params;
	Expression rret = fd.rret;
	CompoundExp body_ = fd.body_;

    // skip errorneous functions
    if (fd.sstate==SemState.error) {
        return null;
    }

    // skip built-in functions
    if (body_ is null) {
        return null;
    }

    // temporary: skip functions of dependent type
    if (fd.isSquare) {
        //writeln(format("Skipping pullback generation for dependent function: %s", fd.toString));
        return null;
    }

    // skip manifold member operations
    if (fd.isManifoldOp) {
        //writeln(format("Skipping pullback generation for manifold member: %s", fd.name.toString));
        return null;
    }

    // skip dat constructors
    if (fd.isConstructor) {
        //writeln(format("Skipping pullback generation for constructor: %s", fd.name.toString));
        return null;
    }

    if (!fd.isDifferentiable) {
        return null;
    }

    // check ftype
    ProductTy ftype = fd.ftype;
    Expression dom = ftype.dom;
    Expression cod = ftype.cod;

    // cannot generate pullback for functions w/o arguments or w/o return types 
    if (dom==unit||cod==unit) {
        return  null;
    }

    writeln(format("Generating pullback for function %s", fd.name.toString));

    fd = cast(FunctionDef)new ReplaceBuiltInOpsWithCallExpTransformation().transform(fd.copy());
    writeln("CEF of primal function ", fd); // CallExp Form

    // AD disabled for now
    return null;

    auto manifoldDom = getManifoldOf(dom, sc, "parameter");
    auto manifoldCod = getManifoldOf(cod, sc, "return");
    
    // skip non-differentiable functions (via nondiff function annotation)
    if (!manifoldDom||!manifoldCod) {
        return null;
    }

    ProductTy pty = pullbackTy(fd, manifoldDom, manifoldCod);
    Parameter[] pbParams = paramsFromType(pty);

    FunctionDef pullback = new FunctionDef(pullbackDefName(fd.name), pbParams, 
        pbParams.length > 0, null, null);
    pullback.ftype = pty;
    pullback.isPullback = true;
    pullback.body_ = pullbackBody(fd, pullback, sc);
    
    if (!pullback.body_) {
        return null;
    }

    // insert into scope
    sc.insert(pullback, true);
    // establish linking with primal
    fd.adjoint = pullback;
    pullback.primal = fd;
    pullback.primalName = fd.name;

    // perform semantic processing
    pullback = functionDefSemantic(pullback, sc);

    return pullback;
}

Identifier reference(Declaration decl) {
    auto ident = new Identifier(decl.name.name);
    ident.meaning = decl;
    return ident;
}

class PullbackState {
    /// names of the variables that store the tangent vectors per intermediate expression
    string[Expression] symbolTable;
    bool[string] symbols;
    /// mapping between primal and adjoint declarations
    Declaration[Declaration] declarations;
    /// pullback statements
    Expression[] stmts;

    Scope sc;

    this(Scope sc) {
        this.sc = sc;
    }
    
    /// removes current grad for expr from state
    void forget(Expression expr) {
        // TODO
    }

    /// adds a statement to the pullback, adding 'grad' to the 
    /// accumulated gradient of 'expr'
    Identifier add(Expression expr, Expression grad) {
        // TODO
        return new Identifier("_");
    }

    Expression tangent(Expression expr) {
        if (expr in symbolTable) {
            return new Identifier(symbolTable[expr]);
        } else if (auto varDecl = cast(VarDecl)expr) {
            auto ty = cast(Type)varDecl.vtype;
            assert(!!ty, "pullback variable type must be a Type instance");
            auto manifold = ty.manifold(sc);
            assert(!!manifold, "pullback variable type must have manifold capabilities");
            return manifold.tangentZeroExp;
        } else {
            auto ty = cast(Type)expr.type;
            assert(!!ty, "pullback expression type must be a Type instance");
            auto manifold = ty.manifold(sc);
            assert(!!manifold, "pullback expression type must have manifold capabilities");
            return manifold.tangentZeroExp;
        }
    }

    /// combines two tangent vectors (i.e. adding them)
    private Expression combine(Expression e1, Expression e2) {
        return apply!(Tok!"+")(e1, e2);
    }
}

CompoundExp pullbackBody(FunctionDef primal, FunctionDef pullback, Scope sc) {
    auto body_ = primal.body_;
    if (!body_) return null;

    PullbackState state = new PullbackState(sc);
    foreach(d_primal, d_adjoint; zip(primal.params, pullback.params[1..$])) {
        state.declarations[d_primal] = d_adjoint;
    }
    pullbackStmt(body_, reference(pullback.params[0]), state);

    // construct pullback return stmt
    auto paramTangents = primal.params.map!(p => state.tangent(p)).array;
    auto ret = new ReturnExp(paramTangents.length > 1 ? new TupleExp(paramTangents) : paramTangents[0]);
    return new CompoundExp(state.stmts ~ [cast(Expression)ret]);
}

void pullbackStmt(Expression stmt, Expression targetTangentVector, PullbackState state) {
    if (auto compExp = cast(CompoundExp)stmt) {
        // === CompoundExp
        // traverse block in reverse order
        Expression[] stmts = new Expression[](compExp.s.length);
        compExp.s.copy(stmts);
        reverse(stmts);
        foreach(s; stmts) {
            pullbackStmt(s, targetTangentVector, state);
        }
    } else if (auto retExp = cast(ReturnExp)stmt) {
        // === ReturnExp
        pullbackExp(retExp.e, targetTangentVector, state);
    } else if (auto singleDef = cast(SingleDefExp)stmt) {
        // === SingleDefExp
        auto lhsTangent = state.tangent(singleDef.decl);
        auto rhs = singleDef.initializer.e2;
        pullbackExp(rhs, lhsTangent, state);
    } else if (auto binExp = cast(ABinaryExp)stmt) {
        // === BinaryExp
        switch (binExp.opRep) {
            case "=": {
                // op=="="
                auto ident = cast(Identifier)binExp.e1;
                if (!ident) {
                    state.sc.error("automatic differentiation only supports identifiers on the left-hand side of an assignment.", binExp.e1.loc);
                    return;
                }
                auto lhsTangent = state.tangent(ident.meaning);
                auto rhs = binExp.e2;
                pullbackExp(rhs, lhsTangent, state);
                // TODO: reconsider this with IteExp
                state.forget(ident.meaning);
                return;
            }
            default:
                state.sc.error(format("Unhandled binary expression %s is not differentiable.", stmt.toString), stmt.loc);
                // nothing to do (side-effect free binary expression on top-level)
        }
    } else {
        state.sc.error(format("The statement %s is not differentiable.", stmt.toString), stmt.loc);
    }
    
    /*
    handleBinaryExp(ABinaryExp binExp)
    handleCallExp(CallExp callExp)
    handleAssertExp(AssertExp assertExp)
    handleIteExp(IteExp iteExp)
    handleParamDefExp(ParamDefExp paramExp)
    handleForExp(ForExp forExp)
    */
}

BinaryExp!op apply(TokenType op)(Expression e1, Expression e2) {
    return new BinaryExp!op(e1, e2);
}

/// rewires the provided copy of an primal expression to an equivalent 
/// expression in the pullback
T rewire(T)(T primalExp, PullbackState state) {
    T expr = primalExp.copy();
    if (auto binExp = cast(ABinaryExp)expr) {
        binExp.e1 = rewire(binExp.e1, state);
        binExp.e2 = rewire(binExp.e2, state);
        return cast(T)binExp;
    } else if (auto ident = cast(Identifier)expr) {
        Identifier originalIdent = cast(Identifier)primalExp;
        if (originalIdent.meaning !in state.declarations) {
            writeln(originalIdent);
            writeln(originalIdent.meaning);
            writeln(state.declarations);
            assert(false);
            state.sc.error(format("generated pullback references primal declaration %s, which is not yet mapped to a pullback equivalent.", 
                expr.toString), expr.loc);
            return expr;
        }
        ident.meaning = state.declarations[originalIdent.meaning];
        return ident;
    } else {
        state.sc.error(format("generated pullback requires reusing primal expression %s, which is currently not supported", 
            expr.toString), expr.loc);
        return expr;
    }
}   

void pullbackExp(Expression exp, Expression tangentVectorExp, PullbackState state) {
    if (auto binExp = cast(ABinaryExp)exp) {
        switch (binExp.opRep) {
            case "·":
                auto t1 = apply!(Tok!"·")(rewire(binExp.e2, state), tangentVectorExp);
                auto t2 = apply!(Tok!"·")(tangentVectorExp, rewire(binExp.e1, state));
                pullbackExp(binExp.e1, t1, state);
                pullbackExp(binExp.e2, t2, state);
                return;
            case "+":
                pullbackExp(binExp.e1, tangentVectorExp, state);
                pullbackExp(binExp.e2, tangentVectorExp, state);
                return;
            case "-":
                auto t1 = apply!(Tok!"·")(LiteralExp.makeInteger(-1), tangentVectorExp);
                pullbackExp(binExp.e1, tangentVectorExp, state);
                pullbackExp(binExp.e2, t1, state);
                return;
                // ":=", "←", "+←", "-←", "=", "≠"
            default:
                // ">", "<", "×"
                state.sc.error(format("The binary operator %s is not differentiable.", binExp.opRep), exp.loc);
                return;
        }
    }
    if (auto identExp = cast(Identifier)exp) {
        auto meaning = identExp.meaning;
        assert(!!meaning);
        state.add(meaning, tangentVectorExp);
        return;
    }

    state.sc.error(format("The expression %s is not differentiable.", exp.toString), exp.loc);

    /*
    override void handleUnaryExp(AUnaryExp unaryExp)
        "-"
    override void handleTupleExp(TupleExp tupleExp)
    override void handleLiteralExp(LiteralExp lit)
    */
    /*
    override void handleCallExp(CallExp exp)
    override void handleArrayExp(ArrayExp arrayExp)
    override void handleFieldExp(FieldExp fieldExp)
    override void handleIndexExp(IndexExp exp)
    
    override void handleLambdaExp(LambdaExp lambdaExp)
    
    override void handleInitExp(InitExp exp)
    override void handleManifoldMemberExp(UnresolvedManifoldMemberExp exp)
    override void handleManifoldMoveExp(ManifoldMoveExp exp)
    override void handleParameterSetHandleExp(ParameterSetHandleExp exp)
    override void handleParameter(Parameter param)
    override void handleTypeAnnotationExp(TypeAnnotationExp typeAnno)
    override void handleType(Type t)
    */
}