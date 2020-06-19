module ast.transformations;

import ast.visitor, ast.expression, ast.declaration, ast.type, ast.error, ast.lexer, ast.type, ast.visitor;
import std.format;

import std.algorithm.iteration;
import std.array, std.stdio;

class ReplaceBuiltInOpsWithCallExpTransformation: Transformation {
    override Expression handleUnsupportedExp(Expression expr) {
        transformChildren(expr);
        return expr;
    }

    override Expression handleNullValue() {
        return null;
    }

    override Expression handleUnaryExp(AUnaryExp unaryExp) {
        if (auto minExp = cast(UnaryExp!(Tok!"-"))unaryExp) {
            auto operand = transform(minExp.e);
            auto binExp = new BinaryExp!(Tok!"·")(LiteralExp.makeInteger(-1), operand);
            binExp.loc = unaryExp.loc;
            return transform(binExp);
        }
        // trigger hard error
        return super.handleUnsupportedExp(unaryExp);
    }

    override Expression handleBinaryExp(ABinaryExp e) {
        immutable string[string] opMapping = [
            "+": "opPlus",
            "-": "opMinus",
            "·": "opMul",
            "/": "opDiv",
            "=": "opEq",
            "≠": "opNeq",
            ">": "opGt",
            "<": "opLt"
        ];
        
        static foreach(op;  [":=", "←", "×"]) {
            if (op==e.opRep) {
                writeln("Transforming ", e);
                transformChildren(e);
                writeln(e);
                return e;
            }
        }
        static foreach(op, accOp; ["+←": "+", "-←": "-", "/←": "/", "·←": "·"]) {
            // unfold op-assign expressions (a += b ==> a = a + b)
            if (auto opAssignExp = cast(BinaryExp!(Tok!op))e) {
                auto lhs = opAssignExp.e1;
                auto rhs = new BinaryExp!(Tok!accOp)(opAssignExp.e1, opAssignExp.e2);
                auto binExp = new BinaryExp!(Tok!"←")(lhs, rhs);
                
                rhs.loc = opAssignExp.loc;
                binExp.loc = opAssignExp.loc;
                
                return transform(binExp);
            }
        }

        static foreach(op; ["+", "-", "≠", "·", "/", ">", "<", "="]) {
            if (auto binExp = cast(BinaryExp!(Tok!op))e) {
                if (op in opMapping) {
                    auto funRef = new Identifier(opMapping[op]);
                    auto e1 = transform(binExp.e1);
                    auto e2 = transform(binExp.e2);
                    auto ce = new CallExp(funRef, new TupleExp([e1, e2]), false, true);
                    ce.loc = e.loc;
                    return ce;
                }
            }
        }
        // trigger hard error
        return super.handleUnsupportedExp(e);
    }
}

abstract class Transformation: AstVisitor!Expression {
    private TransformChildrenSwitch transformChildrenSwitch;

    this() {
        this.transformChildrenSwitch = new TransformChildrenSwitch(this);
    }

    final Expression transform(Expression expr) {
        return this.visit(expr);
    }
    
    final void transformChildren(Expression expr) {
        transformChildrenSwitch.visit(expr);
    }

    override Expression handleUnsupportedExp(Expression expr) {
        assert(false, format("Transformation %s encountered unhandled expression %s", 
            typeid(this), expr.toString));
    }
}

class TransformChildrenSwitch: AstVisitor!void {
    Transformation transformation;
    this(Transformation transformation) {
        this.transformation = transformation;
    }

    override void handleUnsupportedExp(Expression e) { /* nop */ }
    override void handleNullValue() { /* nop */ }

    override void handleFunctionDef(FunctionDef fd) {
        fd.params = cast(Parameter[])fd.params.map!(p => transformation.transform(p)).array;
	    fd.rret = transformation.transform(fd.rret);
	    fd.body_ = cast(CompoundExp)transformation.transform(fd.body_);
    }
    override void handleParameter(Parameter param) {
        param.vtype = transformation.transform(param.vtype);
    }
    override void handleIdentifier(Identifier ident) {
    }
    override void handleCompoundExp(CompoundExp compExp) {
        compExp.s = compExp.s.map!(s => transformation.transform(s)).array;
    }
    override void handleReturnExp(ReturnExp retExp) {
        retExp.e = transformation.transform(retExp.e);
    }
    override void handleBinaryExp(ABinaryExp binExp) {
        binExp.e1 = transformation.transform(binExp.e1);
        binExp.e2 = transformation.transform(binExp.e2);
    }
    override void handleSingleDefExp(SingleDefExp singleDef) {
        handleVarDecl(singleDef.decl);

        if (auto initializer=singleDef.initializer) {
            initializer.e2 = transformation.transform(singleDef.initializer.e2);
        }
    }
    override void handleLiteralExp(LiteralExp literalExp) {}
    override void handleTypeAnnotationExp(TypeAnnotationExp typeAnno) {
        typeAnno.e = transformation.transform(typeAnno.e);
        typeAnno.t = transformation.transform(typeAnno.t);
    }
    override void handleType(Type type) {}
    override void handleCallExp(CallExp callExp) {
        callExp.e = transformation.transform(callExp.e);
        callExp.arg = transformation.transform(callExp.arg);
    }
    override void handleTupleExp(TupleExp tupleExp) {
        tupleExp.e = tupleExp.e.map!(e => transformation.transform(e)).array;
    }
    override void handleVarDecl(VarDecl varDecl) {
        varDecl.vtype = transformation.transform(varDecl.vtype);
        varDecl.initializer = transformation.transform(varDecl.initializer);
    }
    override void handleLambdaExp(LambdaExp lambdaExp) {
        handleFunctionDef(lambdaExp.fd);
    }
    override void handleAssertExp(AssertExp assertExp) {
        assertExp.e = transformation.transform(assertExp.e);
    }
    override void handleIteExp(IteExp iteExp) {
        iteExp.cond = transformation.transform(iteExp.cond);
        iteExp.then = assertiveCast!CompoundExp(transformation.transform(iteExp.then));
        iteExp.othw = assertiveCast!CompoundExp(transformation.transform(iteExp.othw));
    }
    override void handleUnaryExp(AUnaryExp unaryExp) {
        unaryExp.e = transformation.transform(unaryExp.e);
    }
    override void handleForExp(ForExp forExp) {
        forExp.left = transformation.transform(forExp.left);
        forExp.right = transformation.transform(forExp.right);
        forExp.step = transformation.transform(forExp.step);
        forExp.bdy = assertiveCast!CompoundExp(transformation.transform(forExp.bdy));
    }
    override void handleWhileExp(WhileExp whileExp) {
        whileExp.cond = transformation.transform(whileExp.cond);
        whileExp.bdy = assertiveCast!CompoundExp(transformation.transform(whileExp.bdy));
    }
    override void handleParamDefExp(ParamDefExp paramExp) {
        paramExp.defineExp = transformation.transform(paramExp.defineExp);
	    paramExp.context = transformation.transform(paramExp.context);
    }
    override void handleDatDecl(DatDecl datDecl) {
        datDecl.dtype = assertiveCast!AggregateTy(transformation.transform(datDecl.dtype));
        datDecl.params = assertiveCast!(DatParameter[])(datDecl.params.map!(p => transformation.transform(p)).array);
        datDecl.body_ = assertiveCast!CompoundDecl(transformation.transform(datDecl.body_));
    }
    override void handleManifoldDecl(ManifoldDecl manifoldDecl) {
        manifoldDecl.tangentVecExp = transformation.transform(manifoldDecl.tangentVecExp);
	    manifoldDecl.tangentZeroExp = transformation.transform(manifoldDecl.tangentZeroExp);
	    manifoldDecl.moveOpDef = assertiveCast!FunctionDef(transformation.transform(manifoldDecl.moveOpDef));
    }
    override void handleArrayExp(ArrayExp arrayExp) {
        arrayExp.e = arrayExp.e.map!(e => transformation.transform(e)).array;
    }
    override void handleFieldExp(FieldExp fieldExp) {
        fieldExp.e = transformation.transform(fieldExp.e);
    }
    override void handleIndexExp(IndexExp indexExp) {
        indexExp.e = transformation.transform(indexExp.e);
        indexExp.a = indexExp.a.map!(e => transformation.transform(e)).array;
    }
    override void handleInitExp(InitExp initExp) {
        initExp.target = transformation.transform(initExp.target);
    }
    override void handleManifoldMemberExp(UnresolvedManifoldMemberExp manifoldMemberExp) {
        manifoldMemberExp.target = transformation.transform(manifoldMemberExp.target);
    }
    override void handleManifoldMoveExp(ManifoldMoveExp moveExp) {
        moveExp.target = transformation.transform(moveExp.target);
    }
    override void handleParameterSetHandleExp(ParameterSetHandleExp paramHandleExp) {
        paramHandleExp.target = transformation.transform(paramHandleExp.target);
    }

    private T assertiveCast(T, E)(E e) {
        auto ec = cast(T)e;
        assert(!!ec, format("Expected transformation result expression %s to be of type %s but was %s.",
            e, T.stringof, typeid(e)));
        return ec;
    }
}