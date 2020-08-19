module ast.visitor;

import ast.expression, ast.declaration, ast.type, ast.error, ast.lexer, ast.type, ast.visitor;

import std.typecons : tuple, Tuple;
import std.array;
import std.algorithm.iteration, std.algorithm.sorting, std.algorithm.searching;
import std.conv;
import std.format;
import std.file;
import std.stdio;

abstract class AstVisitor(T) {
    class RecursionGuard {
        private bool[Node] visited;
        bool hasVisited(Node n) {
            return (n in this.visited) ? true : false;
        }
        void flagVisited(Node n) {
            this.visited[n] = true;
        }
    }
    RecursionGuard recursionGuard;

    this() {
        this.recursionGuard = new RecursionGuard();
    }

    abstract T handleUnsupportedExp(Expression expr);
    abstract T handleNullValue();

    T handleFunctionDef(FunctionDef fd) {
        return handleUnsupportedExp(fd);
    }
    T handleParameter(Parameter param) {
        return handleUnsupportedExp(param);
    }
    T handleIdentifier(Identifier ident) {
        return handleUnsupportedExp(ident);
    }
    T handleCompoundExp(CompoundExp compExp) {
        return handleUnsupportedExp(compExp);
    }
    T handleReturnExp(ReturnExp retExp) {
        return handleUnsupportedExp(retExp);
    }
    T handleBinaryExp(ABinaryExp binExp) {
        return handleUnsupportedExp(binExp);
    }
    T handleSingleDefExp(SingleDefExp singleDef) {
        return handleUnsupportedExp(singleDef);
    }
    T handleLiteralExp(LiteralExp literalExp) {
        return handleUnsupportedExp(literalExp);
    }
    T handleTypeAnnotationExp(TypeAnnotationExp typeAnno) {
        return handleUnsupportedExp(typeAnno);
    }
    T handleType(Type type) {
        return handleUnsupportedExp(type);
    }
    T handleCallExp(CallExp callExp) {
        return handleUnsupportedExp(callExp);
    }
    T handleTupleExp(TupleExp tupleExp) {
        return handleUnsupportedExp(tupleExp);
    }
    T handleVarDecl(VarDecl varDecl) {
        return handleUnsupportedExp(varDecl);
    }
    T handleLambdaExp(LambdaExp lambdaExp) {
        return handleUnsupportedExp(lambdaExp);
    }
    T handleAssertExp(AssertExp assertExp) {
        return handleUnsupportedExp(assertExp);
    }
    T handleIteExp(IteExp iteExp) {
        return handleUnsupportedExp(iteExp);
    }
    T handleUnaryExp(AUnaryExp unaryExp) {
        return handleUnsupportedExp(unaryExp);
    }
    T handleForExp(ForExp forExp) {
        return handleUnsupportedExp(forExp);
    }
     T handleWhileExp(WhileExp whileExp) {
        return handleUnsupportedExp(whileExp);
    }
    T handleParamDefExp(ParamDefExp paramExp) {
        return handleUnsupportedExp(paramExp);
    }
    T handleDatDecl(DatDecl datDecl) {
        return handleUnsupportedExp(datDecl);
    }
    T handleManifoldDecl(ManifoldDecl manifoldDecl) {
        return handleUnsupportedExp(manifoldDecl);
    }
    T handleArrayExp(ArrayExp arrayExp) {
        return handleUnsupportedExp(arrayExp);
    }
    T handleFieldExp(FieldExp fieldExp) {
        return handleUnsupportedExp(fieldExp);
    }
    T handleIndexExp(IndexExp exp) {
        return handleUnsupportedExp(exp);
    }
    T handleInitExp(InitExp exp) {
        return handleUnsupportedExp(exp);
    }
    T handleParameterSetHandleExp(ParameterSetHandleExp exp) {
        return handleUnsupportedExp(exp);
    }
    T handlePullExp(PullExp pullExp) {
        return handleUnsupportedExp(pullExp);
    }
    T handleSliceExp(SliceExp sliceExp) {
        return handleUnsupportedExp(sliceExp);
    }
    T handleCommentExp(CommentExp commentExp) {
        return handleUnsupportedExp(commentExp);
    }
    T handleInitializedFunctionExp(InitializedFunctionExp funExp) {
        return handleUnsupportedExp(funExp);
    }
    T handleImportExp(ImportExp importExp) {
        return handleUnsupportedExp(importExp);
    }
    T handleNoGradExp(NoGradExp nogradExp) {
        return handleUnsupportedExp(nogradExp);
    }

    T visit(Expression expr) {
        if (expr is null) { 
            return handleNullValue();
        }
        if (recursionGuard.hasVisited(expr)) {
            static if(is(T == void)) { return; } 
            else { return expr; }
        }
        recursionGuard.flagVisited(expr);

        if (auto fd = cast(FunctionDef)expr) {
            return this.handleFunctionDef(fd);
        } else if (auto param = cast(Parameter)expr) {
            return this.handleParameter(param);
        } else if (auto importExp = cast(ImportExp)expr) {
            return this.handleImportExp(importExp);
        } else if (auto varDecl = cast(VarDecl)expr) {
            return this.handleVarDecl(varDecl);
        } else if (auto ident = cast(Identifier)expr) {
            return this.handleIdentifier(ident);
        } else if (auto compExp = cast(CompoundExp)expr) {
            return this.handleCompoundExp(compExp);
        } else if (auto retExp = cast(ReturnExp)expr) {
            return this.handleReturnExp(retExp);
        } else if (auto binExp = cast(ABinaryExp)expr) {
            return this.handleBinaryExp(binExp);
        } else if (auto singleDef = cast(SingleDefExp)expr) {
            return this.handleSingleDefExp(singleDef);
        } else if (auto litExp = cast(LiteralExp)expr) {
            return this.handleLiteralExp(litExp);
        } else if (auto typeAnnoExp = cast(TypeAnnotationExp)expr) {
            return this.handleTypeAnnotationExp(typeAnnoExp);
        } else if (auto type = cast(Type)expr) {
            return this.handleType(type);
        } else if (auto callExp = cast(CallExp)expr) {
            return this.handleCallExp(callExp);
        } else if (auto tupleExp = cast(TupleExp)expr) {
            return this.handleTupleExp(tupleExp);
        } else if (auto lambdaExp = cast(LambdaExp)expr) {
            return this.handleLambdaExp(lambdaExp);
        } else if (auto assertExp = cast(AssertExp)expr) {
            return this.handleAssertExp(assertExp);
        } else if (auto arrayExp = cast(ArrayExp)expr) {
            return this.handleArrayExp(arrayExp);
        } else if (auto iteExp = cast(IteExp)expr) {
            return this.handleIteExp(iteExp);
        } else if (auto unaryExp = cast(AUnaryExp)expr) {
            return this.handleUnaryExp(unaryExp);
        } else if (auto forExp = cast(ForExp)expr) {
            return this.handleForExp(forExp);
        } else if (auto whileExp = cast(WhileExp)expr) {
            return this.handleWhileExp(whileExp);
        } else if (auto paramExp = cast(ParamDefExp)expr) {
            return this.handleParamDefExp(paramExp);
        } else if (auto datDecl = cast(DatDecl)expr) {
            return this.handleDatDecl(datDecl);
        } else if (auto manifoldDecl = cast(ManifoldDecl)expr) {
            return this.handleManifoldDecl(manifoldDecl);
        } else if (auto fieldExp = cast(FieldExp)expr) {
            return this.handleFieldExp(fieldExp);
        } else if (auto indexExp = cast(IndexExp)expr) {
            return this.handleIndexExp(indexExp);
        } else if (auto initExp = cast(InitExp)expr) {
            return this.handleInitExp(initExp);
        } else if (auto parameterSetHandleExp = cast(ParameterSetHandleExp)expr) {
            return this.handleParameterSetHandleExp(parameterSetHandleExp);
        } else if (auto pullExp = cast(PullExp)expr) {
            return this.handlePullExp(pullExp);
        } else if (auto sliceExp = cast(SliceExp)expr) {
            return this.handleSliceExp(sliceExp);
        } else if (auto commentExp = cast(CommentExp)expr) {
            return this.handleCommentExp(commentExp);
        } else if (auto funExp = cast(InitializedFunctionExp)expr) {
            return this.handleInitializedFunctionExp(funExp);
        } else if (auto noGradExp = cast(NoGradExp)expr) {
            return this.handleNoGradExp(noGradExp);
        } else {
            return this.handleUnsupportedExp(expr);
        }
    }
}
