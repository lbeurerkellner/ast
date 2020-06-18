module ast.ad;

import ast.scope_, ast.declaration, ast.expression, ast.type;
import std.format;
import std.stdio;

FunctionDef generatePullback(FunctionDef fd, Scope sc) {
    Parameter[] params = fd.params;
	Expression rret = fd.rret;
	CompoundExp body_ = fd.body_;

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

    writeln(format("Generating pullback for function %s", fd.name.toString));

    // check ftype
    ProductTy ftype = fd.ftype;
    Expression dom = ftype.dom;
    Expression cod = ftype.cod;

    // cannot generate pullback for functions w/o arguments or w/o return types 
    if (dom==unit||cod==unit) {
        return  null;
    }

    if (!isDifferentiableType(dom, sc) || !isDifferentiableType(cod, sc)) {
        return null;
    }

    // sc.error(format("cannot generate pullback for non-differentiable function %s", fd.name), fd.loc);

    return null;
}

bool isDifferentiableType(Expression t, Scope sc) {
    if (auto ty = cast(Type)t) {
        if (ty.manifold(sc) !is null) {
            return true;
        }
    }

    sc.error(format("type %s is not differentiable (no manifold capabilities)", t.toString), t.loc);
    return false;
}