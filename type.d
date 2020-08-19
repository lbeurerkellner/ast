// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.type;
import astopt;

import std.array, std.algorithm, std.conv;
import std.functional, std.range;
import ast.expression, ast.declaration, ast.semantic_, ast.scope_, util;

bool isSameType(Expression lhs,Expression rhs){
	return lhs.eval() == rhs.eval(); // TODO: evaluation context?
}

enum NumericType{
	none,
	Bool,
	ℕt,
	ℤt,
	ℚt,
	ℝ,
	ℂ,
}

NumericType whichNumeric(Expression t){ // TODO: more general solution
	import std.traits: EnumMembers;
	static foreach(type;[EnumMembers!NumericType].filter!(x=>x!=NumericType.none))
		if(mixin(text("cast(",to!string(type).endsWith("t")?to!string(type)[0..$-1]:to!string(type),"Ty)t"))) return type;
	return NumericType.none;
}

bool isNumeric(Expression t){
	if (auto ty = cast(Type)t) t = unalias(ty);
	return whichNumeric(t)!=NumericType.none;
}

Expression getNumeric(int which,bool classical){
	final switch(which){
		import std.traits: EnumMembers;
		static foreach(type;[EnumMembers!NumericType].filter!(x=>x!=NumericType.none))
			case mixin(text("NumericType.",type)): return mixin(text(type))(classical);
		case NumericType.none: return null;
	}
}

string preludeNumericTypeName(Expression e){
	import ast.semantic_: modules;
	if(preludePath() !in modules) return null;
	auto exprssc=modules[preludePath()];
	auto sc=exprssc[1];
	auto ce=cast(CallExp)e;
	if(!ce) return null;
	auto id=cast(Identifier)ce.e;
	if(!id) return null;
	if(!id.meaning||id.meaning.scope_ !is sc) return null;
	return id.name;
}

bool isInt(Expression e){ return preludeNumericTypeName(e)=="int"; }
bool isUint(Expression e){ return preludeNumericTypeName(e)=="uint"; }
bool isFloat(Expression e){ return preludeNumericTypeName(e)=="float"; }
bool isRat(Expression e){ return preludeNumericTypeName(e)=="rat"; }

bool isSubtype(Expression lhs,Expression rhs){
	if(!lhs||!rhs) return false;
	if(cast(AnyTy)rhs !is null) return true;
	auto l=lhs.eval(), r=rhs.eval();
	l = unalias(l); r = unalias(r);
	auto wl=whichNumeric(l), wr=whichNumeric(r);
	if(!lhs.isClassical()&&rhs.isClassical()) return false;
	if(wl==NumericType.none||wr==NumericType.none) return l.isSubtypeImpl(r);
	return wl<=wr;
}

Expression combineTypes(Expression lhs,Expression rhs,bool meet){ // TODO: more general solution // TODO: ⊤/⊥?
	import std.format : format;
	if(!lhs) return rhs;
	if(!rhs) return lhs;
	if(lhs == rhs) return lhs;
	auto l=lhs.eval(), r=rhs.eval();
	auto wl=whichNumeric(l), wr=whichNumeric(r);
	if(wl==NumericType.none&&wr==NumericType.none) return l.combineTypesImpl(r,meet);
	// special case for scalar multiplication of tangent vectors
	if(cast(TangentVectorTy)r||cast(TangentVectorTy)l) return l.combineTypesImpl(r, meet);
	if(wl==NumericType.none||wr==NumericType.none) return null;
	return getNumeric(meet?min(wl,wr):max(wl,wr),meet?lhs.isClassical()||rhs.isClassical():lhs.isClassical()&&rhs.isClassical());
}

Expression joinTypes(Expression lhs,Expression rhs){
	return combineTypes(lhs,rhs,false);
}
Expression meetTypes(Expression lhs,Expression rhs){
	return combineTypes(lhs,rhs,true);
}

abstract class Type: Expression{
	this(){ if(!this.type) this.type=typeTy; sstate=SemState.completed; }
	override @property string kind(){ return "type"; }
	override string toString(){ return "T"; }
	abstract override bool opEquals(Object r);
	abstract override bool isClassical();
	override Annotation getAnnotation(){ return Annotation.qfree; }

	override bool isSubtypeImpl(Expression other) {
		if (auto anyType = cast(AnyTy)other) {
			return true;
		}
		return super.isSubtypeImpl(other);
	}

	final Manifold manifold(Scope sc) {
		if (!isManifoldType) return null;
		assert(sc);

		return memoize!((Type type, Scope sc) {
			return this.manifoldImpl(sc);
		})(this, sc);
	}

	// returns the manifold implementation for this type or null if none was defined
	Manifold manifoldImpl(Scope sc) {
		import std.format : format;

		// TODO: find something better than this.toString here
		Identifier manifoldId = new Identifier("manifold " ~ this.toString);
		if (auto decl = cast(ManifoldDecl)sc.lookup(manifoldId,false,true,Lookup.probing)) {
			decl = manifoldDeclSemantic(decl, sc);
			auto mtype = decl.mtype;
			if (!mtype) {
				return null;
			}
			return mtype;
		} else {
			// writeln(format("Could not find manifold declaration for type %s under name %s.", this.toString(), manifoldId.toString()));
			return null;
		}
	}

	override Expression tangentVecTy(Scope sc) {
		Identifier manifoldId = new Identifier("manifold " ~ this.toString);
		if (auto decl = cast(ManifoldDecl)sc.lookup(manifoldId,false,true,Lookup.probing)) {
			decl = manifoldDeclSemantic(decl, sc);
			return decl.tangentVecExp;
		} else {
			return null;
		}
	}
}

class ErrorTy: Type{
	this(){}//{sstate = SemState.error;}
	override ErrorTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){return "__error";}
	override bool isClassical(){ return true; }
	mixin VariableFree;
}

class BoolTy: Type{
	private bool classical;
	private this(bool classical){ this.classical=classical; }
	override BoolTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!𝔹":"𝔹";
		else return "𝔹";
	}
	override bool opEquals(Object o){
		auto r=cast(BoolTy)o;
		return r && classical==r.classical;
	}
	override bool isClassical(){
		return classical;
	}
	override bool hasClassicalComponent(){
		return classical;
	}
	override BoolTy getClassical(){
		return Bool(true);
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}
static if(language==silq) private BoolTy[2] theBool;
else private BoolTy theBool;

BoolTy Bool(bool classical=true){
	static if(language==silq) return theBool[classical]?theBool[classical]:(theBool[classical]=new BoolTy(classical));
	else return theBool?theBool:(theBool=new BoolTy(true));
}

class ℕTy: Type{
	static if(language==silq) private bool classical;
	else private enum classical=true;
	private this(bool classical){
		static if(language==silq) this.classical=classical;
	}
	override ℕTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!ℕ":"ℕ";
		else return "ℕ";
	}
	override bool opEquals(Object o){
		auto r=cast(ℕTy)o;
		return r&&classical==r.classical;
	}
	override bool isClassical(){
		return classical;
	}
	override bool hasClassicalComponent(){
		return classical;
	}
	override ℕTy getClassical(){
		return ℕt(true);
	}

	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}
static if(language==silq) private ℕTy[2] theℕ;
else private ℕTy theℕ;

ℕTy ℕt(bool classical=true){
	static if(language==silq) return theℕ[classical]?theℕ[classical]:(theℕ[classical]=new ℕTy(classical));
	else return theℕ?theℕ:(theℕ=new ℕTy(true));
}

class ℤTy: Type{
	static if(language==silq) private bool classical;
	else private enum classical=true;
	private this(bool classical){
		static if(language==silq) this.classical=classical;
	}
	override ℤTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!ℤ":"ℤ";
		else return "ℤ";
	}
	override bool opEquals(Object o){
		auto r=cast(ℤTy)o;
		return r&&classical==r.classical;
	}
	override bool isClassical(){
		return classical;
	}
	override bool hasClassicalComponent(){
		return classical;
	}
	override ℤTy getClassical(){
		return ℤt(true);
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}
static if(language==silq) private ℤTy[2] theℤ;
else private ℤTy theℤ;

ℤTy ℤt(bool classical=true){
	static if(language==silq) return theℤ[classical]?theℤ[classical]:(theℤ[classical]=new ℤTy(classical));
	else return theℤ?theℤ:(theℤ=new ℤTy(true));
}

class ℚTy: Type{
	static if(language==silq) private bool classical;
	else private enum classical=true;
	private this(bool classical){
		static if(language==silq) this.classical=classical;
	}
	override ℚTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!ℚ":"ℚ";
		else return "ℚ";
	}
	override bool opEquals(Object o){
		auto r=cast(ℚTy)o;
		return r&&classical==r.classical;
	}
	override bool isClassical(){
		return classical;
	}
	override bool hasClassicalComponent(){
		return classical;
	}
	override ℚTy getClassical(){
		return ℚt(true);
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}
static if(language==silq) private ℚTy[2] theℚ;
else private ℚTy theℚ;

ℚTy ℚt(bool classical=true){
	static if(language==silq) return theℚ[classical]?theℚ[classical]:(theℚ[classical]=new ℚTy(classical));
	else return theℚ?theℚ:(theℚ=new ℚTy(true));
}

class ℝTy: Type{
	static if(language==silq) private bool classical;
	else private enum classical=true;
	private this(bool classical){
		static if(language==silq) this.classical=classical;
	}

	override ℝTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!ℝ":"ℝ";
		else return "ℝ";
	}
	override bool opEquals(Object o){
		auto r=cast(ℝTy)o;
		return r&&classical==r.classical;
	}
	override bool isClassical(){
		return classical;
	}
	override bool hasClassicalComponent(){
		return classical;
	}
	override ℝTy getClassical(){
		return ℝ(true);
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}
static if(language==silq) private ℝTy[2] theℝ;
else private ℝTy theℝ;

ℝTy ℝ(bool classical=true){
	static if(language==silq) return theℝ[classical]?theℝ[classical]:(theℝ[classical]=new ℝTy(classical));
	else return theℝ?theℝ:(theℝ=new ℝTy(true));
}

class ℂTy: Type{
	static if(language==silq) private bool classical;
	else private enum classical=true;
	private this(bool classical){
		static if(language==silq) this.classical=classical;
	}
	override ℂTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!ℂ":"ℂ";
		return "ℂ";
	}
	override bool opEquals(Object o){
		auto r=cast(ℂTy)o;
		return r&&classical==r.classical;
	}
	override bool isClassical(){
		return classical;
	}
	override bool hasClassicalComponent(){
		return classical;
	}
	override ℂTy getClassical(){
		return ℂ(true);
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}
static if(language==silq) private ℂTy[2] theℂ;
else private ℂTy theℂ;

ℂTy ℂ(bool classical=true){
	static if(language==silq) return theℂ[classical]?theℂ[classical]:(theℂ[classical]=new ℂTy(classical));
	else return theℂ?theℂ:(theℂ=new ℂTy(true));
}



class AggregateTy: Type{
	DatDecl decl;
	static if(language==silq){
		bool classical;
		private AggregateTy classicalTy;
	}else enum classical=true;
	static if(language==dp){
		bool isParameterized;
	}
	this(DatDecl decl,bool classical){
		if(!classical) assert(decl.isQuantum);
		this.decl=decl;
		this.isParameterized=decl.isParameterized;
		static if(language==silq){
			this.classical=classical;
			if(classical) classicalTy=this;
			else classicalTy=New!AggregateTy(decl,true);
		}
	}
	override AggregateTy copyImpl(CopyArgs args){
		return this;
	}
	override bool opEquals(Object o){
		if(auto r=cast(AggregateTy)o)
			return decl is r.decl && classical==r.classical;
		return false;
	}
	override string toString(){
		return decl.name.name;
	}
	override bool isClassical(){
		return classical;
	}
	override bool hasClassicalComponent(){
		return classical;
	}
	override AggregateTy getClassical(){
		static if(language==silq) return classicalTy;
		else return this;
	}

	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) e){
		return 0;
	}

	override bool isSubtypeImpl(Expression other) {
		if (auto aggrTy = isDataTyId(other)) {
			return super.isSubtypeImpl(aggrTy);
		}
		return super.isSubtypeImpl(other);
	}
}

class ContextTy: Type{
	static if(language==silq) private bool classical;
	else private enum classical=true;
	private this(bool classical){
		static if(language==silq) this.classical=classical;
	}
	override ContextTy copyImpl(CopyArgs args){
		return this;
	}
	override bool opEquals(Object o){
		auto ctx=cast(ContextTy)o;
		return ctx&&ctx.classical==classical;
	}
	override bool isClassical(){
		return classical;
	}
	override bool hasClassicalComponent(){
		return classical;
	}
	override string toString(){
		static if(language==silq) return (classical?"!":"")~"`Ctx";
		else return "`Ctx";
	}
	override ContextTy getClassical(){
		return contextTy(true);
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) e){
		return 0;
	}
}
static if(language==silq) private ContextTy[2] theContextTy;
else private ContextTy theContextTy;
ContextTy contextTy(bool classical=true){
	static if(language==silq) return theContextTy[classical]?theContextTy[classical]:(theContextTy[classical]=new ContextTy(classical));
	else return theContextTy?theContextTy:(theContextTy=new ContextTy(true));
}

interface ITupleTy{
	@property size_t length();
	Expression opIndex(size_t i);
	Expression opSlice(size_t l,size_t r);
}

class TupleTy: Type,ITupleTy{
	Expression[] types;
	override ITupleTy isTupleTy(){ return this; }
	@property size_t length(){ return types.length; }
	Expression opIndex(size_t i){ return types[i]; }
	Expression opSlice(size_t l,size_t r){ return tupleTy(types[l..r]); }
	private this(Expression[] types)in{
		assert(types.all!(x=>x.type.isTypeTy));
		assert(!types.length||!types[1..$].all!(x=>x==types[0]));
	}body{
		this.types=types;
	}
	override TupleTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		if(!types.length) return "𝟙";
		if(types.length==1) return "("~types[0].toString()~")¹";
		string addp(Expression a){
			if(cast(FunTy)a) return "("~a.toString()~")";
			return a.toString();
		}
		return types.map!(a=>a.isTupleTy()&&a!is unit?"("~a.toString()~")":addp(a)).join(" × ");
	}
	override int freeVarsImpl(scope int delegate(string) dg){
		foreach(t;types)
			if(auto r=t.freeVarsImpl(dg))
				return r;
		return 0;
	}
	override Type substituteImpl(Expression[string] subst){
		auto ntypes=types.dup;
		foreach(ref t;ntypes) t=t.substitute(subst);
		return tupleTy(ntypes);
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto tt=rhs.isTupleTy();
		if(!tt||types.length!=tt.length) return false;
		return all!(i=>types[i].unify(tt[i],subst,meet))(iota(types.length));
	}
	override bool opEquals(Object o){
		if(auto r=cast(TupleTy)o)
			return types==r.types;
		return false;
	}
	override bool isSubtypeImpl(Expression r){
		auto ltup=this,rtup=r.isTupleTy();
		if(rtup&&ltup.types.length==rtup.length)
		   return all!(i=>isSubtype(ltup.types[i],rtup[i]))(iota(ltup.types.length));
		auto rarr=cast(ArrayTy)r;
		if(rarr) return all!(i=>isSubtype(ltup.types[i],rarr.next))(iota(ltup.types.length));
		return false;
	}
	override Expression combineTypesImpl(Expression r,bool meet){
		auto ltup=this,rtup=r.isTupleTy();
		if(rtup&&ltup.types.length==rtup.length){
			auto rtypes=zip(ltup.types,iota(rtup.length).map!(i=>rtup[i])).map!((t)=>combineTypes(t.expand,meet)).array;
			if(all!(x=>x !is null)(rtypes)) return tupleTy(rtypes);
		}
		if(auto rarr=cast(ArrayTy)r){
			if(meet){
				auto rtypes=zip(ltup.types,iota(length).map!(i=>rarr.next)).map!((t)=>combineTypes(t.expand,meet)).array;
				if(all!(x=>x !is null)(rtypes)) return tupleTy(rtypes);
			}else{
				auto rtype=ltup.types.fold!((a,b)=>combineTypes(a,b,meet))(rarr.next);
				if(rtype) return arrayTy(rtype);
			}
		}
		return null;
	}
	override bool isClassical(){
		return all!(x=>x.isClassical())(types);
	}
	override bool hasClassicalComponent(){
		return any!(x=>x.isClassical())(types);
	}
	override Expression getClassical(){
		auto ntypes=types.map!(x=>x.getClassical()).array;
		if(all!(x=>x !is null)(ntypes)) return tupleTy(ntypes);
		return null;
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		foreach(x;types) if(auto r=dg(x)) return r;
		return 0;
	}
	override Expression evalImpl(Expression ntype){
		assert(ntype.isTypeTy);
		auto ntypes=types.map!(t=>t.eval()).array;
		if(ntypes==types) return this;
		return tupleTy(ntypes);
	}
}

Type unit(){ return tupleTy([]); }

Type tupleTy(Expression[] types)in{
	assert(types.all!(x=>x.type.isTypeTy));
}body{
	import ast.lexer: Token,Tok;
	if(types.length&&types.all!(x=>x==types[0])){
		auto len=LiteralExp.makeInteger(types.length);
		return vectorTy(types[0],len);
	}
	return memoize!((Expression[] types)=>new TupleTy(types))(types);
}

size_t numComponents(Expression t){
	if(auto tpl=t.isTupleTy())
		return tpl.length;
	return 1;
}

class ArrayTy: Type{
	Expression next;

	override @property bool isManifoldType() {
		if (auto n = next) {
			return next.isManifoldType();
		} else {
			return false;
		}
	}

	private this(Expression next)in{
		assert(next.type.isTypeTy);
	}body{
		this.next=next;
	}
	override ArrayTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		bool p=cast(FunTy)next||next.isTupleTy()&&next!is unit;
		return p?"("~next.toString()~")[]":next.toString()~"[]";
	}
	override int freeVarsImpl(scope int delegate(string) dg){
		return next.freeVarsImpl(dg);
	}
	override ArrayTy substituteImpl(Expression[string] subst){
		return arrayTy(next.substitute(subst));
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		if(auto vt=cast(VectorTy)rhs)
			return next.unifyImpl(vt.next,subst,meet);
		if(auto tt=cast(TupleTy)rhs)
			return tt.types.all!(ty=>next.unifyImpl(ty,subst,meet));
		if(auto at=cast(ArrayTy)rhs)
			return next.unifyImpl(at.next,subst,meet);
		return false;
	}
	override ArrayTy evalImpl(Expression ntype){
		assert(ntype.isTypeTy);
		return arrayTy(next.eval());
	}
	override bool opEquals(Object o){
		if(auto r=cast(ArrayTy)o)
			return next==r.next;
		return false;
	}
	override bool isSubtypeImpl(Expression r){
		auto larr=this,rarr=cast(ArrayTy)r;
		if(!rarr) return false;
		return isSubtype(larr.next,rarr.next);
	}
	override Expression combineTypesImpl(Expression r,bool meet){
		auto larr=this,rarr=cast(ArrayTy)r;
		if(rarr){
			auto combinedNext=combineTypes(larr.next,rarr.next,meet);
			if(combinedNext) return arrayTy(combinedNext);
		}
		if(auto rvec=cast(VectorTy)r){
			auto nnext=combineTypes(next,rvec.next,meet);
			if(nnext){
				if(meet) return vectorTy(nnext,rvec.num);
				else return arrayTy(nnext);
			}
		}
		if(auto rtup=r.isTupleTy()){
			if(meet){
				auto ntypes=iota(rtup.length).map!(i=>combineTypes(next,rtup[i],meet)).array;
				if(all!(x=>x is null)(ntypes)) return tupleTy(ntypes);
			}else{
				auto rtype=iota(rtup.length).map!(i=>rtup[i]).fold!((a,b)=>combineTypes(a,b,meet))(next);
				if(rtype) return arrayTy(rtype);
			}
		}
		return null;
	}
	override bool isClassical(){
		return next.isClassical();
	}
	override bool hasClassicalComponent(){
		return true; // length is classical
	}
	override Expression getClassical(){
		auto nnext=next.getClassical();
		if(!nnext) return null;
		return arrayTy(nnext);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(next);
	}

	override Expression tangentVecTy(Scope sc) {
		Expression nextTangentVecTy = this.next.tangentVecTy(sc);
		if (!nextTangentVecTy) return null;
		// construct element-wise tangentVector
		return arrayTy(nextTangentVecTy);
	}

	override Manifold manifoldImpl(Scope sc) {
		Type nextType = cast(Type)this.next;
		if (!nextType) {
			return null;
		}
		Manifold nextManifold = nextType.manifoldImpl(sc);
		if (!nextManifold) {
			return null;
		}
		// construct element-wise tangentVector
		Expression elementWiseTangentVecTy = tangentVecTy(sc);

		Scope containerScope = nextManifold.manifoldDecl.declScope.parent;
		// use internal ManifoldDeclScope w/o corresponding ManifoldDecl
		auto declScope = new ManifoldDeclScope(containerScope, 
			new ManifoldDecl(new Identifier("`"~this.toString), null));
		declScope.decl.typeName = this;

		// construct tangentZero 
		auto elementWiseTangentVecZero = new FunctionDef(new Identifier("__arrayTy_tangentZero"), [], true, null, null);
		// construct move operation
		auto elementWiseMoveOpDef = new FunctionDef(new Identifier("__arrayTy_tangentZero"), [new Parameter(true, new Identifier("along"), elementWiseTangentVecTy)], true, null, null);

		declScope.decl.tangentZeroDef = elementWiseTangentVecZero;
		declScope.decl.moveOpDef = elementWiseMoveOpDef;
		declScope.decl.tangentVecExp = elementWiseTangentVecTy;

		// semantically process constructed manifold operations
		foreach(ref op; [elementWiseTangentVecZero, elementWiseMoveOpDef]) {
			op = cast(FunctionDef)presemantic(op, declScope);
			op = functionDefSemantic(op, declScope);
		}

		auto pointWiseManifold = new Manifold(this, elementWiseMoveOpDef, elementWiseTangentVecTy, elementWiseTangentVecZero);
		pointWiseManifold.manifoldDecl = declScope.decl;
		return pointWiseManifold;
	}
}

ArrayTy arrayTy(Expression next)in{
	assert(next&&next.type.isTypeTy);
}body{
	return memoize!((Expression next)=>new ArrayTy(next))(next);
}

class VectorTy: Type, ITupleTy{
	Expression next,num;

	override ITupleTy isTupleTy(){
		if(cast(LiteralExp)num) return this;
		return null;
	}
	override VectorTy copyImpl(CopyArgs args){
		return this;
	}
	@property Expression elementType(){
		if (auto nextVecTy=cast(VectorTy)next) {
			return nextVecTy.elementType;
		}
		return next;
	}
	@property size_t length(){
		auto lit=cast(LiteralExp)num;
		assert(!!lit);
		return to!size_t(lit.lit.str); // TODO: avoid crash if length is too big
	}
	@property Expression[] shape(){
		if (auto vecTy=cast(VectorTy)next) {
			return [num] ~ vecTy.shape;
		} else {
			return [num];
		}
	}
	override @property bool isManifoldType() {
		if (auto ety = elementType) {
			return ety.isManifoldType();
		} else {
			return false;
		}
	}
	@property TupleExp shapeTuple(){
		auto shapeExprs = shape;
		if (!shapeExprs.each!(se => isSubtype(se.type, ℕt(true)))) {
			return null;
		}
		auto shapeTuple = new TupleExp(shapeExprs);
		shapeTuple.type = tupleTy(iota(shapeExprs.length).map!(i => to!Expression(ℕt(true))).array);
		if (shapeExprs.length > 0) {
			shapeTuple.loc = shapeExprs[0].loc.to(shapeExprs[$-1].loc);
		} else {
			shapeTuple.loc = num.loc;
		}
		shapeTuple.sstate = SemState.completed;
		return shapeTuple;
	}
	Expression opIndex(size_t i){ return next; }
	Expression opSlice(size_t l,size_t r){
		assert(0<=l&&l<=r&&r<=length);
		auto len=LiteralExp.makeInteger(r-l);
		return vectorTy(next,len);
	}
	
	private this(Expression next,Expression num)in{
		assert(next.type.isTypeTy);
	}body{
		this.next=next;
		this.num=num;
		this.type=isManifoldType?manifoldTypeTy:typeTy;
		super();
	}
	override string toString(){
		bool p=cast(FunTy)next||next.isTupleTy&&next!is unit;
		bool q=!cast(Identifier)num&&!cast(LiteralExp)num; // TODO: improve
		return (p?"("~next.toString()~")^":next.toString()~"^")~(q?"("~num.toString()~")":num.toString());
	}
	override int freeVarsImpl(scope int delegate(string) dg){
		if(auto r=next.freeVarsImpl(dg)) return r;
		return num.freeVarsImpl(dg);
	}
	override Expression substituteImpl(Expression[string] subst){
		auto numSubst = num.substitute(subst);
		auto nextSubst = next.substitute(subst);

		// check for empty tuple as num
		if (auto tupExp=cast(TupleExp)numSubst) {
			if (tupExp.e.length == 0) {
				// consider T^() as T
				return nextSubst;
			}
		}

		return vectorTy(nextSubst,numSubst);
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		if(auto tt=cast(TupleTy)rhs)
			return tt.types.all!(ty=>next.unifyImpl(ty,subst,meet)) && num.unifyImpl(LiteralExp.makeInteger(tt.length),subst,meet);
		if(auto vt=cast(VectorTy)rhs) {
			if (isSubtype(this.num.type, arrayTy(ℕt(true)))) {
				if (!next.unifyImpl(vt.elementType,subst,meet)) {
					return false;
				}
				if (auto shapeTuple=vt.shapeTuple) {
					return num.unifyImpl(shapeTuple,subst,meet);
				}
				return false;
			} else {
				return next.unifyImpl(vt.next,subst,meet) && num.unifyImpl(vt.num,subst,meet);
			}
		}
		if (isSubtype(elementType, rhs)) {
			auto emptyTuple = new TupleExp([]);
			emptyTuple.type = unit;
			return num.unifyImpl(emptyTuple,subst, meet);
		}
		return false;
	}
	override VectorTy evalImpl(Expression ntype){
		assert(ntype.isTypeTy);
		return vectorTy(next.eval(),num.eval());
	}
	override bool opEquals(Object o){
		if(auto r=cast(VectorTy)o)
			return next==r.next&&num==r.num;
		return false;
	}

	override bool isSubtypeImpl(Expression r){
		if(auto rarr=cast(ArrayTy)r) return isSubtype(next,rarr.next);
		auto lvec=this,rvec=cast(VectorTy)r;
		if(rvec) return isSubtype(lvec.next,rvec.next) && num==rvec.num;
		auto ltup=this.isTupleTy(),rtup=r.isTupleTy();
		if(ltup&&rtup&&ltup.length==rtup.length)
			return all!(i=>isSubtype(ltup[i],rtup[i]))(iota(ltup.length));
		return false;
	}
	override Expression combineTypesImpl(Expression r,bool meet){
		if(auto rarr=cast(ArrayTy)r){
			auto nnext=combineTypes(next,rarr.next,meet);
			if(nnext){
				if(meet) return vectorTy(nnext,num);
				else return arrayTy(nnext);
			}
		}
		auto lvec=this,rvec=cast(VectorTy)r;
		if(rvec){
			auto nnext=combineTypes(lvec.next,rvec.next,meet);
			if(!nnext) return null;
			if(num==rvec.num){
				return vectorTy(nnext,num);
			}else if(!meet){
				return arrayTy(nnext);
			}else return null;
		}
		auto ltup=this.isTupleTy(),rtup=r.isTupleTy();
		if(rtup){
			bool equal=false;
			if(ltup) equal=ltup.length==rtup.length;
			else equal=num==LiteralExp.makeInteger(rtup.length);
			if(equal){
				auto rtypes=iota(rtup.length).map!(i=>combineTypes(next,rtup[i],meet)).array;
				if(all!(x=>x !is null)(rtypes)) return tupleTy(rtypes);
			}else if(!meet){
				auto nnext=iota(rtup.length).map!(i=>rtup[i]).fold!((a,b)=>combineTypes(a,b,meet))(next);
				if(nnext) return arrayTy(nnext);
			}else return null;
		}
		return null;
	}
	override bool isClassical(){
		return next.isClassical();
	}
	override bool hasClassicalComponent(){
		return next.hasClassicalComponent();
	}
	override Expression getClassical(){
		auto nnext=next.getClassical();
		if(!nnext) return null;
		return vectorTy(nnext,num);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(next)) return r;
		return dg(num);
	}

	override Expression tangentVecTy(Scope sc) {
		Expression elementType = this.elementType;
		if (!elementType) return null;
		Expression tangentVecTy = this.elementType.tangentVecTy(sc);
		if (!tangentVecTy) return null;
		// construct element-wise tangentVector
		return this.replacingElementType(tangentVecTy);
	}

	override Manifold manifoldImpl(Scope sc) {
		Type elementType = cast(Type)this.elementType;
		if (!elementType) {
			return null;
		}
		Manifold elementMType = elementType.manifoldImpl(sc);
		if (!elementMType) {
			return null;
		}
		// construct element-wise tangentVector
		Expression elementWiseTangentVecTy = tangentVecTy(sc);

		Scope containerScope = elementMType.manifoldDecl.declScope.parent;
		// use internal ManifoldDeclScope w/o corresponding ManifoldDecl
		auto declScope = new ManifoldDeclScope(containerScope, 
			new ManifoldDecl(new Identifier("`"~this.toString), null));
		declScope.decl.typeName = this;

		// construct tangentZero using the pointWise operator
		auto elementWiseTangentVecZero = makePointWiseTangentZeroExp(elementMType, this, elementWiseTangentVecTy, declScope);
		// construct move operation using pointWise operator (support as built-in in interpreter)
		auto elementWiseMoveOpDef = makePointWiseMoveOp(elementMType, elementWiseTangentVecTy, declScope);

		declScope.decl.tangentZeroDef = elementWiseTangentVecZero;
		declScope.decl.moveOpDef = elementWiseMoveOpDef;
		declScope.decl.tangentVecExp = elementWiseTangentVecTy;

		// semantically process constructed manifold operations
		foreach(ref op; [elementWiseTangentVecZero, elementWiseMoveOpDef]) {
			op = cast(FunctionDef)presemantic(op, declScope);
			op = functionDefSemantic(op, declScope);
		}

		auto pointWiseManifold = new Manifold(this, elementWiseMoveOpDef, elementWiseTangentVecTy,
			elementWiseTangentVecZero);
		pointWiseManifold.manifoldDecl = elementMType.manifoldDecl;
		return pointWiseManifold;
	}
}

VectorTy tensorTy(Expression dtype, Expression[] shape) {
	if (shape.length == 1) {
		return vectorTy(dtype, shape[0]);
	} else {
		return vectorTy(tensorTy(dtype, shape[1..$]), shape[0]);
	}
}

VectorTy vectorTy(Expression next, Expression num)in{
	assert(next&&next.type.isTypeTy);
	assert(num && (
		isSubtype(num.type,ℤt(true)) ||  
		isSubtype(num.type,arrayTy(ℤt(true))
	)));
}body{
	if (isSubtype(num.type, arrayTy(ℕt(true)))) {
		if (auto arrayExp = cast(ArrayExp)num) {
			if (arrayExp.e.length == 1) {
				num = arrayExp.e[0];
			}
		}
		if (auto tupleExp = cast(TupleExp)num) {
			if (tupleExp.e.length == 1) {
				num = tupleExp.e[0];
			}
		}
	}

	return memoize!((Expression next, Expression num){
		auto vecTy = new VectorTy(next,num);
		if (auto tupleExp = cast(TupleExp)num) {
			return tensorTy(vecTy.next, tupleExp.e);
		}
		if (auto arrayExp = cast(ArrayExp)num) {
			return tensorTy(vecTy.next, arrayExp.e);
		}
		return vecTy;
	})(next, num);
}

FunctionDef makePointWiseMoveOp(Manifold elementManifold, Expression tangentVecTy, Scope sc) {
	assert(elementManifold.moveOpDef !is null);
	assert(elementManifold.elementType !is null);
	assert(sc !is null);

	FunctionDef funDef = new PointWiseFunctionDef(new Identifier("move"), [
		new Parameter(false, new Identifier("along"), new FieldExp(new Identifier("this"), new Identifier("tangentVector")))
	], false, elementManifold.moveOpDef, unit);

	funDef.type = unit;
	funDef.isParameterized = false;

	return funDef;
}

VectorTy replacingElementType(VectorTy vecTy, Expression elementType) {
	if (auto nextVecTy=cast(VectorTy)vecTy.next) {
		return vectorTy(replacingElementType(nextVecTy, elementType), vecTy.num);
	} else {
		return vectorTy(elementType, vecTy.num);
	}
}


FunctionDef makePointWiseTangentZeroExp(Manifold elementManifold, VectorTy vectorType, Expression tangentVecTy, Scope sc) {
	assert(elementManifold.tangentZeroDef !is null);

	auto id = new Identifier("tangentZero");
	id.meaning = elementManifold.tangentZeroDef;
	auto fe = new FieldExp(new Identifier("e"), id);
	auto pointWiseCallExp = new CallExp(fe, new TupleExp([]), false, true);
	auto pointWiseLambda = new LambdaExp(new FunctionDef(new Identifier("_"), [
		new Parameter(true, new Identifier("e"), vectorType.elementType)
	], false, null, new CompoundExp([
		new ReturnExp(pointWiseCallExp)
	])));
	pointWiseLambda.fd.isParameterized = false;

	auto thisRef = new Identifier("this");
	auto args = new TupleExp([thisRef, pointWiseLambda]);
	auto ce = new CallExp(new Identifier("pointWise"), args, false, true);
	auto re = new ReturnExp(ce);

	auto fd = new FunctionDef(new Identifier("__pointwise_tangentZero"), [],
		true, new FieldExp(new Identifier("this"), new Identifier("tangentVector")), new CompoundExp([re]));
	fd.type = unit;
	fd.isParameterized = false;

	return fd;
}

static Expression elementType(Expression ty){
	if(auto at=cast(ArrayTy)ty) return at.next;
	if(auto vt=cast(VectorTy)ty) return vt.next;
	return null;
}

class AnyTy : Type {
	static if(language==silq) bool classical;
	else enum classical=true;
	private this(bool classical){
		static if(language==silq) this.classical=classical;
	}
	override AnyTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!any":"any";
		else return "any";
	}
	override bool opEquals(Object o){
		return !!cast(AnyTy)o;
	}
	override bool isClassical(){
		return classical;
	}
	override bool hasClassicalComponent(){
		// TODO Luca: not clear
		return true;
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}

AnyTy anyTy(bool classical=true){
	static if(language==silq) return memoize!((bool classical)=>new AnyTy(classical))(classical);
	else return memoize!(()=>new AnyTy(true));
}

class StringTy: Type{
	static if(language==silq) bool classical;
	else enum classical=true;
	private this(bool classical){
		static if(language==silq) this.classical=classical;
	}
	override StringTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!string":"string";
		else return "string";
	}
	override bool opEquals(Object o){
		return !!cast(StringTy)o;
	}
	override bool isClassical(){
		return classical;
	}
	override bool hasClassicalComponent(){
		return true; // length is classical
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
	override bool supportsBinaryOperatorImpl(string op, Expression operandType) {
		if (op=="+") {
			return isSubtype(operandType, stringTy) || isSubtype(operandType, ℝ(true));
		}
		return false;
	}

	override Expression combineTypesImpl(Expression rhs, bool meet) {
		if (cast(StringTy)rhs !is null) {
			return this;
		} else if (isSubtype(rhs, ℝ(true))) {
			return this;
		}
		return super.combineTypesImpl(rhs, meet);
	}
}

StringTy stringTy(bool classical=true){
	static if(language==silq) return memoize!((bool classical)=>new StringTy(classical))(classical);
	else return memoize!(()=>new StringTy(true));
}

enum Annotation{
	none,
	mfree,
	qfree
}


static if(language==silq) enum deterministic=Annotation.qfree;
static if(language==psi) enum deterministic=Annotation.none;
static if(language==dp) enum deterministic=Annotation.none;

string annotationToString(Annotation annotation){
	static if(language==silq) return annotation?text(annotation):"";
	static if(language==psi) return "";
	static if(language==dp) return annotation?text(annotation):"";
}

class RawProductTy: Expression{
	Parameter[] params;
	Expression cod;
	bool isSquare,isTuple;
	Annotation annotation;
	this(Parameter[] params,Expression cod,bool isSquare,bool isTuple,Annotation annotation){
		this.params=params; this.cod=cod;
		this.isSquare=isSquare; this.isTuple=isTuple;
		this.annotation=annotation;
	}
	override RawProductTy copyImpl(CopyArgs args){
		return new RawProductTy(params.map!(p=>p.copy(args)).array,cod.copy(args),isSquare,isTuple,annotation);
	}
	override string toString(){
		return "<unanalyzed Π type>"; // TODO: format nicely.
	}
	override bool isClassical(){
		assert(0);
	}
	override bool hasClassicalComponent(){
		assert(0);
	}

	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}

class ProductTy: Type{
	bool[] isConst;
	string[] names;
	Expression dom, cod;
	bool isSquare,isTuple;
	Annotation annotation;
	static if(language==silq){
		bool isClassical_;
		private ProductTy classicalTy;
	}else enum isClassical_=true;

	static if(language==dp){
		bool isParameterized=false;
		bool isInitialized=false;
		bool isDifferentiable=false;
		ProductTy isPullbackOf=null;
	}

	static if(language==dp) {
		private this(bool[] isConst,string[] names,
				 Expression dom,Expression cod,
				 bool isSquare,bool isTuple,
				 Annotation annotation,bool isClassical_,
				 bool isParameterized, bool isInitialized, bool isDifferentiable,
				 ProductTy primalTy)in{
			// TODO: assert that all names are distinct
			if(isTuple){
				auto tdom=dom.isTupleTy;
				assert(!!tdom);
				assert(names.length==tdom.length);
				assert(isConst.length==tdom.length);
			}else{
				assert(names.length==1);
				assert(isConst.length==1);
			}
			assert(cod.type.isTypeTy,text(cod));
		}body{
			this.isConst=isConst; // TODO: don't track this in PSI
			this.names=names; this.dom=dom; this.cod=cod;
			this.isSquare=isSquare; this.isTuple=isTuple;
			this.annotation=annotation;
			static if(language==silq){this.isClassical_=isClassical_;
				if(this.isClassical) classicalTy=this;
				else classicalTy=new ProductTy(isConst,names,dom,cod,isSquare,isTuple,annotation,true);
			}

			this.isParameterized=isParameterized;
			this.isInitialized=isInitialized;
			this.isDifferentiable=isDifferentiable;
			this.isPullbackOf=primalTy;
			// TODO: report DMD bug, New!ProductTy does not work
		}
	} else {
		private this(bool[] isConst,string[] names,
				 Expression dom,Expression cod,
				 bool isSquare,bool isTuple,
				 Annotation annotation,bool isClassical_)in{
			// TODO: assert that all names are distinct
			if(isTuple){
				auto tdom=dom.isTupleTy;
				assert(!!tdom);
				assert(names.length==tdom.length);
				assert(isConst.length==tdom.length);
			}else{
				assert(names.length==1);
				assert(isConst.length==1);
			}
			assert(cod.type.isTypeTy,text(cod));
		}body{
			this.isConst=isConst; // TODO: don't track this in PSI
			this.names=names; this.dom=dom; this.cod=cod;
			this.isSquare=isSquare; this.isTuple=isTuple;
			this.annotation=annotation;
			static if(language==silq){this.isClassical_=isClassical_;
				if(this.isClassical) classicalTy=this;
				else classicalTy=new ProductTy(isConst,names,dom,cod,isSquare,isTuple,annotation,true);
			}
			// TODO: report DMD bug, New!ProductTy does not work
		}
	}

	override ProductTy copyImpl(CopyArgs args){
		return this;
	}
	/+private+/ @property ITupleTy tdom()in{ // TODO: make private
		assert(isTuple);
	}body{
		auto r=dom.isTupleTy;
		assert(!!r);
		return r;
	}
	override string toString(){
		auto c=cod.toString();
		auto del=isSquare?"[]":"()";
		string r;
		if(!cod.hasAnyFreeVar(names)){
			string d;
			string addp(bool const_,Expression a,string del="()"){
				static if(language==silq){
					if(const_&&a.impliesConst()) const_=false;
				}else const_=false;
				if(cast(FunTy)a) return del[0]~(const_?"const (":"")~a.toString()~(const_?")":"")~del[1];
				if(a.isTupleTy()) return (const_?"const (":"")~a.toString()~(const_?")":"");
				return (const_?"const ":"")~a.toString();
			}
			if(all!(x=>!x)(isConst)){
				d=dom.toString();
				if(isSquare) d=del[0]~d~del[1];
			}else if(auto tpl=dom.isTupleTy()){
				if(isTuple){
					assert(!!tpl.length);
					if(tpl.length==1) return "("~(isConst[0]&&!tpl[0].impliesConst()?"const ":"")~tpl[0].toString()~")¹";
					assert(tpl.length==isConst.length);
					d=zip(isConst,iota(tpl.length).map!(i=>tpl[i])).map!(a=>(a[1].isTupleTy()&&a[1]!is unit?"("~(a[0]&&!a[1].impliesConst()?"const ":"")~a[1].toString()~")":addp(a[0],a[1]))).join(" × ");
					if(isSquare) d=del[0]~d~del[1];
				}else d=addp(isConst[0],dom,del);
			}else d=addp(isConst[0],dom,del);
			static if(language==dp) {
				if (!isDifferentiable) d = "nondiff " ~ d;
				d = (isParameterized ? (isInitialized ? "init" : "param") : "noparam") ~ " " ~ d;
			}
			static if(language==silq) auto arrow=(isClassical?"!":"")~"→";
			else enum arrow="→";
			r=d~" "~arrow~(annotation?to!string(annotation):"")~" "~c;
		}else{
			assert(names.length);
			string args;
			if(isTuple){
				args=zip(isConst,names,iota(tdom.length).map!(i=>tdom[i])).map!(x=>(x[0]?"const ":"")~x[1]~":"~x[2].toString()).join(",");
				if(nargs==1) args~=",";
			}else args=(isConst[0]&&!dom.impliesConst()?"const ":"")~names[0]~":"~dom.toString();
			static if(language==silq) auto pi=(isClassical?"!":"")~"∏";
			else enum pi="Π";
			r=pi~del[0]~args~del[1]~annotationToString(annotation)~". "~c;
		}
		return r;
	}
	@property size_t nargs(){
		if(isTuple) return tdom.length;
		return 1;
	}
	Expression argTy(size_t i)in{assert(i<nargs);}body{
		if(isTuple) return tdom[i];
		return dom;
	}
	override int freeVarsImpl(scope int delegate(string) dg){
		if(auto r=dom.freeVarsImpl(dg)) return r;
		return cod.freeVarsImpl(v=>names.canFind(v)?0:dg(v));
	}
	private ProductTy relabel(string oname,string nname)in{
		assert(names.canFind(oname));
		assert(!hasFreeVar(nname));
		assert(!names.canFind(nname));
	}out(r){
		if(oname!=""&&oname!=nname){
			assert(r.names.canFind(nname));
			assert(!r.names.canFind(oname));
		}
	}body{
		if(oname==""||oname==nname) return this;
		import std.algorithm;
		auto i=names.countUntil(oname);
		assert(i!=-1);
		auto nnames=names.dup;
		nnames[i]=nname;
		auto nvar=varTy(nname,argTy(i));
		static if (language==dp) return productTy(isConst,nnames,dom,cod.substitute(oname,nvar),isSquare,isTuple,
						 annotation,isClassical_, isParameterized, isInitialized, isDifferentiable, isPullbackOf);
		else return productTy(isConst,nnames,dom,cod.substitute(oname,nvar),isSquare,isTuple,annotation,isClassical_);
	}
	private ProductTy relabelAway(string oname)in{
		assert(names.canFind(oname));
	}out(r){
		if(oname!="") assert(!r.names.canFind(oname));
	}body{
		if(oname=="") return this;
		auto nname=oname;
		while(names.canFind(nname)||hasFreeVar(nname)) nname~="'";
		return relabel(oname,nname);
	}
	private string freshName(string base,Expression block){
		auto nn=base;
		while(hasFreeVar(nn)||block.hasFreeVar(nn)) nn~="'";
		return nn;
	}
	private string[] freshNames(Expression block){
		auto nnames=names.dup;
		foreach(i,ref nn;nnames)
			while(hasFreeVar(nn)||block.hasFreeVar(nn)||nnames[0..i].canFind(nn)) nn~="'";
		return nnames;
	}
	private ProductTy relabelAll(string[] nnames)out(r){
		assert(nnames.length==names.length);
		foreach(n;nnames) assert(!hasFreeVar(n));
	}body{
		Expression[string] subst;
		foreach(i;0..names.length) subst[names[i]]=varTy(nnames[i],argTy(i));
		static if(language==dp) return productTy(isConst,nnames,dom,cod.substitute(subst),isSquare,isTuple,
						 annotation,isClassical_,isParameterized,isInitialized,isDifferentiable,isPullbackOf);
		else return productTy(isConst,nnames,dom,cod.substitute(subst),isSquare,isTuple,annotation,isClassical_);
	}
	override ProductTy substituteImpl(Expression[string] subst){
		foreach(n;names){
			if(n=="") continue;
			bool ok=true;
			foreach(k,v;subst) if(v.hasFreeVar(n)) ok=false;
			if(ok) continue;
			auto r=cast(ProductTy)relabelAway(n).substitute(subst);
			assert(!!r);
			return r;
		}
		auto ndom=dom.substitute(subst);
		auto nsubst=subst.dup;
		foreach(n;names) nsubst.remove(n);
		auto ncod=cod.substitute(nsubst);
		auto nIsConst=isConst;
		if(isTuple){
			auto tpl=ndom.isTupleTy();
			assert(tpl&&tpl.length==nIsConst.length);
			if(iota(nIsConst.length).any!(i=>!nIsConst[i]&&tpl[i].impliesConst)){
				nIsConst=nIsConst.dup;
				foreach(i;0..nIsConst.length) if(!nIsConst[i]&&tpl[i].impliesConst) nIsConst[i]=true;
			}
		}else{
			assert(nIsConst.length==1);
			if(ndom.impliesConst&&!nIsConst[0])
				nIsConst=[true];
		}
		static if (language==dp) return productTy(nIsConst,names,ndom,ncod,isSquare,isTuple,
						 annotation,isClassical_, isParameterized, isInitialized, isDifferentiable, isPullbackOf);
		else return productTy(nIsConst,names,ndom,ncod,isSquare,isTuple,annotation,isClassical_);
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto r=cast(ProductTy)rhs; // TODO: get rid of duplication (same code in opEquals)
		if(!r) return false;
		if(isTuple&&!r.dom.isTupleTy()) return false;
		r=r.setTuple(isTuple);
		if(!r) return false;
		if(isConst.length!=r.isConst.length) return false;
		if(isSquare!=r.isSquare||annotation>r.annotation||
		   isClassical_!=r.isClassical_||nargs!=r.nargs)
			return false;
		r=r.relabelAll(freshNames(r));
		Expression[string] nsubst;
		foreach(k,v;subst) if(!names.canFind(k)) nsubst[k]=v;
		auto res=dom.unify(r.dom,nsubst,!meet)&&cod.unify(r.cod,nsubst,meet);
		foreach(k,v;nsubst) subst[k]=v;
		return res;
	}
	Expression tryMatch(Expression arg,out Expression garg)in{assert(isSquare&&cast(ProductTy)cod);}body{
		auto cod=cast(ProductTy)this.cod;
		assert(!!cod);
		auto nnames=freshNames(arg);
		if(nnames!=names) return relabelAll(nnames).tryMatch(arg,garg);
		Expression[] atys;
		auto tpl=arg.type.isTupleTy();
		if(cod.isTuple&&tpl){
			atys=iota(tpl.length).map!(i=>tpl[i]).array;
			if(atys.length!=cod.nargs) return null;
		}else atys=[arg.type];
		Expression[string] subst;
		foreach(i,n;names) subst[n]=null;
		foreach(i,aty;atys){
			if(i>=cod.nargs) continue;
			if(!cod.argTy(i).unify(aty,subst,false))
				return null;
		}
		auto gargs=new Expression[](names.length);
		foreach(i,n;names){
			if(!subst[n]) return null;
			gargs[i]=subst[n];
		}
		if(!isTuple) assert(gargs.length==1);
		if(isTuple){
			auto tgarg=new TupleExp(gargs);
			tgarg.type=tupleTy(gargs.map!(garg=>garg.type).array);
			tgarg.sstate=SemState.completed;
			garg=tgarg;
		}else garg=gargs[0];
		cod=cast(ProductTy)tryApply(garg,true);
		if(!cod) return null;
		return cod.tryApply(arg,false);
	}
	Expression tryApply(Expression arg,bool isSquare){
		if(isSquare != this.isSquare) return null;
		if(!isSubtype(arg.type,dom)) return null;
		Expression[string] subst;
		if(isTuple){
			auto tdom=dom.isTupleTy();
			assert(!!tdom);
			foreach(i,n;names){
				import ast.lexer;
				auto exp=new IndexExp(arg,[LiteralExp.makeInteger(i)],false);
				exp.type=tdom[i];
				exp.sstate=SemState.completed;
				subst[n]=exp.eval();
				subst["#"~to!string(i)]=subst[n];
			}
		}else{
			assert(names.length==1);
			subst[names[0]]=arg;
			subst["#0"]=arg;
		}
		return cod.substitute(subst);
	}
	override bool opEquals(Object o){
		auto r=cast(ProductTy)o;
		if(!r) return false;
		if(isTuple&&!r.dom.isTupleTy()) return false;
		r=r.setTuple(isTuple);
		if(!r) return false;
		assert(isTuple==r.isTuple);
		if(isConst!=r.isConst||isSquare!=r.isSquare||annotation!=r.annotation||
		   isClassical_!=r.isClassical_||nargs!=r.nargs)
			return false;
		return this.isSubtypeImpl(r)&&r.isSubtypeImpl(this);
	}
	override bool isSubtypeImpl(Expression rhs){
		auto r=cast(ProductTy)rhs;
		if(!r) return false;
		if(isTuple&&!r.dom.isTupleTy()) return false;
		r=r.setTuple(isTuple);
		if(!r) return false;
		if(isConst!=r.isConst||isSquare!=r.isSquare||nargs!=r.nargs) {
			return false;
		}
		static if(language==dp) {
			if (!isDifferentiable&&r.isDifferentiable) return false;
			
			bool lRequiresInitialization = isParameterized&&!isInitialized;
			bool rRequiresInitialization = r.isParameterized&&!r.isInitialized;
			if (lRequiresInitialization!=rRequiresInitialization) return false;

			bool lHasParams = isParameterized&&isInitialized;
			bool rHasParams = r.isParameterized&&r.isInitialized;
			if (rHasParams&&!lHasParams) return false;
		}
		if(annotation<r.annotation||!isClassical&&r.isClassical) return false;
		auto name=freshName("`x",r);
		auto vars=varTy(name,r.dom);
		auto lCod=tryApply(vars,isSquare);
		auto rCod=r.tryApply(vars,isSquare);
		if(!lCod) return false;
		assert(!!rCod);
		return isSubtype(lCod,rCod);
	}
	override Expression combineTypesImpl(Expression rhs,bool meet){
		auto r=cast(ProductTy)rhs;
		if(!r) return null;
		auto nannotation=meet?min(annotation,r.annotation):max(annotation,r.annotation);
		auto nisClassical=meet?isClassical||r.isClassical:isClassical&&r.isClassical;
		auto ndom=combineTypes(dom,r.dom,!meet);
		if(!ndom) return null;
		auto tpl=isTuple?ndom.isTupleTy():null;
		if(isTuple!=r.isTuple||isTuple&&!tpl||isTuple&&names!=r.names){
			auto nl=setTuple(false);
			auto nr=r.setTuple(false);
			if(!nl||!nr) return null;
			return combineTypes(nl,nr,meet);
		}
		if(isConst!=r.isConst||isSquare!=r.isSquare||nargs!=r.nargs)
			return null;
		static if(language==dp) {
			auto combinationIsDifferentiable = isDifferentiable&&r.isDifferentiable;
			if (meet&&isDifferentiable!=r.isDifferentiable) return null;
			if (isParameterized!=r.isParameterized) return null;
			if (isInitialized!=r.isInitialized) return null;
		}
		if(isTuple){
			assert(names==r.names);
			assert(!!tpl);
			if(tpl.length!=names.length) return null;
			auto vars=new TupleExp(iota(names.length).map!(i=>cast(Expression)varTy(names[i],tpl[i])).array);
			vars.type=ndom;
			vars.sstate=SemState.completed;
			auto lCod=tryApply(vars,isSquare);
			auto rCod=r.tryApply(vars,isSquare);
			assert(lCod&&rCod);
			auto ncod=combineTypes(lCod,rCod,meet);
			static if(language==dp) return productTy(isConst,names,ndom,ncod,isSquare,isTuple,
				nannotation,nisClassical, isParameterized, isInitialized, combinationIsDifferentiable, isPullbackOf);
			else return productTy(isConst,names,ndom,ncod,isSquare,isTuple,nannotation,nisClassical);
		}else{
			auto name=names[0]==r.names[0]?names[0]:freshName("x",r);
			auto var=varTy(name,ndom);
			auto lCod=tryApply(var,isSquare);
			auto rCod=r.tryApply(var,isSquare);
			assert(lCod&&rCod);
			auto ncod=combineTypes(lCod,rCod,meet);
			static if(language==dp) return productTy(isConst,names,ndom,ncod,isSquare,isTuple,
				nannotation,nisClassical,isParameterized, isInitialized, combinationIsDifferentiable, isPullbackOf);
			else return productTy(isConst,names,ndom,ncod,isSquare,isTuple,
				nannotation,nisClassical);
		}
	}
	private ProductTy setTuple(bool tuple)in{
		assert(!tuple||dom.isTupleTy());
	}body{
		if(tuple==isTuple) return this;
		string[] nnames;
		bool[] nIsConst;
		if(tuple){
			auto tpl=dom.isTupleTy();
			assert(!!tpl);
			nnames=iota(tpl.length).map!(i=>"x"~lowNum(i)).array;
			assert(isConst.length==1);
			nIsConst=isConst[0].repeat(tpl.length).array;
		}else{
			auto isConst2=iota(nargs).filter!(i=>!argTy(i).impliesConst()).map!(i=>isConst[i]);
			if(!isConst2.empty&&!isConst2.all!(x=>x==isConst2.front))
				return null;
			nnames=["x"];
			nIsConst=[isConst2.empty?true:isConst2.front];
		}
		foreach(i,ref nn;nnames) while(hasFreeVar(nn)) nn~="'";
		static if(language==dp) return productTy(nIsConst,nnames,dom,cod,isSquare,tuple,
			annotation,isClassical_, isParameterized, isInitialized, isDifferentiable, isPullbackOf);
		else return productTy(nIsConst,nnames,dom,cod,isSquare,tuple,
			annotation,isClassical_);
	}
	override bool isClassical(){
		return isClassical_;
	}
	override bool hasClassicalComponent(){
		return true; // code is classical
	}
	override ProductTy getClassical(){
		static if(language==silq) return classicalTy;
		else return this;
	}
	override int componentsImpl(scope int delegate(Expression) e){
		return 0; // TODO: ok?
	}
	override Expression evalImpl(Expression ntype){
		assert(ntype.isTypeTy);
		auto ndom=dom.eval(),ncod=cod.eval();
		if(ndom==dom&&ncod==cod) return this;
		static if(language==dp) return productTy(isConst,names,ndom,ncod,isSquare,isTuple,
			annotation,isClassical_, isParameterized, isInitialized, isDifferentiable, isPullbackOf);
		else return productTy(isConst,names,ndom,ncod,isSquare,isTuple,annotation,isClassical_);
	}

	override @property bool isManifoldType() { return isParameterized&&isInitialized; }

	override Expression tangentVecTy(Scope sc) {
		return tangentVectorTy(parameterSetTopTy(sc), sc);
	}
}

static if (language==dp) {
	ProductTy productTy(bool[] isConst,string[] names,
						Expression dom,Expression cod,
						bool isSquare,bool isTuple,
						Annotation annotation,bool isClassical,
						bool isParameterized=false, bool isInitialized=false, bool isDifferentiable=false,
						ProductTy primalTy=null)in{
		assert(dom&&cod);
		if(isTuple){
			auto tdom=dom.isTupleTy();
			assert(tdom&&names.length==tdom.length&&isConst.length==tdom.length);
		}else assert(names.length==1&&isConst.length==1);
	}body{
		return memoize!((bool[] isConst,string[] names,
						 Expression dom,Expression cod,
						 bool isSquare,bool isTuple,
						 Annotation annotation,bool isClassical,
						 bool isParameterized, bool isInitialized, bool isDifferentiable, ProductTy primalTy)
			=>new ProductTy(isConst,names,dom,cod,isSquare,isTuple,annotation,isClassical, isParameterized, isInitialized, isDifferentiable, primalTy))
				(isConst,names,dom,cod,isSquare,isTuple,annotation,isClassical, isParameterized, isInitialized, isDifferentiable, primalTy);
	}
} else {
	ProductTy productTy(bool[] isConst,string[] names,Expression dom,Expression cod,bool isSquare,bool isTuple,Annotation annotation,bool isClassical)in{
		assert(dom&&cod);
		if(isTuple){
			auto tdom=dom.isTupleTy();
			assert(tdom&&names.length==tdom.length&&isConst.length==tdom.length);
		}else assert(names.length==1&&isConst.length==1);
	}body{
		return memoize!((bool[] isConst,string[] names,Expression dom,Expression cod,bool isSquare,bool isTuple,Annotation annotation,bool isClassical)=>new ProductTy(isConst,names,dom,cod,isSquare,isTuple,annotation,isClassical))(isConst,names,dom,cod,isSquare,isTuple,annotation,isClassical);
	}
}


static if (language==dp) {
	FunTy funTy(bool[] isConst,Expression dom,Expression cod,bool isSquare,bool isTuple,Annotation annotation,bool isClassical,
		bool isParameterized=false, bool isInitialized=false, bool isDifferentiable=false)in{
	assert(dom&&cod);
	if(isTuple){
		auto tdom=dom.isTupleTy();
		assert(isConst.length==tdom.length);
	}else assert(isConst.length==1);
}body{
	auto nargs=1+[].length;
	if(isTuple) if(auto tpl=dom.isTupleTy()) nargs=tpl.length;
	return productTy(isConst,iota(nargs).map!(_=>"").array,dom,cod,isSquare,isTuple,annotation,isClassical,
		isParameterized, isInitialized, isDifferentiable);
}
} else {
	FunTy funTy(bool[] isConst,Expression dom,Expression cod,bool isSquare,bool isTuple,Annotation annotation,bool isClassical)in{
	assert(dom&&cod);
	if(isTuple){
		auto tdom=dom.isTupleTy();
		assert(isConst.length==tdom.length);
	}else assert(isConst.length==1);
}body{
	auto nargs=1+[].length;
	if(isTuple) if(auto tpl=dom.isTupleTy()) nargs=tpl.length;
	return productTy(isConst,iota(nargs).map!(_=>"").array,dom,cod,isSquare,isTuple,annotation,isClassical);
}
}


alias FunTy=ProductTy;

FunTy funTy(Expression dom,Expression cod,bool isSquare,bool isTuple,Annotation annotation,bool isClassical)in{
	assert(dom&&cod);
}body{
	auto nargs=1+[].length;
	if(isTuple) if(auto tpl=dom.isTupleTy()) nargs=tpl.length;
	return funTy(false.repeat(nargs).array,dom,cod,isSquare,isTuple,annotation,isClassical);
}

FunTy funTy(Expression dom,Expression cod,bool isSquare,bool isTuple,bool isClassical)in{
	assert(dom&&cod);
}body{
	return funTy(dom,cod,isSquare,isTuple,Annotation.qfree,isClassical);
}

Identifier varTy(string name,Expression type,bool classical=false){
	return memoize!((string name,Expression type,bool classical){
		auto r=new Identifier(name);
		static if(language==silq) r.classical=classical;
		r.type=type;
		r.sstate=SemState.completed;
		return r;
	})(name,type,classical);
}

struct FreeIdentifiers{
	Expression self;
	int opApply(scope int delegate(Identifier) dg){
		int rec(Expression e){
			if(auto id=cast(Identifier)e) if(auto r=dg(id)) return r;
			if(auto pt=cast(ProductTy)e){
				foreach(id;pt.dom.freeIdentifiers)
					if(auto r=dg(id)) return r;
				foreach(id;pt.cod.freeIdentifiers){
					if(pt.names.canFind(id.name)) continue;
					if(auto r=dg(id)) return r;
				}
			}
			// TODO: LambdaExp
			foreach(x;e.components)
				if(auto r=rec(x))
					return r;
			return 0;
		}
		return rec(self);
	}
}
auto freeIdentifiers(Expression self){
	return FreeIdentifiers(self);
}
bool hasFreeIdentifier(Expression self,string name){
	foreach(id;self.freeIdentifiers) if(id.name==name) return true;
	return false;
}

// metatype with additional constraint on types having manifold capabilities
class ManifoldTypeTy: Type{
	this(){ this.type=this; super(); }
	override ManifoldTypeTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		return "manifold *";
	}
	override bool opEquals(Object o){
		return !!cast(TypeTy)o;
	}
	override bool isClassical(){
		return true; // quantum superposition of multiple types not allowed
	}
	override bool hasClassicalComponent(){
		return true;
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
	override bool isSubtypeImpl(Expression other) {
		return !!cast(TypeTy)other || !!cast(ManifoldTypeTy)other;
	}

	override Expression substituteImpl(Expression[string] subst) {
		return this;
	}
}

class TypeTy: Type{
	this(){ this.type=this; super(); }
	override TypeTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		return "*";
	}
	override bool opEquals(Object o){
		return !!cast(TypeTy)o;
	}
	override bool isClassical(){
		return true; // quantum superposition of multiple types not allowed
	}
	override bool hasClassicalComponent(){
		return true;
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
	override bool isSubtypeImpl(Expression other) {
		return !!cast(TypeTy)other;
	}

	override Expression substituteImpl(Expression[string] subst) {
		return this;
	}
}
TypeTy typeTy(){ 
	return memoize!(()=>new TypeTy())();
}

ManifoldTypeTy manifoldTypeTy(){
	return memoize!(()=>new ManifoldTypeTy())();
}

bool isTypeTy(Expression ty) {
	return ty==typeTy || ty==manifoldTypeTy;
}

class Manifold: Node {
	Type elementType;
	FunctionDef moveOpDef;
	FunctionDef tangentZeroDef;


	ManifoldDecl manifoldDecl;
 
	this(Type elementType, FunctionDef moveOpDef, Expression tangentVecTy, FunctionDef tangentZeroDef){ 
		this.elementType = elementType;
		this.moveOpDef = moveOpDef;
		this.tangentZeroDef = tangentZeroDef;
	}

	override @property string kind() {
		return "manifold implementation";
	}
	override string toString(){
		return "manifold " ~ elementType.toString();
	}
	override bool opEquals(Object o){
		Manifold otherManifold = cast(Manifold)o;
		if (!otherManifold) return false;
		return elementType == otherManifold.elementType &&
			moveOpDef == otherManifold.moveOpDef &&
			tangentZeroDef == otherManifold.tangentZeroDef &&
			manifoldDecl == otherManifold.manifoldDecl;
	}
}

class AliasTy : Type {
	string name;
	Expression target;
	enum classical=true;
	private this(string name, Expression target){
		this.name = name;
		this.target = target;
		this.type=typeTy;
		super();
	}
	override AliasTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		return "(" ~ name ~ " aka " ~ (target ? target.toString() : "null") ~ ")";
	}
	override bool opEquals(Object o){
		auto otherAlias = cast(AliasTy)o;
		if (!otherAlias) {
			return false;
		}
		return otherAlias.target == target &&
			otherAlias.name == name;
	}
	override bool isClassical(){
		return classical;
	}
	override bool hasClassicalComponent(){
		return true;
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}

	override bool isSubtypeImpl(Expression other) {
		return target.isSubtypeImpl(other);
	}

	override Expression combineTypesImpl(Expression r,bool meet){
		return target.combineTypesImpl(r, meet);
	}
}

AliasTy aliasTy(string name, Expression target){
	return memoize!((string name, Expression target)=>new AliasTy(name, target))(name, target);
}

T unalias(T)(T type) {
	if (auto aliasType = cast(AliasTy)type) {
		return cast(Type)aliasType.target;
	}
	return type;
}

class ParameterSetTy : Type {
	Expression target;
	Scope sc;

	@property isTypeBound() {
		return target.type.isTypeTy || isDataTyId(target);
	}

	@property isValueBound() {
		return !isTypeBound;
	}

	enum classical=true;
	private this(Expression target, Scope sc){
		super();
		
		this.target = target;
		this.sc = sc;

		this.type=typeTy;
	}
	override ParameterSetTy copyImpl(CopyArgs args){
		return new ParameterSetTy(target.copy(), sc);
	}
	override string toString(){
		if (target==anyTy) return "ϑ";
		return "ϑ[" ~ target.toString ~ "]";
	}
	override bool opEquals(Object o){
		auto otherParamSetTy = cast(ParameterSetTy)o;
		if (!otherParamSetTy) {
			return false;
		}
		return otherParamSetTy.target == target;
	}
	override bool isClassical(){
		return classical;
	}
	override bool hasClassicalComponent(){
		return true;
	}
	override Expression evalImpl(Expression ntype){ 
		return parameterSetTy(target.eval(), sc); 
	}
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(target);
	}

	override bool supportsBinaryOperatorImpl(string op, Expression operand) {
		if (op=="+") return cast(ParameterSetTy)operand !is null;
		return false;
	}

	override Expression combineTypesImpl(Expression rawRhs, bool meet) {
		if (auto rhs = cast(ParameterSetTy)rawRhs) {
			// TODO think about this (e.g. in addition all parameter names of lhs are maintained)
			return this;
			/*if (this.isTypeBound&&rhs.isTypeBound) { // combine type bounds
				if (auto combinedBound=this.target.combineTypesImpl(rhs, meet)) {
					return parameterSetTy(combinedBound, sc);
				}
			} else if (this.isValueBound&&rhs.isValueBound) {
				if (this.target==rhs.target) { // check for equal bounds
					return this;
				} else {
					// otherwise loosen type to combination of the value types of lhs and rhs
					if (auto combinedTypeBound=this.target.type.combineTypesImpl(rhs.target.type, meet)) {
						return parameterSetTy(combinedTypeBound, sc);
					}
				}
			} else if (this.isTypeBound&&rhs.isValueBound) {
				// lift both bounds to be type-bound
				auto otherTypeBound = rhs.target.type;
				return parameterSetTy(combineTypes(this.target, otherTypeBound, meet), sc);
			}*/
		}
		return super.combineTypesImpl(rawRhs, meet);
	}

	override bool isSubtypeImpl(Expression other) {
		if (ParameterSetTy otherTy = cast(ParameterSetTy)other) {
			if (auto otherTargetTy = typeOrDataType(otherTy.target)) {
				// if lhs parameter set is bound by value and rhs by type
				if (!this.target.type.isTypeTy && otherTargetTy.type.isTypeTy) {
					if (isSubtype(typeOrDataType(this.target.type), otherTargetTy)) {
						return true;
					}
				}
			}
		}

		return this == other;
	}

	override Expression substituteImpl(Expression[string] subst){ 
		auto targetSubst = target.substitute(subst);
		return parameterSetTy(targetSubst, sc);
	}

	override @property bool isManifoldType() { return true; }
	
	static ulong ctr = 0;

	override Expression tangentVecTy(Scope sc) {
		return tangentVectorTy(this, sc);
	}

	override Manifold manifoldImpl(Scope sc) {
		auto elementSpecificTangentVecTy = tangentVectorTy(new Identifier("this"), sc);

		FunctionDef tangentZeroDef = new FunctionDef(new Identifier("tangentZero"), [], 
			true, elementSpecificTangentVecTy, null); // body is null, tangentZero for parameter sets is an interpreter built-in

		tangentZeroDef.ftype = productTy([], [], unit, elementSpecificTangentVecTy, false, true, Annotation.none, true);
		tangentZeroDef.type = unit;
		tangentZeroDef.isParameterized = false;

		FunctionDef moveOpDef = new FunctionDef(new Identifier("move"), [
			new Parameter(false, new Identifier("along"), elementSpecificTangentVecTy)
		], false, unit, null); // body is null, moveOp is an interpreter built-in

		moveOpDef.ftype = productTy([true], ["along"], elementSpecificTangentVecTy, unit, false, false, Annotation.none, true);
		moveOpDef.type = unit;
		moveOpDef.isParameterized = false;

		return new Manifold(this, moveOpDef, tangentVectorTy(this, sc), tangentZeroDef);
	}

	override int freeVarsImpl(scope int delegate(string) dg){ 
		if (auto res=target.freeVarsImpl(dg)) return res;
		if (auto t=target.type) return t.freeVarsImpl(dg);
		return 0;
	}
}

ParameterSetTy parameterSetTy(Expression target, Scope sc){
	if (auto initializedFunctionExp = cast(InitializedFunctionExp)target) {
		auto parameterSetTy = cast(ParameterSetTy) initializedFunctionExp.p.type;
		assert(parameterSetTy, text("not of parameter set type ", initializedFunctionExp.p.type));
		return parameterSetTy;
	}
	return memoize!((Expression target, Scope sc)=>new ParameterSetTy(target, sc))(target, sc);
}
ParameterSetTy parameterSetTopTy(Scope sc){
	return parameterSetTy(anyTy, sc);
}

class TangentVectorTy : Type {
	// TangentVectorTy can be value-bound (a.tangentVector, bound is value expression) or 
	// type-bound (ℝ.tangentVector, bound is type expression)
	Expression bound;
	Scope sc;

	@property isTypeBound() {
		return bound.type.isTypeTy || isDataTyId(bound);
	}

	@property isValueBound() {
		return !isTypeBound;
	}

	this(Expression bound, Scope sc){
		this.bound = bound;
		this.type=typeTy;
		this.sc=sc;
		super();
	}

	/// returns the tangent vector type currently associated with the tangent type of bound
	private Expression resolve() {
		Type targetType;
		if (isTypeBound) {
			targetType = typeOrDataType(bound);
		} else {
			targetType = typeOrDataType(bound.type);
		}
		if (!targetType) return null;
		return targetType.tangentVecTy(sc);
	}

	override TangentVectorTy copyImpl(CopyArgs args){
		return tangentVectorTy(this.bound.copy(), sc);
	}
	override string toString(){
		if (isTypeBound) {
			return this.bound.toString~".tangentVector";
		} else {
			auto type = this.bound.type;
			string typeStr;
			if (!type) typeStr = "null";
			else typeStr = type.toString;
			return typeStr~".tangentVector["~bound.toString~"]";
		}
	}
	override bool opEquals(Object o){
		if (auto otherTangentVec = cast(TangentVectorTy)o) {
			return bound==otherTangentVec.bound;
		}
		return false;
	}
	override bool isClassical(){
		return true;
	}
	override bool hasClassicalComponent(){
		return true;
	}

	override Expression evalImpl(Expression ntype){ 
		TangentVectorTy res = tangentVectorTy(this.bound.eval(), sc);
		// check whether the evaluation resolves this tangent vector type 
		// to some concrete other type
		if (auto tv = res.resolve()) {
			if ((cast(TangentVectorTy)tv) is null) {
				return unalias(tv);
			}
		}
		// like isDataTyId, but handles direct cases of AggregateTy as well
		AggregateTy isDataTy(Expression e) {
			if (auto aggrTy=cast(AggregateTy)e) return aggrTy;
			else return isDataTyId(e);
		}
		if (auto aggrty = isDataTy(res.bound)) {
			return tangentVectorTy(parameterSetTy(aggrty, sc), sc);
		}
		if (auto aggrty = isDataTy(res.bound.type)) {
			return tangentVectorTy(parameterSetTy(res.bound, sc), sc);
		}
		return res;
	}
	// mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(this.bound);
	}

	override bool isSubtypeImpl(Expression other) {
		if (auto otherTangentVec = cast(TangentVectorTy)other) {
			if (isTypeBound&&otherTangentVec.isTypeBound) {
				return isSubtype(bound.eval(), otherTangentVec.bound.eval());
			} else if (isValueBound&&otherTangentVec.isTypeBound) {
				auto evaluatedBoundType = bound.eval().type;
				return isSubtype(evaluatedBoundType, otherTangentVec.bound.eval());
			} else if (isTypeBound&&otherTangentVec.isValueBound) {
				auto evaluatedBoundType = bound.eval().type;
				return isSubtype(evaluatedBoundType, otherTangentVec.bound.eval());
			} else { // both value-bound
				return bound.eval() == otherTangentVec.bound.eval();
			}
		}
		// otherwise, try to resolve tangent vector to concrete type
		if (auto tv = resolve()) {
			// value-bound: given bound:T, check T.tangentVector :- other
			// type-bound: given bound=T:*, check T.tangentVector :- other
			if (tv==this) 
				return this==other;
			return isSubtype(tv, other);
		}


		return super.isSubtypeImpl(other);
	}
	mixin VariableFree;
	override Expression combineTypesImpl(Expression r,bool meet){
		if (auto tv = resolve()) {			
			// value-bound: given bound:T, combine T.tangentVector + other
			// type-bound: given bound=T:*, combine T.tangentVector + other	
			return combineTypes(tv, r, meet);
		} else if (auto otherTangentVec = cast(TangentVectorTy)r) {
			// lift both bounds to type-bound tangent vector types
			auto typeBound = isTypeBound?bound:bound.type;
			auto otherTypeBound = otherTangentVec.isTypeBound?otherTangentVec.bound:otherTangentVec.bound.type;
			// combine type bounds
			auto combinedTypeBound = combineTypes(typeBound, otherTypeBound, meet);
			return tangentVectorTy(combinedTypeBound, sc);
		} else {
			return null;
		}
	}

	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		if (auto otherTangentVec = cast(TangentVectorTy)rhs) {
			return bound.unify(otherTangentVec.bound, subst, meet);
		} else {
			return false;
		}
	}
	override int freeVarsImpl(scope int delegate(string) dg){ 
		if (auto res=bound.freeVarsImpl(dg)) return res;
		if (auto t=bound.type) return t.freeVarsImpl(dg);
		return 0;
	}
	override Expression substituteImpl(Expression[string] subst){ 
		return tangentVectorTy(bound.substitute(subst), sc);
	}
	override bool supportsBinaryOperatorImpl(string op, Expression operand) {
		// point-wise addition 
		if (op=="+"&&isSubtype(operand, this)) return true;
		// scalar multiplication
		if (op=="·"&&isSubtype(operand, ℝ(true))) return true;
		
		// point-wise multiplication
		if (op=="·"&&isSubtype(operand, this)) return true;
		// point-wise division
		if (op=="/"&&isSubtype(operand, this)) return true;
		// scalar addition
		if (op=="+"&&isSubtype(operand, ℝ(true))) return true;
		// scalar division
		if (op=="/"&&isSubtype(operand, ℝ(true))) return true;
		
		return super.supportsBinaryOperatorImpl(op, operand);
	}
}

class ParameterSetTangentVectorTy: TangentVectorTy {
	this(Expression bound, Scope sc){
		super(bound, sc);
	}

	override string toString() {
		if (isTypeBound) {
			if (auto paramTy = cast(ParameterSetTy)bound) {
				if (!paramTy.target.type.isTypeTy&&cast(FunTy)paramTy.target.type is null) {
					auto paramTypeTy = parameterSetTy(paramTy.target.type, sc);
					auto paramSetHandle = new ParameterSetHandleExp(paramTy.target);
					return paramTypeTy.toString~".tangentVector["~paramSetHandle.toString~"]";
				}
			}
		}
		return super.toString();
	}

	override Expression combineTypesImpl(Expression r,bool meet){
		// parameter set addition
		if (auto otherParameterSetTangentVectorTy=cast(ParameterSetTangentVectorTy)r) {
			auto paramTy = cast(ParameterSetTy)bound;
			auto otherParamTy = cast(ParameterSetTy)otherParameterSetTangentVectorTy.bound;
			if (paramTy&&otherParamTy) {
				return tangentVectorTy(combineTypes(paramTy, otherParamTy, meet), sc);
			}
		}
		// scalar multiplication
		if (isSubtype(r, ℝ(true))) return this;

		return super.combineTypesImpl(r, meet);
	}
}

TangentVectorTy tangentVectorTy(Expression target, Scope sc) {
	// always use params[a] (ParameterSetTy) in place of a.params (ParameterSetHandleExp) in the type model
	if (auto parameterSetHandleExp = cast(ParameterSetHandleExp)target) {
		target = parameterSetTy(parameterSetHandleExp.target, sc);
	}
	if (auto paramTy=cast(ParameterSetTy)target.type) {
		// if target is of value-bound ParameterSetTy, use it as target instead
		if (paramTy.isValueBound) target = paramTy;
		// if target is value of ParameterSetTy
		else target = target.type;
	}
	return memoize!((Expression target, Scope sc){
		if (auto paramTy=cast(ParameterSetTy)target) return new ParameterSetTangentVectorTy(paramTy, sc);
		if (auto paramTy=cast(ParameterSetTy)target.type) return new ParameterSetTangentVectorTy(target, sc);
		return new TangentVectorTy(target, sc);
	})(target, sc);
}

/// unsafe dynamic type which can be cast to any other type and otherwise behaves like anyTy
class DynamicTy : AnyTy {
	private this(bool classical){
		super(classical);
	}
	override DynamicTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!dynamic":"dynamic";
		else return "dynamic";
	}
	override bool opEquals(Object o){
		return !!cast(DynamicTy)o;
	}
	override bool isClassical(){
		return classical;
	}
	override bool hasClassicalComponent(){
		return true;
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}

DynamicTy dynamicTy(bool classical=true){
	static if(language==silq) return memoize!((bool classical)=>new DynamicTy(classical))(classical);
	else return memoize!(()=>new DynamicTy(true));
}

/// nograd type represents the singular value (`nograd`) returned by a pullback for non-differentiable parameters
class NoGradTy : Type {
	private this(){}
	override NoGradTy copyImpl(CopyArgs args){
		return this;
	}
	override string toString(){
		static if(language==silq) return classical?"!nograd":"nograd";
		else return "nograd";
	}
	override bool opEquals(Object o){
		return !!cast(NoGradTy)o;
	}
	override bool isClassical(){
		return true;
	}
	override bool hasClassicalComponent(){
		return true;
	}
	override Expression evalImpl(Expression ntype){ return this; }
	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
}

NoGradTy noGradTy(){
	return memoize!(()=>new NoGradTy())();
}