// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.semantic_;
import astopt;

import std.array,std.algorithm,std.range,std.exception;
import std.format, std.conv, std.typecons:Q=Tuple,q=tuple;
import ast.lexer,ast.scope_,ast.expression,ast.type,ast.declaration,ast.error,ast.reverse,util;

alias CommaExp=BinaryExp!(Tok!",");
alias AssignExp=BinaryExp!(Tok!"←");
alias DefineExp=BinaryExp!(Tok!":=");
alias OrAssignExp=BinaryExp!(Tok!"||←");
alias AndAssignExp=BinaryExp!(Tok!"&&←");
alias AddAssignExp=BinaryExp!(Tok!"+←");
alias SubAssignExp=BinaryExp!(Tok!"-←");
alias MulAssignExp=BinaryExp!(Tok!"·←");
alias DivAssignExp=BinaryExp!(Tok!"/←");
alias IDivAssignExp=BinaryExp!(Tok!"div←");
alias ModAssignExp=BinaryExp!(Tok!"%←");
alias PowAssignExp=BinaryExp!(Tok!"^←");
alias CatAssignExp=BinaryExp!(Tok!"~←");
alias BitOrAssignExp=BinaryExp!(Tok!"∨←");
alias BitXorAssignExp=BinaryExp!(Tok!"⊕←");
alias BitAndAssignExp=BinaryExp!(Tok!"∧←");
alias AddExp=BinaryExp!(Tok!"+");
alias SubExp=BinaryExp!(Tok!"-");
alias NSubExp=BinaryExp!(Tok!"sub");
alias MulExp=BinaryExp!(Tok!"·");
alias DivExp=BinaryExp!(Tok!"/");
alias IDivExp=BinaryExp!(Tok!"div");
alias ModExp=BinaryExp!(Tok!"%");
alias PowExp=BinaryExp!(Tok!"^");
alias CatExp=BinaryExp!(Tok!"~");
alias BitOrExp=BinaryExp!(Tok!"∨");
alias BitXorExp=BinaryExp!(Tok!"⊕");
alias BitAndExp=BinaryExp!(Tok!"∧");
alias UMinusExp=UnaryExp!(Tok!"-");
alias UNotExp=UnaryExp!(Tok!"¬");
alias UBitNotExp=UnaryExp!(Tok!"~");
alias LtExp=BinaryExp!(Tok!"<");
alias LeExp=BinaryExp!(Tok!"≤");
alias GtExp=BinaryExp!(Tok!">");
alias GeExp=BinaryExp!(Tok!"≥");
alias EqExp=BinaryExp!(Tok!"=");
alias NeqExp=BinaryExp!(Tok!"≠");
alias OrExp=BinaryExp!(Tok!"||");
alias AndExp=BinaryExp!(Tok!"&&");
alias RangeExp=BinaryExp!(Tok!"..");

static if(language==dp) {
	alias NonDiffTypeExp=UnaryExp!(Tok!"nondiff");
	alias NoParamTypeExp=UnaryExp!(Tok!"noparam");
	alias GradExp=UnaryExp!(Tok!"grad");
	alias DefineIfFreshExp=BinaryExp!(Tok!"?=");
	alias UnparamExp=UnaryExp!(Tok!"unparam");
}

alias Exp=Expression;

void propErr(Expression e1,Expression e2){
	if(e1.sstate==SemState.error) e2.sstate=SemState.error;
}

DataScope isInDataScope(Scope sc){
	auto asc=cast(AggregateScope)sc;
	if(asc) return cast(DataScope)asc.parent;
	return null;
}

AggregateTy isDataTyId(Expression e){
	if(auto ce=cast(CallExp)e)
		return isDataTyId(ce.e);
	if(auto id=cast(Identifier)e)
		if(auto decl=cast(DatDecl)id.meaning)
			return decl.dtype;
	if(auto fe=cast(FieldExp)e)
		if(auto decl=cast(DatDecl)fe.f.meaning)
			return decl.dtype;
	return null;
}

void declareParameters(P)(Expression parent,bool isSquare,P[] params,Scope sc)if(is(P==Parameter)||is(P==DatParameter)){
	foreach(ref p;params){
		if(!p.dtype){ // !ℝ is the default parameter type for () and * is the default parameter type for []
			if(isSquare){
				auto id=New!Identifier("*");
				id.loc=p.loc;
				p.dtype=id;
			}else{
				auto id=New!Identifier(isSquare?"*":"ℝ");
				id.loc=p.loc;
				static if(language==silq){
					p.dtype=New!(UnaryExp!(Tok!"!"))(id);
					p.dtype.loc=p.loc;
				}else p.dtype=id;
			}
		}
		p=cast(P)varDeclSemantic(p,sc);
		assert(!!p);
		propErr(p,parent);
	}
}

VarDecl addVar(string name,Expression ty,Location loc,Scope sc){
	auto id=new Identifier(name);
	id.loc=loc;
	auto var=new VarDecl(id);
	var.loc=loc;
	var.vtype=ty;
	var=varDeclSemantic(var,sc);
	assert(!!var && var.sstate==SemState.completed);
	return var;
}

// generates a synthesized member-function for a DatDecl with parameters (initializes the parameters)
FunctionDef makeParameterInitializerFunction(ParamDefExp[] parameterDefinitions) {
	import std.algorithm.iteration : map;
	
	auto body_ = new CompoundExp(
		parameterDefinitions.map!((def){
			auto defineExp = cast(DefineExp)def.defineExp;
			assert(defineExp);
			auto originalLhs = defineExp.e1;
			auto rhs = defineExp.e2;

			Expression lhs;

			if (auto ident = cast(Identifier)originalLhs) {
				lhs = new FieldExp(new Identifier("this"), ident);
			} else if (auto typeAnno = cast(TypeAnnotationExp)originalLhs) {
				if (auto ident = cast(Identifier) typeAnno.e) {
					lhs = new FieldExp(new Identifier("this"), ident); 
				}
			}

			if (!lhs) {
				writeln("error: unhandled parameter definition left-hand side: ", originalLhs);
				assert(false);
			}
			lhs.loc = originalLhs.loc;
			auto memberDefineExp = cast(Expression)new AssignExp(lhs, rhs);
			memberDefineExp.loc = defineExp.loc;
			return memberDefineExp;
		}).array
	);
	
	return new FunctionDef(new Identifier(DatDecl.INIT_FUNCTION_NAME), [], true, null, body_);
}

Expression presemantic(Declaration expr,Scope sc){
	bool success=true; // dummy
	if(!expr.scope_) makeDeclaration(expr,success,sc);
	if(DatDecl dat=cast(DatDecl)expr){
		if(dat.dtype) return expr;
		auto dsc=new DataScope(sc,dat);
		assert(!dat.dscope_);
		dat.dscope_=dsc;
		dat.dtype=new AggregateTy(dat,!dat.isQuantum);
		// handle type parameters
		if(dat.hasParams) declareParameters(dat,true,dat.params,dsc); 
		if(!dat.body_.ascope_) dat.body_.ascope_=new AggregateScope(dat.dscope_);
		if(cast(NestedScope)sc) dat.context = addVar("`outer",contextTy(true),dat.loc,dsc);
		
		// handle parameter declarations (param fields)
		ParamDefExp[] parameterDefinitions;
		foreach(ref exp;dat.body_.s) { 
			if (auto paramDefExp = cast(ParamDefExp)exp) {
				parameterDefinitions ~= [paramDefExp];
			}
			exp=makeDeclaration(exp,success,dat.body_.ascope_);
		}
		if (parameterDefinitions.length > 0) {
			auto initFun = presemantic(makeParameterInitializerFunction(parameterDefinitions), dat.body_.ascope_);
			dat.body_.s ~= [initFun];
		}

		foreach(ref exp;dat.body_.s) if(auto decl=cast(Declaration)exp) exp=presemantic(decl,dat.body_.ascope_);
	}
	if(auto fd=cast(FunctionDef)expr){
		if(fd.fscope_) return fd;
		auto fsc=new FunctionScope(sc,fd);
		static if (language==dp) fsc.allowsParameterDefinitions = fd.isParameterized;
		fd.type=unit;
		fd.fscope_=fsc;

		static if (language==dp) {
			// manifold declarations may refer to manifold element type 
			// as 'this' in type expressions
			if (auto manifoldDecl=sc.getManifoldDecl()){
				Expression manifoldTy=manifoldDecl.typeName.copy();
				manifoldTy.loc=fd.loc;
				manifoldTy=typeSemantic(manifoldTy, sc);
				assert(!!manifoldTy);
				fd.thisVar=addVar("this", manifoldTy, fd.loc, fsc);
			}
			if (fd.isSquare) {
				fd.isParameterized=false;
			}
			// make sure the inner lambda expressions of pullback declarations
			// are marked as nondiff in the AST
			if (fd.isPullback) {
				auto nfd = getSquareLambdaDelegate(fd);
				while (!!nfd) {
					nfd.isParameterized = false;
					nfd.isDifferentiable = false;
					nfd = getSquareLambdaDelegate(nfd);
				}
			}
		}
		declareParameters(fd,fd.isSquare,fd.params,fsc); // parameter variables
		if(fd.rret){
			fd.ret=typeSemantic(fd.rret,fsc);
			if(!setFtype(fd)) fd.sstate=SemState.error;
			if(!fd.body_){
				switch(fd.getName){
					case "invQImpl":
						// capture c:
						auto id=new Identifier("c");
						id.loc=fd.loc;
						expressionSemantic(id,fsc,ConstResult.yes);
						break;
					default: break;
				}
				return expr;
			}
		}
		if(!fd.body_){
			sc.error("function without body should have a return type annotation",fd.loc);
			fd.sstate=SemState.error;
			return expr;
		}
		assert(!fd.body_.blscope_);
		fd.body_.blscope_=new BlockScope(fsc);
		if(auto dsc=isInDataScope(sc)){
			auto id=new Identifier(dsc.decl.name.name);
			id.loc=dsc.decl.loc;
			id.meaning=dsc.decl;
			id=cast(Identifier)expressionSemantic(id,sc,ConstResult.no);
			assert(!!id);
			Expression ctxty=id;
			if(dsc.decl.hasParams){
				auto args=dsc.decl.params.map!((p){
					auto id=new Identifier(p.name.name);
					id.meaning=p;
					auto r=expressionSemantic(id,sc,ConstResult.no);
					assert(r.sstate==SemState.completed);
					return r;
				}).array;
				assert(dsc.decl.isTuple||args.length==1);
				ctxty=callSemantic(new CallExp(ctxty,dsc.decl.isTuple?new TupleExp(args):args[0],true,false),sc,ConstResult.no);
				ctxty.sstate=SemState.completed;
				assert(ctxty.type.isTypeTy);
			}
			if(dsc.decl.name.name==fd.name.name){
				assert(!!fd.body_.blscope_);
				auto thisVar=addVar("this",ctxty,fd.loc,fd.body_.blscope_); // the 'this' variable
				fd.isConstructor=true;
				if(fd.rret){
					sc.error("constructor cannot have return type annotation",fd.loc);
					fd.sstate=SemState.error;
				}else{
					assert(dsc.decl.dtype);
					fd.ret=ctxty;
				}
				if(!fd.body_.s.length||!cast(ReturnExp)fd.body_.s[$-1]){
					auto thisid=new Identifier(thisVar.getName);
					thisid.loc=fd.loc;
					thisid.scope_=fd.body_.blscope_;
					thisid.meaning=thisVar;
					thisid.type=ctxty;
					thisid.sstate=SemState.completed;
					auto rete=new ReturnExp(thisid);
					rete.loc=thisid.loc;
					rete.sstate=SemState.completed;
					fd.body_.s~=rete;
				}
				if(dsc.decl.context){
					fd.context=dsc.decl.context; // TODO: ok?
					fd.contextVal=dsc.decl.context; // TODO: ok?
				}
				fd.thisVar=thisVar;
			}else{
				fd.contextVal=addVar("this",unit,fd.loc,fsc); // the 'this' value
				assert(!!fd.body_.blscope_);
				assert(fsc.allowMerge);
				fsc.allowMerge=false; // TODO: this is hacky
				fd.context=addVar("this",ctxty,fd.loc,fd.body_.blscope_);
				fsc.allowMerge=true;
				assert(fd.context.getName!=fd.contextVal.getName);
			}
			// member functions cannot be parameterized
			fd.isParameterized=false;
			assert(dsc.decl.dtype);
		}else if(auto nsc=cast(NestedScope)sc){
			fd.contextVal=addVar("`outer",contextTy(true),fd.loc,fsc); // TODO: replace contextTy by suitable record type; make name 'outer' available
			fd.context=fd.contextVal;
		}
	}
	static if (language==dp) if (auto maniDecl = cast(ManifoldDecl)expr) {
		return manifoldDeclPresemantic(maniDecl,sc);
	}
	return expr;
}

// returns the FunctionDef with the actual body of a 
// square (type parameterised) FunctionDef
FunctionDef getSquareLambdaDelegate(FunctionDef funDef) {
    if (funDef.body_ is null) return null;
    if (funDef.body_.s.length != 1) return null;
    auto returnExp = cast(ReturnExp)funDef.body_.s[0];
    if (!returnExp) return null;
    auto le = cast(LambdaExp)returnExp.e;
	if (!le) return null;
	return le.fd;
}

import std.typecons: tuple,Tuple;
static Tuple!(Expression[],TopScope)[string] modules;
TopScope prsc=null;
int importModule(string path,ErrorHandler err,out Expression[] exprs,out TopScope sc,Location loc=Location.init){
	if(path in modules){
		auto exprssc=modules[path];
		exprs=exprssc[0],sc=exprssc[1];
		if(!sc){
			if(loc.line) err.error("circular imports not supported",loc);
			else stderr.writeln("error: circular imports not supported");
			return 1;
		}
		return 0;
	}
	modules[path]=tuple(Expression[].init,TopScope.init);
	scope(success) modules[path]=tuple(exprs,sc);
	Expression[] prelude;
	import ast.parser;
	if(!prsc && path != preludePath())
		if(auto r=importModule(preludePath,err,prelude,prsc))
			return r;
	if(auto r=parseFile(getActualPath(path),err,exprs,loc))
		return r;
	sc=new TopScope(err);
	if(prsc) sc.import_(prsc);
	int nerr=err.nerrors;
	exprs=semantic(exprs,sc);
	if(nerr!=err.nerrors){
		if(loc.line) sc.error("errors in imported file",loc);
		return 1;
	}
	return 0;
}

bool isInPrelude(Declaration decl){
	auto ppath=preludePath();
	if(ppath !in modules) return false;
	auto psc=modules[ppath];
	return decl.scope_.isNestedIn(psc[1]);
}

Expression makeDeclaration(Expression expr,ref bool success,Scope sc, bool isParamDefinition = false){
	if(auto imp=cast(ImportExp)expr){
		imp.scope_ = sc;
		auto ctsc=cast(TopScope)sc;
		if(!ctsc){
			sc.error("nested imports not supported",imp.loc);
			imp.sstate=SemState.error;
			return imp;
		}
		foreach(p;imp.e){
			auto path = getActualPath(ImportExp.getPath(p));
			Expression[] exprs;
			TopScope tsc;
			if(importModule(path,sc.handler,exprs,tsc,imp.loc)){
				imp.sstate=SemState.error;
			}
			if(tsc) ctsc.import_(tsc);
		}
		if(imp.sstate!=SemState.error) imp.sstate=SemState.completed;
		return imp;
	}
	if(auto decl=cast(Declaration)expr){
		if(!decl.scope_)
			success&=sc.insert(decl);
		return decl;
	}
	if(auto ce=cast(CommaExp)expr){
		ce.e1=makeDeclaration(ce.e1,success,sc);
		propErr(ce.e1,ce);
		ce.e2=makeDeclaration(ce.e2,success,sc);
		propErr(ce.e2,ce);
		return ce;
	}
	if(auto be=cast(DefineExp)expr){
		VarDecl makeVar(Identifier id){
			auto nid=new Identifier(id.name);
			nid.loc=id.loc;
			auto vd=new VarDecl(nid);
			static if (language==dp) vd.isParamDefinition = isParamDefinition;
			vd.loc=id.loc;
			if(be.e2.sstate!=SemState.error||!sc.lookupHere(nid,false,Lookup.probing))
				success&=sc.insert(vd);
			id.name=vd.getName;
			id.scope_=sc;
			return vd;
		}
		static if (language==dp) {
			if (isParamDefinition && !sc.allowsParameterDefinitions) {
				sc.error("Can only declare parameters in parameterized functions or dat declarations.", be.loc);
				success=false;
				expr.sstate=SemState.error;
				return expr;
			}
		}
		if(auto id=cast(Identifier)be.e1){
			auto vd=makeVar(id);
			auto de=new SingleDefExp(vd,be);
			de.loc=be.loc;
			propErr(vd,de);
			return de;
		}else if(auto tpl=cast(TupleExp)be.e1){
			VarDecl[] vds;
			foreach(exp;tpl.e){
				if(auto idx=cast(IndexExp)exp) vds~=null; // TODO
				else if(auto id=cast(Identifier)exp) vds~=makeVar(id);
				else goto LnoIdTuple;
			}
			auto de=new MultiDefExp(vds,be);
			de.loc=be.loc;
			foreach(vd;vds) if(vd) propErr(vd,de);
			return de;
		}else if(cast(IndexExp)be.e1){
			auto de=new SingleDefExp(null,be);
			de.loc=be.loc;
			return de;
		}else LnoIdTuple:{
			sc.error("left-hand side of definition must be identifier or tuple of identifiers",be.e1.loc);
			success=false;
		}
		success&=expr.sstate==SemState.completed;
		return expr;
	}
	if(auto tae=cast(TypeAnnotationExp)expr){
		if(auto id=cast(Identifier)tae.e){
			auto vd=new VarDecl(id);
			vd.loc=tae.loc;
			vd.dtype=tae.t;
			static if (language==dp) vd.isParamDefinition = isParamDefinition;
			vd.vtype=typeSemantic(vd.dtype,sc);
			vd.loc=id.loc;
			success&=sc.insert(vd);
			id.name=vd.getName;
			id.scope_=sc;
			return vd;
		}
	}
	if (auto paramExp=cast(ParamDefExp)expr){
		auto defineExp = cast(DefineExp)paramExp.defineExp;
		assert(defineExp);
		auto paramDecl = makeDeclaration(defineExp.e1, success, sc, true);
		
		auto paramDeclAsVarDecl = cast(VarDecl)paramDecl;
		assert(paramDeclAsVarDecl, text("parameter definition of unsupported kind ", typeid(paramDecl)));
		paramDeclAsVarDecl.isParamDefinition = true;
		return paramDeclAsVarDecl;
	}
	if (auto fieldDeclExp = cast(DefExp)expr) {
		return fieldDeclExp;
	}
	if(expr.sstate!=SemState.error&&expr.loc.line!=0) {
		sc.error(text("not a declaration: ", expr.toString(), " ", typeid(expr)),expr.loc);
	}
	expr.sstate=SemState.error;
	success=false;
	return expr;
}

void checkNotLinear(Expression e,Scope sc){
	if(sc.allowsLinear()) return;
	if(auto decl=cast(Declaration)e){
		if(decl.isLinear()){
			sc.error(format("cannot make linear declaration '%s' at this location",e),e.loc);
			e.sstate=SemState.error;
		}
	}
}


Expression[] semantic(Expression[] exprs,Scope sc){
	bool success=true;
	foreach(ref expr;exprs) if(!cast(DefineExp)expr&&!cast(CommaExp)expr) expr=makeDeclaration(expr,success,sc); // TODO: get rid of special casing?
	/+foreach(ref expr;exprs){
	 if(auto decl=cast(Declaration)expr) expr=presemantic(decl,sc);
		if(cast(DefineExp)expr) expr=makeDeclaration(expr,success,sc);
	}+/
	foreach(ref expr;exprs){
		if(auto decl=cast(Declaration)expr) expr=presemantic(decl,sc);
		expr=toplevelSemantic(expr,sc);
		success&=expr.sstate==SemState.completed;
	}
	if(!sc.allowsLinear()){
		foreach(ref expr;exprs){
			checkNotLinear(expr,sc);
		}
	}
	return exprs;
}

Expression toplevelSemantic(Expression expr,Scope sc){
	if(expr.sstate==SemState.error) return expr;
	if(auto fd=cast(FunctionDef)expr) return functionDefSemantic(fd,sc);
	if(auto dd=cast(DatDecl)expr) return datDeclSemantic(dd,sc);
	if(cast(DefineExp)expr||cast(DefExp)expr) return defineOrAssignSemantic(expr,sc);
	if(auto ce=cast(CommaExp)expr) return expectDefineOrAssignSemantic(ce,sc);
	if(auto imp=cast(ImportExp)expr){
		assert(util.among(imp.sstate,SemState.error,SemState.completed));
		return imp;
	}
	static if (language==dp) if (auto maniDecl = cast(ManifoldDecl)expr) return manifoldDeclSemantic(maniDecl,sc);
	sc.error("not supported at toplevel",expr.loc);
	expr.sstate=SemState.error;
	return expr;
}

bool isBuiltIn(Identifier id){
	if(!id||id.meaning) return false;
	switch(id.name){
	case "π","pi":
	case "readCSV":
	static if(language==silq){
		case "quantumPrimitive","__show","__query":
			return true;
	}else static if(language==psi){
		case "Marginal","sampleFrom":
		case "Expectation":
			return true;
	} else static if(language==dp) {
		// no additional cases	
	} else static assert(0);
	case "*","𝟙","𝟚","B","𝔹","N","ℕ","Z","ℤ","Q","ℚ","R","ℝ","C","ℂ":
		return true;
	case "string", "any":
		return true;
	default: return false;
	}
}

Expression getDistribution(Location loc,Scope sc){
	return getPreludeSymbol("Distribution",loc,sc);
}

Expression distributionTy(Expression base,Scope sc){
	return typeSemantic(new CallExp(getDistribution(base.loc,sc),base,true,true),sc);
}

Expression builtIn(Identifier id,Scope sc){
	Expression t=null;
	switch(id.name){
	case "readCSV": t=funTy(stringTy(true),arrayTy(ℝ(true)),false,false,true); break;

	case "π","pi": t=ℝ(true); break;
	case "Marginal","sampleFrom","quantumPrimitive","__query","__show": t=unit; break; // those are actually magic polymorphic functions
	case "Expectation": t=funTy(ℝ(false),ℝ(false),false,false,true); break; // TODO: should be lifted
	case "*","𝟙","𝟚","B","𝔹","N","ℕ","Z","ℤ","Q","ℚ","R","ℝ","C","ℂ":
		id.type=typeTy;
		if(id.name=="*") return typeTy;
		if(id.name=="𝟙") return unit;
		if(id.name=="𝟚"||id.name=="B"||id.name=="𝔹") return Bool(false);
		if(id.name=="N"||id.name=="ℕ") return ℕt(false);
		if(id.name=="Z"||id.name=="ℤ") return ℤt(false);
		if(id.name=="Q"||id.name=="ℚ") return ℚt(false);
		if(id.name=="R"||id.name=="ℝ") return ℝ(false);
		if(id.name=="C"||id.name=="ℂ") return ℂ(false);
	case "string", "any":
		id.type=typeTy();
		if(id.name=="string") return stringTy(true);
		if (id.name=="any") return anyTy(true);
	static if(language==dp) 
	case "manifold": {
		id.type=typeTy;
		return manifoldTypeTy();
	}
	case "ϑ", "params": {
		id.type=typeTy;
		return parameterSetTopTy(sc);
	}
	case "nograd": {
		id.type=typeTy;
		return new NoGradExp();
	}
	case "dynamic": {
		id.type=typeTy;
		return dynamicTy(true);
	}
	default: return null;
	}
	id.type=t;
	id.sstate=SemState.completed;
	return id;
}

bool isBuiltIn(FieldExp fe)in{
	assert(fe.e.sstate==SemState.completed);
}body{
	if(fe.f.meaning) return false;
	if(auto at=cast(ArrayTy)fe.e.type){
		if(fe.f.name=="length"){
			return true;
		}
	}
	return false;
}

Expression builtIn(FieldExp fe,Scope sc)in{
	assert(fe.e.sstate==SemState.completed);
}body{
	if(fe.f.meaning) return null;
	if(auto at=cast(ArrayTy)fe.e.type){
		if(fe.f.name=="length"){
			fe.type=ℕt(true); // no superpositions over arrays with different lengths
			fe.f.sstate=SemState.completed;
			return fe;
		}else return null;
	}
	return null;
}

bool isFieldDecl(Expression e){
	if(cast(VarDecl)e) return true;
	if(auto tae=cast(TypeAnnotationExp)e)
		if(auto id=cast(Identifier)tae.e)
			return true;
	return false;
}

Expression fieldDeclSemantic(Expression e,Scope sc)in{
	assert(isFieldDecl(e));
}body{
	e.sstate=SemState.completed;
	return e;
}

Expression expectFieldDeclSemantic(Expression e,Scope sc){
	if(auto ce=cast(CommaExp)e){
		ce.e1=expectFieldDeclSemantic(ce.e1,sc);
		ce.e2=expectFieldDeclSemantic(ce.e2,sc);
		propErr(ce.e1,ce);
		propErr(ce.e2,ce);
		return ce;
	}
	if(isFieldDecl(e)) return fieldDeclSemantic(e,sc);
	sc.error("expected field declaration",e.loc);
	e.sstate=SemState.error;
	return e;
}

Expression nestedDeclSemantic(Expression e,Scope sc){
	if(auto fd=cast(FunctionDef)e)
		return functionDefSemantic(fd,sc);
	if(auto dd=cast(DatDecl)e)
		return datDeclSemantic(dd,sc);
	if(auto paramDef=cast(ParamDefExp)e)
		return paramDef;
	if(isFieldDecl(e)) 
		return fieldDeclSemantic(e,sc);
	if(auto ce=cast(CommaExp)e) 
		return expectFieldDeclSemantic(ce,sc);
	sc.error(text("not a declaration", " ", typeid(e)),e.loc, );
	e.sstate=SemState.error;
	return e;
}

CompoundDecl compoundDeclSemantic(CompoundDecl cd,Scope sc){
	auto asc=cd.ascope_;
	if(!asc) asc=new AggregateScope(sc);
	++asc.getDatDecl().semanticDepth;
	scope(exit) if(--asc.getDatDecl().semanticDepth==0&&!asc.close()) cd.sstate=SemState.error;
	cd.ascope_=asc;
	bool success=true; // dummy
	foreach(ref e;cd.s) e=makeDeclaration(e,success,asc);
	foreach(ref e;cd.s) if(auto decl=cast(Declaration)e) e=presemantic(decl,asc);
	foreach(ref e;cd.s){
		e=nestedDeclSemantic(e,asc);
		propErr(e,cd);
	}
	if(!sc.allowsLinear()){
		foreach(ref e;cd.s){
			checkNotLinear(e,sc);
			propErr(e,cd);
		}
	}
	cd.type=unit;
	return cd;
}

Expression statementSemantic(Expression e,Scope sc)in{
	assert(sc.allowsLinear());
}do{
	static if(language==silq){
		scope(exit){
			sc.pushConsumed();
			sc.resetConst();
		}
	}
	if(auto ce=cast(CallExp)e)
		return callSemantic(ce,sc,ConstResult.yes);
	if(auto ce=cast(CompoundExp)e){
		foreach(ref s;ce.s){
			s=statementSemantic(s,sc);
			propErr(s,ce);
		}
		return ce;
	}
	if(auto ite=cast(IteExp)e){
		ite.cond=conditionSemantic!true(ite.cond,sc);
		static if(language==silq){
			auto quantumControl=ite.cond.type!=Bool(true);
			auto restriction_=quantumControl?Annotation.mfree:Annotation.none;
		}else{
			enum quantumControl=false;
			enum restriction_=Annotation.none;
		}
		// initialize scopes, to allow captures to be inserted
		ite.then.blscope_=new BlockScope(sc,restriction_);
		if(!ite.othw){
			ite.othw=New!CompoundExp((Expression[]).init);
			ite.othw.loc=ite.loc;
		}
		ite.othw.blscope_=new BlockScope(sc,restriction_);
		ite.then=controlledCompoundExpSemantic(ite.then,sc,ite.cond,restriction_);
		ite.othw=controlledCompoundExpSemantic(ite.othw,sc,ite.cond,restriction_);
		propErr(ite.cond,ite);
		propErr(ite.then,ite);
		propErr(ite.othw,ite);
		NestedScope[] scs;
		if(!quantumControl){
			if(definitelyReturns(ite.then)) scs=[ite.othw.blscope_];
			else if(definitelyReturns(ite.othw)) scs=[ite.then.blscope_];
			else scs=[ite.then.blscope_,ite.othw.blscope_];
		}else scs=[ite.then.blscope_,ite.othw.blscope_];
		if(sc.merge(quantumControl,scs)){
			sc.note("consumed in one branch of if expression", ite.loc);
			ite.sstate=SemState.error;
		}
		ite.type=unit;
		return ite;
	}
	if(auto ret=cast(ReturnExp)e)
		return returnExpSemantic(ret,sc);
	if(auto fd=cast(FunctionDef)e)
		return functionDefSemantic(fd,sc);
	if(auto dd=cast(DatDecl)e)
		return datDeclSemantic(dd,sc);
	if(auto ce=cast(CommaExp)e) return expectDefineOrAssignSemantic(ce,sc);
	if(isDefineOrAssign(e)) return defineOrAssignSemantic(e,sc);
	if(auto fe=cast(ForExp)e){
		assert(!fe.bdy.blscope_);
		fe.left=expressionSemantic(fe.left,sc,ConstResult.no);
		static if(language==silq) sc.pushConsumed();
		if(fe.left.sstate==SemState.completed && !isSubtype(fe.left.type, ℝ(true))){
			sc.error(format("lower bound for loop variable should be a classical number, not %s",fe.left.type),fe.left.loc);
			fe.sstate=SemState.error;
		}
		if(fe.step){
			fe.step=expressionSemantic(fe.step,sc,ConstResult.no);
			if(fe.step.sstate==SemState.completed && !isSubtype(fe.step.type, ℤt(true))){
				sc.error(format("step should be a classical integer, not %s",fe.step.type),fe.step.loc);
				fe.sstate=SemState.error;
			}
		}
		fe.right=expressionSemantic(fe.right,sc,ConstResult.no);
		static if(language==silq) sc.pushConsumed();
		if(fe.right.sstate==SemState.completed && !isSubtype(fe.right.type, ℝ(true))){
			sc.error(format("upper bound for loop variable should be a classical number, not %s",fe.right.type),fe.right.loc);
			fe.sstate=SemState.error;
		}
		auto fesc=fe.bdy.blscope_=new BlockScope(sc);
		auto vd=new VarDecl(fe.var);
		vd.vtype=fe.left.type && fe.right.type ? joinTypes(fe.left.type, fe.right.type) : ℤt(true);
		assert(fe.sstate==SemState.error||vd.vtype.isClassical());
		if(fe.sstate==SemState.error){
			if(!vd.vtype) vd.vtype=ℤt(true);
			vd.vtype=vd.vtype.getClassical();
		}
		vd.loc=fe.var.loc;
		if(vd.name.name!="_"&&!fesc.insert(vd))
			fe.sstate=SemState.error;
		fe.var.name=vd.getName;
		fe.fescope_=fesc;
		fe.loopVar=vd;
		fe.bdy=compoundExpSemantic(fe.bdy,sc);
		assert(!!fe.bdy);
		propErr(fe.left,fe);
		propErr(fe.right,fe);
		propErr(fe.bdy,fe);
		auto forgetScope=new BlockScope(sc);
		static if(language==silq){
			if(sc.merge(false,fesc,forgetScope)){
				sc.note("possibly consumed in for loop", fe.loc);
				fe.sstate=SemState.error;
			}
			if(forgetScope.forgottenVars.length){
				sc.error("variables potentially consumed multiple times in for loop",fe.loc);
				foreach(decl;forgetScope.forgottenVars)
					sc.note(format("variable '%s'",decl.name),decl.loc);
				fe.sstate=SemState.error;
			}
		}else sc.merge(false,fesc,forgetScope);
		fe.type=unit;
		return fe;
	}
	if(auto we=cast(WhileExp)e){
		we.cond=conditionSemantic(we.cond,sc);
		we.bdy=compoundExpSemantic(we.bdy,sc);
		propErr(we.cond,we);
		propErr(we.bdy,we);
		if(we.cond.sstate==SemState.completed){
			import ast.parser: parseExpression;
			auto ncode='\n'.repeat(we.cond.loc.line?we.cond.loc.line-1:0).to!string~we.cond.loc.rep~"\0\0\0\0";
			auto nsource=new Source(we.cond.loc.source.name,ncode);
			auto condDup=parseExpression(nsource,sc.handler); // TODO: this is an ugly hack, implement dup
			assert(!!condDup);
			condDup.loc=we.cond.loc;
			condDup=expressionSemantic(condDup,we.bdy.blscope_,ConstResult.no);
			static if(language==silq) we.bdy.blscope_.pushConsumed();
			if(condDup.sstate==SemState.error)
				sc.note("possibly consumed in while loop", we.loc);
			propErr(condDup,we);
		}
		auto forgetScope=new BlockScope(sc);
		static if(language==silq){
			if(sc.merge(false,we.bdy.blscope_,forgetScope)){
				sc.note("possibly consumed in while loop", we.loc);
				we.sstate=SemState.error;
			}
			if(forgetScope.forgottenVars.length){
				sc.error("variables potentially consumed multiple times in while loop", we.loc);
				foreach(decl;forgetScope.forgottenVars)
					sc.note(format("variable '%s'",decl.name),decl.loc);
				we.sstate=SemState.error;
			}
		}else sc.merge(false,we.bdy.blscope_,forgetScope);
		we.type=unit;
		return we;
	}
	if(auto re=cast(RepeatExp)e){
		re.num=expressionSemantic(re.num,sc,ConstResult.no);
		static if(language==silq) sc.pushConsumed();
		if(re.num.sstate==SemState.completed && !isSubtype(re.num.type, ℤt(true))){
			sc.error(format("number of iterations should be a classical integer, not %s",re.num.type),re.num.loc);
			re.sstate=SemState.error;
		}
		re.bdy=compoundExpSemantic(re.bdy,sc);
		propErr(re.num,re);
		propErr(re.bdy,re);
		auto forgetScope=new BlockScope(sc);
		static if(language==silq){
			if(sc.merge(false,re.bdy.blscope_,forgetScope)){
				sc.note("possibly consumed in repeat loop", re.loc);
				re.sstate=SemState.error;
			}
			if(forgetScope.forgottenVars.length){
				sc.error("variables potentially consumed multiple times in repeat loop", re.loc);
				foreach(decl;forgetScope.forgottenVars)
					sc.note(format("variable '%s'",decl.name),decl.loc);
				re.sstate=SemState.error;
			}
		}else sc.merge(false,re.bdy.blscope_,forgetScope);
		re.type=unit;
		return re;
	}
	if(auto oe=cast(ObserveExp)e){
		oe.e=conditionSemantic(oe.e,sc);
		propErr(oe.e,oe);
		oe.type=unit;
		return oe;
	}
	if(auto oe=cast(CObserveExp)e){ // TODO: get rid of cobserve!
		oe.var=expressionSemantic(oe.var,sc,ConstResult.no);
		oe.val=expressionSemantic(oe.val,sc,ConstResult.no);
		propErr(oe.var,oe);
		propErr(oe.val,oe);
		if(oe.sstate==SemState.error)
			return oe;
		if(!oe.var.type.isSubtype(ℝ(true)) || !oe.val.type.isSubtype(ℝ(true))){
			static if(language==silq)
				sc.error("both arguments to cobserve should be classical real numbers",oe.loc);
			else sc.error("both arguments to cobserve should be real numbers",oe.loc);
			oe.sstate=SemState.error;
		}
		oe.type=unit;
		return oe;
	}
	if(auto ae=cast(AssertExp)e){
		ae.e=conditionSemantic(ae.e,sc);
		propErr(ae.e,ae);
		ae.type=unit;
		return ae;
	}
	if(auto fe=cast(ForgetExp)e) return expressionSemantic(fe,sc,ConstResult.yes);

	static if (language==dp) {
		if (auto paramExp=cast(ParamDefExp)e){
			return paramDefSemantic(paramExp, sc);
		}
		if (auto defineIfFreshExp=cast(DefineIfFreshExp)e) {
			defineIfFreshExp.e1 = expressionSemantic(defineIfFreshExp.e1, sc, ConstResult.yes);
			defineIfFreshExp.e2 = expressionSemantic(defineIfFreshExp.e2, sc, ConstResult.yes);
			defineIfFreshExp.type = defineIfFreshExp.e2.type;
			// validate lhs
			auto indexLhs = cast(IndexExp)defineIfFreshExp.e1;
			if (!indexLhs) {
				sc.error("the operator ?= can only be used with an index access expression on the left-hand side",defineIfFreshExp.loc);
				defineIfFreshExp.sstate=SemState.error;
				return defineIfFreshExp;
			}
			if (!isSubtype(indexLhs.e.type, parameterSetTopTy(sc))&&
			    !isSubtype(indexLhs.e.type, tangentVectorTy(parameterSetTopTy(sc), sc))) {
				sc.error(format("the operator ?= can only be applied to index expressions on expressions of type %s, not %s", parameterSetTopTy(sc).toString, indexLhs.e.type.toString),defineIfFreshExp.loc);
				defineIfFreshExp.sstate=SemState.error;
				return defineIfFreshExp;
			}
			return defineIfFreshExp;
		}
		if (auto comment=cast(CommentExp)e) {
			comment.type=unit;
			return comment;
		}
	}

	sc.error(format("not supported at this location: %s", e.toString),e.loc);
	e.sstate=SemState.error;
	return e;
}

ParamDefExp paramDefSemantic(ParamDefExp paramExp, Scope sc) {
	auto singleDef = cast(SingleDefExp)statementSemantic(paramExp.defineExp, sc);
	if (!singleDef) {
		sc.error("parameter definition of unsupported kind", paramExp.loc);
		paramExp.sstate=SemState.error;
		return paramExp;
	}
	paramExp.defineExp = singleDef;
	// mark underlying VarDecl as parameter definition
	singleDef.decl.isParamDefinition = true;

	paramExp.context = paramExp.context?expressionSemantic(paramExp.context,sc,ConstResult.yes):null;

	if (paramExp.context !is null) {
		if (!(isSubtype(paramExp.context.type, ℕt) || isSubtype(paramExp.context.type, stringTy))) {
			sc.error(format("parameter context must be a natural number or string not %s", paramExp.context.type.toString()),paramExp.context.loc);
			paramExp.context.sstate=SemState.error;
		}
	}
	
	return paramExp;
}

CompoundExp controlledCompoundExpSemantic(CompoundExp ce,Scope sc,Expression control,Annotation restriction_)in{
	//assert(!ce.blscope_);
}do{
	static if(language==silq){
		if(control.type&&!control.type.isClassical()){
			if(!ce.blscope_) ce.blscope_=new BlockScope(sc,restriction_);
			if(control.isQfree()) ce.blscope_.addControlDependency(control.getDependency(ce.blscope_));
			else ce.blscope_.addControlDependency(Dependency(true,SetX!string.init));
		}
	}
	return compoundExpSemantic(ce,sc,restriction_);
}

CompoundExp compoundExpSemantic(CompoundExp ce,Scope sc,Annotation restriction_=Annotation.none){
	if(!ce.blscope_) ce.blscope_=new BlockScope(sc,restriction_);
	foreach(ref e;ce.s){
		e=statementSemantic(e,ce.blscope_);
		propErr(e,ce);
	}
	ce.type=unit;
	return ce;
}

VarDecl varDeclSemantic(VarDecl vd,Scope sc){
	bool success=true;
	if(!vd.scope_) makeDeclaration(vd,success,sc);
	vd.type=unit;
	if(!success) vd.sstate=SemState.error;
	if(!vd.vtype){
		assert(vd.dtype,text(vd));
		vd.vtype=typeSemantic(vd.dtype,sc);
	}
	if(auto prm=cast(Parameter)vd){
		if(vd.vtype&&vd.vtype.impliesConst())
			prm.isConst=true;
	}
	if(!vd.vtype) vd.sstate=SemState.error;
	if(vd.sstate!=SemState.error)
		vd.sstate=SemState.completed;
	return vd;
}

static if(language==silq){
Dependency getDependency(Expression e,Scope sc)in{
	assert(e.isQfree());
}do{
	auto result=Dependency(false);
	foreach(id;e.freeIdentifiers){
		if(id.type&&!id.type.isClassical){
			if(!sc.dependencyTracked(id)) // for variables captured in closure
				return Dependency(true);
			result.dependencies.insert(id.name);
			if(!id.constLookup){
				auto vd=cast(VarDecl)id.meaning;
				if(!vd||!vd.isConst) result.replace(id.name,sc.getDependency(id));
			}
		}
	}
	return result;
}

bool consumes(Expression e){
	if(!e.constLookup&&cast(Identifier)e&&(!e.type||!e.type.isClassical())) return true;
	foreach(c;e.components)
		if(c.consumes())
			return true;
	return false;
}
bool isLifted(Expression e,Scope sc){
	return e.isQfree()&&!e.getDependency(sc).isTop;
}
}

Expression defineSemantic(DefineExp be,Scope sc){
	static if(language==silq){
		if(auto tpl=cast(TupleExp)be.e1) if(tpl.e.count!(x=>!!cast(IndexExp)x)>1) return permuteSemantic(be,sc);
	}
	if(sc.allowsLinear){
		if(auto e=lowerDefine!false(be,sc)){
			if(e.sstate!=SemState.error)
				return statementSemantic(e,sc);
			return e;
		}
	}
	static if(language==psi){ // TODO: remove this?
		if(auto ce=cast(CallExp)be.e2){
			if(auto id=cast(Identifier)ce.e){
				if(id.name=="array" && !ce.isSquare){
					ce.arg=expressionSemantic(ce.arg,sc,ConstResult.yes);
					if(isSubtype(ce.arg.type,ℕt)){
						ce.e.type=funTy(ℝ,arrayTy(ℝ),false,false,Annotation.qfree,true);
						ce.e.sstate=SemState.completed;
					}
				}
			}
		}
	}
	bool success=true;
	auto e2orig=be.e2;
	auto tpl=cast(TupleExp)be.e1;
	static if(language==silq){
		bool semanticDone=false;
		if(tpl&&tpl.e.count!(x=>!!cast(IndexExp)x)==1){
			foreach(ref e;tpl.e){
				if(auto idx=cast(IndexExp)e){
					e=indexReplaceSemantic(idx,be.e2,be.loc,sc);
					propErr(e,be);
					semanticDone=true;
				}
			}
		}else if(auto idx=cast(IndexExp)be.e1){
			be.e1=indexReplaceSemantic(idx,be.e2,be.loc,sc);
			propErr(be.e1,be);
			semanticDone=true;
		}
	}else enum semanticDone=false;
	if(!semanticDone) be.e2=expressionSemantic(be.e2,sc,ConstResult.no);
	static if(language==silq){
		Dependency[] dependencies;
		if(be.e2.sstate==SemState.completed&&sc.getFunction()){
			bool ok=false;
			if(auto tpl1=cast(TupleExp)be.e1){
				dependencies.length=tpl1.length;
				if(auto tpl2=cast(TupleExp)be.e2){
					if(tpl1.length==tpl2.length){
						ok=true;
						foreach(i;0..tpl1.length)
							if(tpl2.e[i].isQfree())
								dependencies[i]=tpl2.e[i].getDependency(sc);
					}
				}
				if(!ok&&be.e2.isQfree()){
					auto dep=be.e2.getDependency(sc);
					foreach(i;0..tpl1.length)
						dependencies[i]=dep;
				}
			}else{
				dependencies.length=1;
				if(be.e2.isQfree()) dependencies[0]=be.e2.getDependency(sc);
			}
		}
	}
	auto de=cast(DefExp)makeDeclaration(be,success,sc);
	if(!de) be.sstate=SemState.error;
	assert(success && de && de.initializer is be || !de||de.sstate==SemState.error);
	auto tt=be.e2.type?be.e2.type.isTupleTy:null;
	if(be.e2.sstate==SemState.completed){
		if(tpl){
			if(tt){
				if(tpl.length!=tt.length){
					sc.error(text("inconsistent number of tuple entries for definition: ",tpl.length," vs. ",tt.length),de.loc);
					if(de){ de.setError(); be.sstate=SemState.error; }
				}
			}else if(!cast(ArrayTy)be.e2.type){
				sc.error(format("cannot unpack type %s as a tuple",be.e2.type),de.loc);
				if(de){ de.setError(); be.sstate=SemState.error; }
			}
		}
		if(de){
			if(de.sstate!=SemState.error){
				de.setType(be.e2.type);
				de.setInitializer();
				foreach(i,vd;de.decls){
					if(vd){
						auto nvd=varDeclSemantic(vd,sc);
						assert(nvd is vd);
					}else if(tpl&&tt){
						if(tpl.e.length>i&&tpl.e[i].type&&tt.length>i){
							if(!isSubtype(tt[i],tpl.e[i].type)){
								sc.error(format("cannot assign %s to %s",tt[i],tpl.e[i].type),tpl.e[i].loc);
								be.sstate=SemState.error;
							}
						}
					}else if(be.e1.type&&be.e2.type){
						if(!isSubtype(be.e2.type,be.e1.type)){
							sc.error(format("cannot assign %s to %s",be.e2.type,be.e1.type),be.loc);
							be.sstate=SemState.error;
						}
					}
				}
			}
			de.type=unit;
			static if(language==silq){
				auto decls=de.decls;
				if(de.sstate!=SemState.error&&sc.getFunction()&&decls.length==dependencies.length)
					foreach(i,vd;decls)
						if(vd&&vd.initializer&&vd.initializer.isQfree())
							sc.addDependency(vd,dependencies[i]);
			}
			propErr(be,de);
		}
		if(cast(TopScope)sc){
			if(!be.e2.isConstant() && !cast(PlaceholderExp)be.e2 && !be.e2.type.isTypeTy){
				sc.error("global constant initializer must be a constant",e2orig.loc);
				if(de){ de.setError(); be.sstate=SemState.error; }
			}
		}
	}else if(de) de.setError();
	auto r=de?de:be;
	if(be.e2.type && be.e2.type.sstate==SemState.completed){
		foreach(id;be.e2.type.freeIdentifiers){
			assert(!!id.meaning, text("identifier ", id, " does not have a .meaning"));
			typeConstBlock(id.meaning,be,sc);
		}
	}
	if(r.sstate!=SemState.error) r.sstate=SemState.completed;
	return r;
}

Identifier getIdFromIndex(IndexExp e){
	if(auto idx=cast(IndexExp)e.e) return getIdFromIndex(idx);
	return cast(Identifier)e.e;
}

static if(language==silq){
Expression indexReplaceSemantic(IndexExp theIndex,ref Expression rhs,Location loc,Scope sc){
	void consumeArray(IndexExp e){
		if(auto idx=cast(IndexExp)e.e) return consumeArray(idx);
		e.e=expressionSemantic(e.e,sc,ConstResult.no); // consume array
		e.e.constLookup=true;
	}
	consumeArray(theIndex);
	if(theIndex.e.type&&theIndex.e.type.isClassical()){
		sc.error(format("use assignment statement '%s = %s' to assign to classical array component",theIndex,rhs),loc);
		theIndex.sstate=SemState.error;
		return theIndex;
	}
	auto nIndex=cast(IndexExp)expressionSemantic(theIndex,sc,ConstResult.yes);
	assert(!!nIndex); // TODO: this might change
	theIndex=nIndex;
	Identifier id;
	bool check(IndexExp e){
		if(e&&(!e.a[0].isLifted(sc)||e.a[0].type&&!e.a[0].type.isClassical())){
			sc.error("index for component replacement must be 'lifted' and classical",e.a[0].loc);
			return false;
		}
		if(e) if(auto idx=cast(IndexExp)e.e) return check(idx);
		id=e&&e.e&&e.e.sstate==SemState.completed?cast(Identifier)e.e:null;
		if(e&&!checkAssignable(id?id.meaning:null,theIndex.e.loc,sc,true)){
			id=null;
			return false;
		}
		return true;
	}
	if(!check(theIndex)) theIndex.sstate=SemState.error;
	assert(!sc.indexToReplace);
	if(theIndex.sstate!=SemState.error) sc.indexToReplace=theIndex;
	rhs=expressionSemantic(rhs,sc,ConstResult.no);
	if(sc.indexToReplace){
		sc.error("reassigned component must be consumed in right-hand side", theIndex.loc);
		theIndex.sstate=SemState.error;
	}
	if(id&&id.type) addVar(id.name,id.type,loc,sc);
	if(theIndex.sstate!=SemState.error) theIndex.sstate=SemState.completed;
	return theIndex;
}

Expression permuteSemantic(DefineExp be,Scope sc)in{ // TODO: generalize defineSemantic to cover this
	auto tpl=cast(TupleExp)be.e1;
	assert(tpl&&tpl.e.any!(x=>!!cast(IndexExp)x));
}do{
	be.e1=expressionSemantic(be.e1,sc,ConstResult.yes); // TODO: this is a hack
	propErr(be.e1,be);
	be.e2=expressionSemantic(be.e2,sc,ConstResult.yes);
	propErr(be.e2,be);
	if(be.e1.type&&be.e1.type.isClassical()){
		sc.error(format("use assignment statement '%s = %s' to assign to classical array components",be.e1,be.e2),be.loc);
		be.sstate=SemState.error;
		return be;
	}
	auto tpl1=cast(TupleExp)be.e1, tpl2=cast(TupleExp)be.e2;
	if(!tpl1||!tpl2||tpl1.e.length!=2||tpl2.e.length!=2||tpl1.e[0]!=tpl2.e[1]||tpl1.e[1]!=tpl2.e[0]){
		sc.error("only swapping supported in permute statement", be.loc);
		be.sstate=SemState.error;
		return be;
	}
	be.isSwap=true;
	if(!chain(tpl1.e,tpl2.e).all!(x=>!!cast(IndexExp)x||!!cast(Identifier)x)){
		sc.error("only swapping of variables and array components supported in permute statement", be.loc);
		be.sstate=SemState.error;
		return be;
	}
	foreach(e;chain(tpl1.e,tpl2.e)){
		if(auto idx=cast(IndexExp)e){
			idx.byRef=true;
			bool check(IndexExp e){
				if(e&&(!e.a[0].isLifted(sc)||e.a[0].type&&!e.a[0].type.isClassical())){
					sc.error("index in permute statement must be 'lifted' and classical",e.a[0].loc);
					return false;
				}
				if(e) if(auto idx=cast(IndexExp)e.e) return check(idx);
				auto id=e?cast(Identifier)e.e:null;
				if(e&&!checkAssignable(id?id.meaning:null,id.loc,sc,true))
					return false;
				return true;
			}
			if(!check(idx)){
				be.sstate=SemState.error;
				return be;
			}
		}else if(auto id=cast(Identifier)e){
			if(!checkAssignable(id.meaning,id.loc,sc,true)){
				be.sstate=SemState.error;
				return be;
			}
		}
	}
	be.sstate=SemState.completed; // TODO: redefine variables in local scope?
	return be;
}
}
void typeConstBlock(Declaration decl,Expression blocker,Scope sc){
	if(!isAssignable(decl,sc)) return;
	if(auto vd=cast(VarDecl)decl){
		static if(language==dp) {
			if (cast(ParameterSetTy)vd.vtype) return;
		}
		vd.isConst=true;
		vd.typeConstBlocker=blocker;
	}
	assert(!isAssignable(decl,sc));
}

bool isAssignable(Declaration meaning,Scope sc){
	auto vd=cast(VarDecl)meaning;
	if(!vd||vd.isConst) return false;
	for(auto csc=sc;csc !is meaning.scope_&&cast(NestedScope)csc;csc=(cast(NestedScope)csc).parent)
		if(auto fsc=cast(FunctionScope)csc)
			return false;
	return true;
}

bool checkAssignable(Declaration meaning,Location loc,Scope sc,bool quantumAssign=false){
	auto vd=cast(VarDecl)meaning;
	if(!vd||vd.isConst){
		if(vd&&vd.isConst){
			sc.error("cannot reassign 'const' variables",loc);
			if(vd.typeConstBlocker){
				string name;
				if(auto decl=cast(Declaration)vd.typeConstBlocker) name=decl.getName;
				if(name){
					sc.note(format("'%s' was made 'const' because it appeared in type of '%s'",vd.name,name),vd.typeConstBlocker.loc);
				}else{
					sc.note(format("'%s' was made 'const' because it appeared in type of local variable",vd.name),vd.typeConstBlocker.loc);
				}
			}
		}else if(meaning&&!vd) sc.error("can only assign to variables",loc);
		else sc.error("cannot assign",loc);
		return false;
	}else if(cast(Parameter)meaning&&(cast(Parameter)meaning).isConst){
		sc.error("cannot reassign 'const' parameters",loc);
		return false;
	}else{
		static if(language==silq){
			if(!quantumAssign&&!vd.vtype.isClassical()&&!sc.canForget(meaning)){
				sc.error("cannot reassign quantum variable", loc);
				return false;
			}
		}
		if(vd.vtype.isTypeTy){
			sc.error("cannot reassign type variables", loc);
			return false;
		}
		for(auto csc=sc;csc !is meaning.scope_;csc=(cast(NestedScope)csc).parent){
			if(auto fsc=cast(FunctionScope)csc){
				// TODO: what needs to be done to lift this restriction?
				// TODO: method calls are also implicit assignments.
				sc.error("cannot assign to variable in closure context (capturing by value)",loc);
				return false;
			}
		}
	}
	return true;
}

AssignExp assignExpSemantic(AssignExp ae,Scope sc){
	ae.type=unit;
	ae.e1=expressionSemantic(ae.e1,sc,ConstResult.yes); // reassigned variable should not be consumed (otherwise, can use ':=')
	propErr(ae.e1,ae);
	if(ae.sstate==SemState.error)
		return ae;
	void checkLhs(Expression lhs){
		if(auto id=cast(Identifier)lhs){
			if(!checkAssignable(id.meaning,ae.loc,sc))
				ae.sstate=SemState.error;
		}else if(auto tpl=cast(TupleExp)lhs){
			foreach(exp;tpl.e)
				checkLhs(exp);
		}else if(auto idx=cast(IndexExp)lhs){
			checkLhs(idx.e);
		}else if(auto sliceExp=cast(SliceExp)lhs){
			checkLhs(sliceExp.e);
		}else if(auto fe=cast(FieldExp)lhs){
			checkLhs(fe.e);
		}else if(auto tae=cast(TypeAnnotationExp)lhs){
			checkLhs(tae.e);
		}else if(auto psh=cast(ParameterSetHandleExp)lhs){
			checkLhs(psh.target);
		}else{
		LbadAssgnmLhs:
			sc.error(format("cannot assign to %s",lhs),ae.e1.loc);
			ae.sstate=SemState.error;
		}
	}
	checkLhs(ae.e1);
	ae.e2=expressionSemantic(ae.e2,sc,ConstResult.no);
	propErr(ae.e2,ae);
	if(ae.sstate!=SemState.error&&!isSubtype(ae.e2.type,ae.e1.type)){
		if(auto id=cast(Identifier)ae.e1){
			sc.error(format("cannot assign %s to variable %s of type %s",ae.e2.type,id,id.type),ae.loc);
			assert(!!id.meaning);
			sc.note("declared here",id.meaning.loc);
		}else sc.error(format(text("cannot assign %s to %s ", ae),ae.e2.type,ae.e1.type),ae.loc);
		ae.sstate=SemState.error;
	}
	static if(language==silq){
	enum Stage{
		collectDeps,
		consumeLhs,
		defineVars
	}
	Dependency[string] dependencies;
	int curDependency;
	void[0][string] consumed;
	void[0][string] defined;
	void updateDependencies(Expression lhs,Expression rhs,bool expandTuples,Stage stage){
		if(auto id=cast(Identifier)lhs){
			if(id&&id.meaning&&id.meaning.name){
				final switch(stage){
					case Stage.collectDeps:
						if(rhs.isQfree()){
							if(id.meaning.getName in dependencies){
								auto dep=dependencies[id.meaning.getName];
								dep.joinWith(rhs.getDependency(sc));
								dependencies[id.meaning.getName]=dep;
							}else dependencies[id.meaning.getName]=rhs.getDependency(sc);
						}
						break;
					case Stage.consumeLhs:
						if(id.meaning.getName !in consumed){
							sc.consume(id.meaning);
							consumed[id.name]=[];
						}
						break;
					case Stage.defineVars:
						auto name=id.meaning.getName;
						if(name !in defined){
							auto var=addVar(name,id.type,lhs.loc,sc);
							if(rhs.isQfree()) sc.addDependency(var,dependencies[name]);
							defined[id.name]=[];
						}
						break;
				}
			}
		}else if(auto tpll=cast(TupleExp)lhs){
			bool ok=false;
			if(expandTuples){
				if(auto tplr=cast(TupleExp)rhs){
					if(tpll.e.length==tplr.e.length){
						foreach(i;0..tpll.e.length)
							updateDependencies(tpll.e[i],tplr.e[i],true,stage);
						ok=true;
					}
				}
			}
			if(!ok) foreach(exp;tpll.e) updateDependencies(exp,rhs,false,stage);
		}else if(auto idx=cast(IndexExp)lhs){
			updateDependencies(idx.e,rhs,false,stage);
		}else if(auto fe=cast(FieldExp)lhs){
			updateDependencies(fe.e,rhs,false,stage);
		}else if(auto tae=cast(TypeAnnotationExp)lhs){
			updateDependencies(tae.e,rhs,expandTuples,stage);
		}else assert(0);
	}
	if(ae.sstate!=SemState.error){
		updateDependencies(ae.e1,ae.e2,true,Stage.collectDeps);
		updateDependencies(ae.e1,ae.e2,true,Stage.consumeLhs);
		foreach(ref dependency;dependencies)
			foreach(name;sc.toPush)
				sc.pushUp(dependency, name);
		sc.pushConsumed();
		updateDependencies(ae.e1,ae.e2,true,Stage.defineVars);
	}
	}
	if(ae.sstate!=SemState.error) ae.sstate=SemState.completed;
	return ae;
}

bool isOpAssignExp(Expression e){
	return cast(OrAssignExp)e||cast(AndAssignExp)e||cast(AddAssignExp)e||cast(SubAssignExp)e||cast(MulAssignExp)e||cast(DivAssignExp)e||cast(IDivAssignExp)e||cast(ModAssignExp)e||cast(PowAssignExp)e||cast(CatAssignExp)e||cast(BitOrAssignExp)e||cast(BitXorAssignExp)e||cast(BitAndAssignExp)e;
}

bool isInvertibleOpAssignExp(Expression e){
	return cast(AddAssignExp)e||cast(SubAssignExp)e||cast(CatAssignExp)e||cast(BitXorAssignExp)e;
}

ABinaryExp opAssignExpSemantic(ABinaryExp be,Scope sc)in{
	assert(isOpAssignExp(be));
}body{
	static if(language==silq){
		// TODO: assignments to fields
		auto semanticDone=false;
		if(auto id=cast(Identifier)be.e1){
			int nerr=sc.handler.nerrors; // TODO: this is a bit hacky
			auto meaning=sc.lookup(id,false,true,Lookup.probing);
			if(nerr!=sc.handler.nerrors){
				sc.note("looked up here",id.loc);
				return be;
			}
			if(meaning){
				id.meaning=meaning;
				id.name=meaning.getName;
				id.type=typeForDecl(meaning);
				id.scope_=sc;
				id.sstate=SemState.completed;
			}else{
				sc.error(format("undefined identifier %s",id.name),id.loc);
				id.sstate=SemState.error;
			}
			semanticDone=true;
		}
	}else enum semanticDone=false;
	if(!semanticDone) be.e1=expressionSemantic(be.e1,sc,ConstResult.no);
	be.e2=expressionSemantic(be.e2,sc,cast(CatAssignExp)be?ConstResult.no:ConstResult.yes);
	propErr(be.e1,be);
	propErr(be.e2,be);
	if(be.sstate==SemState.error)
		return be;
	void checkULhs(Expression lhs){
		if(auto id=cast(Identifier)lhs){
			if(!checkAssignable(id.meaning,be.loc,sc,isInvertibleOpAssignExp(be)))
				be.sstate=SemState.error;
		}else if(auto idx=cast(IndexExp)lhs){
			checkULhs(idx.e);
		}else if(auto fe=cast(FieldExp)lhs){
			checkULhs(fe.e);
		}else{
		LbadAssgnmLhs:
			sc.error(format("cannot update-assign to %s",lhs),be.e1.loc);
			be.sstate=SemState.error;
		}
	}
	Expression ce=null;
	import ast.parser;
	static foreach(op;binaryOps){
		static if(op.endsWith("←")){
			if(auto ae=cast(BinaryExp!(Tok!op))be){
				ce=new BinaryExp!(Tok!(op[0..$-"←".length]))(be.e1, be.e2);
				ce.loc=be.loc;
			}
		}
	}
	assert(!!ce);
	ce=expressionSemantic(ce,sc,ConstResult.no);
	propErr(ce, be);
	checkULhs(be.e1);
	if(be.sstate!=SemState.error&&!isSubtype(ce.type, be.e1.type)){
		sc.error(format("incompatible operand types %s and %s",be.e1.type,be.e2.type),be.loc);
		be.sstate=SemState.error;
	}
	static if(language==silq){
		if(be.sstate!=SemState.error&&!be.e1.type.isClassical()){
			auto id=cast(Identifier)be.e1;
			if(!id){
				sc.error(format("cannot update-assign to quantum expression %s",be.e1),be.e1.loc);
				be.sstate=SemState.error;
			}else if((!isInvertibleOpAssignExp(be)||be.e2.hasFreeIdentifier(id.name))&&id.meaning&&!sc.canForget(id.meaning)){
				sc.error("quantum update must be invertible",be.loc);
				be.sstate=SemState.error;
			}
			if(id&&id.meaning&&id.meaning.name){
				if(be.e2.isQfree()){
					auto dependency=sc.getDependency(id.meaning);
					dependency.joinWith(be.e2.getDependency(sc));
					sc.consume(id.meaning);
					sc.pushConsumed();
					auto name=id.meaning.name.name;
					auto var=addVar(name,id.type,be.loc,sc);
					dependency.remove(name);
					sc.addDependency(var,dependency);
				}else{
					sc.consume(id.meaning);
					sc.pushConsumed();
					auto var=addVar(id.meaning.name.name,id.type,be.loc,sc);
				}
			}
		}
	}
	be.type=unit;
	if(be.sstate!=SemState.error) be.sstate=SemState.completed;
	return be;
}

bool isAssignment(Expression e){
	return cast(AssignExp)e||isOpAssignExp(e);
}

Expression assignSemantic(Expression e,Scope sc)in{
	assert(isAssignment(e));
}body{
	if(auto ae=cast(AssignExp)e) return assignExpSemantic(ae,sc);
	if(isOpAssignExp(e)) return opAssignExpSemantic(cast(ABinaryExp)e,sc);
	assert(0);
}

bool isDefineOrAssign(Expression e){
	return isAssignment(e)||cast(DefineExp)e||cast(DefExp)e;
}

Expression defineOrAssignSemantic(Expression e,Scope sc)in{
	assert(isDefineOrAssign(e));
}body{
	if(isAssignment(e)) return assignSemantic(e,sc);
	if(auto be=cast(DefineExp)e) return defineSemantic(be,sc);
	if(cast(DefExp)e) return e; // TODO: ok?
	assert(0);
}

Expression expectDefineOrAssignSemantic(Expression e,Scope sc){
	if(auto ce=cast(CommaExp)e){
		ce.e1=expectDefineOrAssignSemantic(ce.e1,sc);
		propErr(ce.e1,ce);
		ce.e2=expectDefineOrAssignSemantic(ce.e2,sc);
		propErr(ce.e2,ce);
		ce.type=unit;
		if(ce.sstate!=SemState.error) ce.sstate=SemState.completed;
		return ce;
	}
	if(isDefineOrAssign(e)) return defineOrAssignSemantic(e,sc);
	sc.error("expected assignment or variable declaration",e.loc);
	e.sstate=SemState.error;
	return e;
}


Expression callSemantic(CallExp ce,Scope sc,ConstResult constResult){
	if(auto id=cast(Identifier)ce.e) id.calledDirectly=true;
	ce.e=expressionSemantic(ce.e,sc,ConstResult.no);
	propErr(ce.e,ce);
	if(ce.sstate==SemState.error)
		return ce;
	scope(success){
		if(ce&&ce.sstate!=SemState.error){
			if(auto ft=cast(FunTy)ce.e.type){
				if(ft.annotation<sc.restriction()){
					if(ft.annotation==Annotation.none){
						sc.error(format("cannot call function '%s' in '%s' context", ce.e, sc.restriction()), ce.loc);
					}else{
						sc.error(format("cannot call '%s' function '%s' in '%s' context", ft.annotation, ce.e, sc.restriction()), ce.loc);
					}
					ce.sstate=SemState.error;
				}
				static if(language==silq){
					if(constResult&&!ce.isLifted(sc)&&!ce.type.isClassical()){
						sc.error("non-'lifted' quantum expression must be consumed", ce.loc);
						ce.sstate=SemState.error;
					}
					if(ce.arg.type.isClassical()&&ft.annotation>=Annotation.qfree){
						if(auto classical=ce.type.getClassical())
							ce.type=classical;
					}
				}
			}
		}
	}
	auto fun=ce.e;
	bool matchArg(FunTy ft){
		if(ft.isTuple){
			if(auto tpl=cast(TupleExp)ce.arg){
				foreach(i,ref exp;tpl.e){
					exp=expressionSemantic(exp,sc,(ft.isConst.length==tpl.e.length?ft.isConst[i]:true)?ConstResult.yes:ConstResult.no);
					propErr(exp,tpl);
				}
				if(tpl.sstate!=SemState.error){
					tpl.type=tupleTy(tpl.e.map!(e=>e.type).array);
				}
			}else{
				ce.arg=expressionSemantic(ce.arg,sc,(ft.isConst.length?ft.isConst[0]:true)?ConstResult.yes:ConstResult.no);
				if(!ft.isConst.all!(x=>x==ft.isConst[0])){
					sc.error("cannot match single tuple to function with mixed 'const' and consumed parameters",ce.loc);
					ce.sstate=SemState.error;
					return true;
				}
			}
		}else{
			assert(ft.isConst.length==1);
			ce.arg=expressionSemantic(ce.arg,sc,ft.isConst[0]?ConstResult.yes:ConstResult.no);
		}
		return false;
	}
	CallExp checkFunCall(FunTy ft){
		bool tryCall(){
			if(!ce.isSquare && ft.isSquare){
				auto nft=ft;
				if(auto id=cast(Identifier)fun){
					if(auto decl=cast(DatDecl)id.meaning){
						if(auto constructor=cast(FunctionDef)decl.body_.ascope_.lookup(decl.name,false,false,Lookup.consuming)){
							if(auto cty=cast(FunTy)typeForDecl(constructor)){
								assert(ft.cod.isTypeTy);
								nft=productTy(ft.isConst,ft.names,ft.dom,cty,ft.isSquare,ft.isTuple,ft.annotation,true, ft.isParameterized, ft.isInitialized, ft.isDifferentiable);
							}
						}
					}
				}
				if(auto codft=cast(ProductTy)nft.cod){
					if(matchArg(codft)) return true;
					propErr(ce.arg,ce);
					if(ce.arg.sstate==SemState.error) return true;
					Expression garg;
					auto tt=nft.tryMatch(ce.arg,garg);
					if(!tt) return false;
					auto nce=new CallExp(ce.e,garg,true,false);
					nce.loc=ce.loc;
					auto nnce=new CallExp(nce,ce.arg,false,false);
					nnce.loc=ce.loc;
					nnce=cast(CallExp)callSemantic(nnce,sc,ConstResult.no);
					ce=nnce;
					return true;
				}
			}
			if(matchArg(ft)) return true;
			propErr(ce.arg,ce);
			if(ce.arg.sstate==SemState.error) return true;
			ce.type=ft.tryApply(ce.arg,ce.isSquare);
			return !!ce.type;
		}
		if(isReverse(ce.e)){
			ce.arg=expressionSemantic(ce.arg,sc,(ft.isConst.length?ft.isConst[0]:true)?ConstResult.yes:ConstResult.no);
			if(auto ft2=cast(FunTy)ce.arg.type){
				if(ft2.annotation<Annotation.mfree){
					sc.error("reversed function must be 'mfree'",ce.arg.loc);
					ce.sstate=SemState.error;
				}
				if(!ft2.isClassical()){
					sc.error("reversed function must be classical",ce.arg.loc);
					ce.sstate=SemState.error;
				}
				if(ce.sstate!=SemState.error&&!ft2.cod.hasAnyFreeVar(ft2.names)&&!ft2.isSquare){
					Expression[] constArgTypes1;
					Expression[] argTypes;
					Expression[] constArgTypes2;
					Expression returnType;
					bool ok=true;
					if(!ft2.isTuple){
						assert(ft2.isConst.length==1);
						if(ft2.isConst[0]) constArgTypes1=[ft2.dom];
						else argTypes=[ft2.dom];
					}else{
						auto tpl=ft2.dom.isTupleTy;
						assert(!!tpl && tpl.length==ft2.isConst.length);
						auto numConstArgs1=ft2.isConst.until!(x=>!x).walkLength;
						auto numArgs=ft2.isConst[numConstArgs1..$].until!(x=>x).walkLength;
						auto numConstArgs2=ft2.isConst[numConstArgs1+numArgs..$].until!(x=>!x).walkLength;
						if(numConstArgs1+numArgs+numConstArgs2!=tpl.length){
							ok=false;
							sc.error("reversed function cannot mix 'const' and consumed arguments",ce.arg.loc);
							ce.sstate=SemState.error;
						}
						constArgTypes1=iota(numConstArgs1).map!(i=>tpl[i]).array;
						argTypes=iota(numConstArgs1,numConstArgs1+numArgs).map!(i=>tpl[i]).array;
						constArgTypes2=iota(numConstArgs1+numArgs,tpl.length).map!(i=>tpl[i]).array;
					}
					if(argTypes.any!(t=>t.hasClassicalComponent())){
						ok=false;
						sc.error("reversed function cannot have classical components in consumed arguments",ce.arg.loc);
						ce.sstate=SemState.error;
					}
					returnType=ft2.cod;
					if(returnType.hasClassicalComponent()){
						ok=false;
						sc.error("reversed function cannot have classical components in return value",ce.arg.loc);
						ce.sstate=SemState.error;
					}
					if(ok){
						auto nargTypes=constArgTypes1~[returnType]~constArgTypes2;
						auto nreturnTypes=argTypes;
						auto dom=nargTypes.length==1?nargTypes[0]:tupleTy(nargTypes);
						auto cod=nreturnTypes.length==1?nreturnTypes[0]:tupleTy(nreturnTypes);
						auto isConst=chain(true.repeat(constArgTypes1.length),only(returnType.impliesConst()),true.repeat(constArgTypes2.length)).array;
						auto annotation=ft2.annotation;
						ce.type=funTy(isConst,dom,cod,false,isConst.length!=1,annotation,true);
						return ce;
					}
				}
			}
		}
		if(ce.sstate!=SemState.error&&!tryCall()){
			auto aty=ce.arg.type;
			if(ce.isSquare!=ft.isSquare)
				sc.error(text("function of type ",ft," cannot be called with arguments ",ce.isSquare?"[":"",aty,ce.isSquare?"]":""),ce.loc);
			else sc.error(format("expected argument types %s, but %s was provided",ft.dom,aty),ce.loc);
			ce.sstate=SemState.error;
		}
		return ce;
	}
	static if(language==dp) {
		// allow parameter set constructor calls
		if (auto paramTy = cast(ParameterSetTy)ce.e) {
			ce.type=paramTy;
			if (paramTy != parameterSetTopTy(sc)) {
				sc.error(text("can only explicitly construct instances of ", parameterSetTopTy(sc)), ce.loc);
				ce.sstate = SemState.error;
				return ce;
			}
			return ce;
		}
	}
	if(auto ft=cast(FunTy)fun.type){
		ce=checkFunCall(ft);
	}else if(auto at=isDataTyId(fun)){
		auto decl=at.decl;
		assert(fun.type is typeTy);
		auto constructor=cast(FunctionDef)decl.body_.ascope_.lookup(decl.name,false,false,Lookup.consuming);
		auto ty=cast(FunTy)typeForDecl(constructor);
		if(ty&&decl.hasParams){
			auto nce=cast(CallExp)fun;
			assert(!!nce);
			auto subst=decl.getSubst(nce.arg);
			ty=cast(ProductTy)ty.substitute(subst);
			assert(!!ty);
		}
		if(!constructor||!ty){
			sc.error(format("no constructor for type %s",at),ce.loc);
			ce.sstate=SemState.error;
		}else{
			ce=checkFunCall(ty);
			if(ce.sstate!=SemState.error){
				auto id=new Identifier(constructor.name.name);
				id.loc=fun.loc;
				id.scope_=sc;
				id.meaning=constructor;
				id.name=constructor.getName;
				id.scope_=sc;
				id.type=ty;
				id.sstate=SemState.completed;

				auto fe=cast(FieldExp)fun;
				auto callExpTarget=cast(CallExp)fun;
				
				if(fe){
					assert(fe.e.sstate==SemState.completed);
					ce.e=new FieldExp(fe.e,id);
					ce.e.type=id.type;
					ce.e.loc=fun.loc;
					ce.e.sstate=SemState.completed;
				} else if (callExpTarget && callExpTarget.isSquare && cast(Identifier)callExpTarget.e) {
					// call target is squared call exp, i.e. dat declaration's type arguments
					callExpTarget.e=id;
				} else {
					ce.e=id;
				}
			}
		}
	}else if(isBuiltIn(cast(Identifier)ce.e)){
		auto id=cast(Identifier)ce.e;
		switch(id.name){
			static if(language==silq){
				case "quantumPrimitive":
					return handleQuantumPrimitive(ce,sc);
				case "__show":
					ce.arg=expressionSemantic(ce.arg,sc,ConstResult.yes);
					auto lit=cast(LiteralExp)ce.arg;
					if(lit&&lit.lit.type==Tok!"``") writeln(lit.lit.str);
					else writeln(ce.arg);
					ce.type=unit;
					break;
				case "__query":
					return handleQuery(ce,sc);
			}else static if(language==psi){
				case "Marginal":
					ce.arg=expressionSemantic(ce.arg,sc,ConstResult.yes);
					propErr(ce.arg,ce);
					if(ce.arg.type) ce.type=distributionTy(ce.arg.type,sc);
					break;
				case "sampleFrom":
					return handleSampleFrom(ce,sc);
			}
			default: assert(0,text("TODO: ",id.name));
		}
	} else{
		sc.error(format("cannot call expression of type %s: %s",fun.type,fun),ce.loc);
		ce.sstate=SemState.error;
	}
	return ce;
}

enum ConstResult:bool{
	no,
	yes,
}

Expression broadcastedType(bool preserveBool)(Expression t1, Expression t2) {
	// check for simple assignment compatibility
	if (auto res = t1.combineTypesImpl(t2, true)) {
		return res;
	}
	auto vecTy1 = cast(VectorTy)t1;
	auto vecTy2 = cast(VectorTy)t2;

	// both are vectors
	if (vecTy1&&vecTy2) {
		// case 1: both cases are non-scalar
		// check for broadcastability
	} else if (vecTy1) {
		// case 2: rhs is scalar
		auto broadcastedElementType = arithmeticType!(preserveBool)(vecTy1.elementType, t2);
		if (!broadcastedElementType) return null;
		return replacingElementType(vecTy1, broadcastedElementType);
	} else if (vecTy2) {
		// case 3: lhs is scalar
		auto broadcastedElementType = arithmeticType!(preserveBool)(t1, vecTy2.elementType);
		if (!broadcastedElementType) return null;
		return replacingElementType(vecTy2, broadcastedElementType);
	} else {
		return null;
	}
	return null;
}

Expression arithmeticType(bool preserveBool)(Expression t1, Expression t2){
	t1=unalias(t1); t2=unalias(t2);
	if(isInt(t1) && isSubtype(t2,ℤt(t1.isClassical()))) return t1; // TODO: automatic promotion to quantum
	if(isInt(t2) && isSubtype(t1,ℤt(t2.isClassical()))) return t2;
	if(isUint(t1) && isSubtype(t2,ℤt(t1.isClassical()))) return t1;
	if(isUint(t2) && isSubtype(t1,ℤt(t2.isClassical()))) return t2;
	if(preludeNumericTypeName(t1) != null||preludeNumericTypeName(t2) != null) {
		return joinTypes(t1,t2);
	}
	t1=t1.eval(); t2=t2.eval();
	if (cast(VectorTy)t1||cast(VectorTy)t2) return broadcastedType!(preserveBool)(t1, t2);
	if(!(isNumeric(t1)&&isNumeric(t2))) return null;
	auto r=joinTypes(t1,t2);
	static if(!preserveBool){
		if(r==Bool(true)) return ℕt(true);
		if(r==Bool(false)) return ℕt(false);
	}
	return r;
}
Expression subtractionType(Expression t1, Expression t2){
	auto r=arithmeticType!false(t1,t2);
	return r==ℕt(true)?ℤt(true):r==ℕt(false)?ℤt(false):r;
}
Expression divisionType(Expression t1, Expression t2){
	auto r=arithmeticType!false(t1,t2);
	if(isInt(r)||isUint(r)) return null; // TODO: add a special operator for float and rat?
	return util.among(r,Bool(true),ℕt(true),ℤt(true))?ℚt(true):
		util.among(r,Bool(false),ℕt(false),ℤt(false))?ℚt(false):r;
}
Expression iDivType(Expression t1, Expression t2){
	auto r=arithmeticType!false(t1,t2);
	if(isInt(r)||isUint(r)) return r;
	if(cast(ℂTy)t1||cast(ℂTy)t2) return null;
	bool classical=t1.isClassical()&&t2.isClassical();
	return (cast(BoolTy)t1||cast(ℕTy)t1)&&(cast(BoolTy)t2||cast(ℕTy)t2)?ℕt(classical):ℤt(classical);
}
Expression nSubType(Expression t1, Expression t2){
	auto r=arithmeticType!true(t1,t2);
	if(isUint(r)) return r;
	if(isSubtype(r,ℕt(false))) return r;
	if(isSubtype(r,ℤt(false))) return ℕt(r.isClassical());
	return null;
}
Expression moduloType(Expression t1, Expression t2){
	auto r=arithmeticType!false(t1,t2);
	return r==ℤt(true)?ℕt(true):r==ℤt(false)?ℕt(false):r; // TODO: more general range information?
}
Expression powerType(Expression t1, Expression t2){
	bool classical=t1.isClassical()&&t2.isClassical();
	if(!isNumeric(t1)||!isNumeric(t2)) return null;
	if(cast(BoolTy)t1&&isSubtype(t2,ℕt(classical))) return Bool(classical);
	if(cast(ℕTy)t1&&isSubtype(t2,ℕt(classical))) return ℕt(classical);
	if(cast(ℂTy)t1||cast(ℂTy)t2) return ℂ(classical);
	if(util.among(t1,Bool(true),ℕt(true),ℤt(true),ℚt(true))&&isSubtype(t2,ℤt(false))) return ℚt(t2.isClassical);
	if(util.among(t1,Bool(false),ℕt(false),ℤt(false),ℚt(false))&&isSubtype(t2,ℤt(false))) return ℚt(false);
	return ℝ(classical); // TODO: good?
}
Expression minusBitNotType(Expression t){
	if(!isNumeric(t)) return null;
	if(cast(BoolTy)t||cast(ℕTy)t) return ℤt(t.isClassical());
	return t;
}
Expression notType(Expression t){
	if(!cast(BoolTy)t) return null;
	return t;
}
Expression logicType(Expression t1,Expression t2){
	if(!cast(BoolTy)t1||!cast(BoolTy)t2) return null;
	return Bool(t1.isClassical()&&t2.isClassical());
}
Expression cmpType(Expression t1,Expression t2){
	if(preludeNumericTypeName(t1) != null||preludeNumericTypeName(t2) != null){
		if(!(joinTypes(t1,t2)||isNumeric(t1)||isNumeric(t2)))
			return null;
	}else{
		t1=unalias(t1.eval()); t2=unalias(t2.eval());
		if (cast(StringTy)t1&&cast(StringTy)t2) return Bool(true);
		auto a1=cast(ArrayTy)t1,a2=cast(ArrayTy)t2;
		auto v1=cast(VectorTy)t1,v2=cast(VectorTy)t2;
		Expression n1=a1?a1.next:v1?v1.next:null,n2=a2?a2.next:v2?v2.next:null;
		if(n1&&n2) return cmpType(n1,n2);
		if(!isNumeric(t1)||!isNumeric(t2)||cast(ℂTy)t1||cast(ℂTy)t2) return null;
	}
	return Bool(t1.isClassical()&&t2.isClassical());
}

Expression unwrap(Expression e){
	if(auto tae=cast(TypeAnnotationExp)e)
		return unwrap(tae.e);
	return e;
}

Expression expressionSemantic(Expression expr,Scope sc,ConstResult constResult){
	if(expr.sstate==SemState.completed||expr.sstate==SemState.error) return expr;
	if(expr.sstate==SemState.started){
		assert(false, "cyclic dependency");
		sc.error("cyclic dependency",expr.loc);
		expr.sstate=SemState.error;
		FunctionDef fd=null;
		if(auto le=cast(LambdaExp)expr) fd=le.fd;
		else if(auto id=cast(Identifier)expr) fd=cast(FunctionDef)id.meaning;
		if(fd&&!fd.rret)
			sc.note("possibly caused by missing return type annotation for recursive function",fd.loc);
		return expr;
	}
	assert(expr.sstate==SemState.presemantic);
	expr.sstate=SemState.started;
	static if(language==silq){
		Scope.ConstBlockContext constSave;
		if(!constResult) constSave=sc.saveConst();
	}
	scope(success){
		static if(language==silq){
			if(!constResult) sc.resetConst(constSave);
			expr.constLookup=constResult;
			if(expr&&expr.sstate!=SemState.error){
				if(constResult&&!expr.isLifted(sc)&&!expr.type.isClassical()){
					sc.error("non-'lifted' quantum expression must be consumed", expr.loc);
					expr.sstate=SemState.error;
				}else{
					assert(!!expr.type);
					expr.sstate=SemState.completed;
				}
			}
			if(expr.type==ℕt(false)||expr.type==ℤt(false)||expr.type==ℚt(false)||expr.type==ℝ(false)||expr.type==ℂ(false)){
				sc.error(format("instances of type '%s' not realizable",expr.type),expr.loc);
				expr.sstate=SemState.error;
			}
		}else{
			if(expr&&expr.sstate!=SemState.error){
				assert(!!expr.type, format("%s must have a .type", expr));
				expr.sstate=SemState.completed;
			}
		}
	}
	if(auto cd=cast(CompoundDecl)expr)
		return compoundDeclSemantic(cd,sc);
	if(auto ce=cast(CompoundExp)expr)
		return compoundExpSemantic(ce,sc);
	if(auto le=cast(LambdaExp)expr){
		FunctionDef nfd=le.fd;
		if(!le.fd.scope_){
			le.fd.scope_=sc;
			nfd=cast(FunctionDef)presemantic(nfd,sc);
		}else assert(le.fd.scope_ is sc);
		assert(!!nfd);
		le.fd=functionDefSemantic(nfd,sc);
		assert(!!le.fd);
		propErr(le.fd,le);
		if(le.fd.sstate==SemState.completed)
			le.type=typeForDecl(le.fd);
		if(le.fd.sstate==SemState.completed) le.sstate=SemState.completed;
		return le;
	}
	if(auto fd=cast(FunctionDef)expr){
		sc.error("function definition cannot appear within an expression",fd.loc);
		fd.sstate=SemState.error;
		return fd;
	}
	if(auto ret=cast(ReturnExp)expr){
		sc.error("return statement cannot appear within an expression",ret.loc);
		ret.sstate=SemState.error;
		return ret;
	}
	if(auto ce=cast(CallExp)expr)
		return expr=callSemantic(ce,sc,constResult);
	static if(language==psi) if(auto pl=cast(PlaceholderExp)expr){
		pl.type = ℝ;
		pl.sstate = SemState.completed;
		return pl;
	}
	static if(language==silq) if(auto fe=cast(ForgetExp)expr){
		bool canForgetImplicitly;
		bool checkImplicitForget(Expression var){
			auto id=cast(Identifier)var;
			if(!id) return false;
			auto meaning=sc.lookup(id,false,true,Lookup.probing);
			return meaning&&sc.canForget(meaning);
		}
		if(auto tpl=cast(TupleExp)fe.var) canForgetImplicitly=tpl.e.all!checkImplicitForget;
		else canForgetImplicitly=checkImplicitForget(fe.var);
		auto var=expressionSemantic(fe.var,sc,ConstResult.no);
		propErr(var,fe);
		if(fe.val){
			fe.val=expressionSemantic(fe.val,sc,ConstResult.yes);
			propErr(fe.val,fe);
			if(fe.sstate!=SemState.error&&!fe.val.isLifted(sc)){
				sc.error("forget expression must be 'lifted'",fe.val.loc);
				fe.sstate=SemState.error;
			}
			if(fe.var.type&&fe.val.type && !joinTypes(fe.var.type,fe.val.type)){
				sc.error(format("incompatible types '%s' and '%s' for forget",fe.var.type,fe.val.type),fe.loc);
				fe.sstate=SemState.error;
			}
		}else if(!canForgetImplicitly){
			sc.error(format("cannot synthesize forget expression for '%s'",var),fe.loc);
		}
		fe.type=unit;
		return fe;
	}
	if(auto id=cast(Identifier)expr){
		id.scope_=sc;
		auto meaning=id.meaning;
		if(!meaning){
			int nerr=sc.handler.nerrors; // TODO: this is a bit hacky
			id.meaning=meaning=sc.lookup(id,false,true,constResult?Lookup.constant:Lookup.consuming);
			if(nerr!=sc.handler.nerrors){
				sc.note("looked up here",id.loc);
				id.sstate=SemState.error;
				return id;
			}
			if(!meaning){
				if(auto r=builtIn(id,sc)){
					if(!id.calledDirectly&&util.among(id.name,"Expectation","Marginal","sampleFrom","__query","__show")){
						sc.error("special operator must be called directly",id.loc);
						id.sstate=r.sstate=SemState.error;
					}
					return r;
				}
				sc.error(format("undefined identifier %s",id.name),id.loc);
				id.sstate=SemState.error;
				return id;
			}
			if(auto fd=cast(FunctionDef)meaning)
				if(auto asc=isInDataScope(fd.scope_))
					if(fd.name.name==asc.decl.name.name)
						meaning=asc.decl;
			id.meaning=meaning;
		}
		id.name=meaning.getName;
		propErr(meaning,id);
		id.type=typeForDecl(meaning);
		if(!id.type&&id.sstate!=SemState.error){
			sc.error("invalid forward reference",id.loc);
			id.sstate=SemState.error;
		}
		if(!id.type.isTypeTy){
			if(auto dsc=isInDataScope(meaning.scope_)){
				if(auto decl=sc.getDatDecl()){
					if(decl is dsc.decl){
						auto this_=new Identifier("this");
						this_.loc=id.loc;
						this_.scope_=sc;
						auto fe=new FieldExp(this_,id);
						fe.loc=id.loc;
						return expressionSemantic(fe,sc,ConstResult.no);
					}
				}
			}
		}
		auto vd=cast(VarDecl)meaning;
		if(vd){
			if(cast(TopScope)vd.scope_||vd.vtype.isTypeTy&&vd.initializer){
				if(!vd.initializer||vd.initializer.sstate!=SemState.completed)
					id.sstate=SemState.error;
				id.substitute=true;
				return id;
			}
		}
		if(id.type&&meaning.scope_.getFunction()){
			bool captureChecked=id.type.isClassical();
			assert(sc.isNestedIn(meaning.scope_));
			auto startScope=sc;
			for(auto csc=sc;csc !is meaning.scope_;csc=(cast(NestedScope)csc).parent){
				bool checkCapture(){
					if(constResult){
						sc.error("cannot capture variable as constant", id.loc);
						id.sstate=SemState.error;
						return false;
					}else if(vd&&vd.isConst){
						sc.error("cannot capture 'const' variable", id.loc);
						id.sstate=SemState.error;
						return false;
					}
					return true;
				}
				if(auto fsc=cast(FunctionScope)csc){
					if(!captureChecked){
						captureChecked=true;
						if(!checkCapture()) break;
						if(fsc.fd&&fsc.fd.context&&fsc.fd.context.vtype==contextTy(true)){
							if(!fsc.fd.ftype) fsc.fd.context.vtype=contextTy(false);
							else{
								assert(!fsc.fd.ftype||fsc.fd.ftype.isClassical());
								sc.error("cannot capture quantum variable in classical function", id.loc);
								id.sstate=SemState.error;
								break;
							}
						}
					}
					fsc.addCapture(id,startScope);
					startScope=fsc;
				}
				if(auto dsc=cast(DataScope)csc){
					if(!captureChecked){
						captureChecked=true;
						if(!checkCapture()) break;
					}
					dsc.addCapture(id,startScope);
					startScope=dsc;
				}
			}
		}
		return id;
	}
	if(auto fe=cast(FieldExp)expr){
		fe.e=expressionSemantic(fe.e,sc,ConstResult.yes);
		propErr(fe.e,fe);
		if(fe.sstate==SemState.error)
			return fe;
		auto noMember(){
			sc.error(format("no member %s for type %s",fe.f,fe.e.type),fe.loc);
			fe.sstate=SemState.error;
			return fe;
		}
		static if (language==dp) {
			if (auto e = parameterSetMemberSemantic(fe, sc)) {
				return expr=e;
			}
			if (auto e = parameterSetTangentVectorMemberSemantic(fe, sc)) {
				return expr=e;
			}
			if (auto e = manifoldMemberSemantic(fe.e, fe.f.name, sc)) {
				return expr=e;
			}
			if (auto e = parameterSetParamMemberSemantic(fe.e.type, fe, sc)) {
				return expr=e;
			}
		}
		DatDecl aggrd=null;
		if(auto aggrty=cast(AggregateTy)fe.e.type) aggrd=aggrty.decl;
		else if(auto id=cast(Identifier)fe.e.type) if(auto dat=cast(DatDecl)id.meaning) aggrd=dat;
		Expression arg=null;
		if(auto ce=cast(CallExp)fe.e.type){
			if(auto id=cast(Identifier)ce.e){
				if(auto decl=cast(DatDecl)id.meaning){
					aggrd=decl;
					arg=ce.arg;
				}
			}
		}
		if(aggrd){
			if(aggrd.body_.ascope_){
				auto meaning=aggrd.body_.ascope_.lookupHere(fe.f,false,Lookup.consuming);
				if(!meaning) return noMember();
				fe.f.meaning=meaning;
				fe.f.name=meaning.getName;
				fe.f.scope_=sc;
				fe.f.type=typeForDecl(meaning);
				if(fe.f.type&&aggrd.hasParams){
					auto subst=aggrd.getSubst(arg);
					fe.f.type=fe.f.type.substitute(subst);
				}
				fe.f.sstate=SemState.completed;
				fe.type=fe.f.type;
				if(!fe.type){
					fe.sstate=SemState.error;
					fe.f.sstate=SemState.error;
				}
				return fe;
			}else return noMember();
		}else if(auto vt=cast(VectorTy)fe.e.type){
			if(fe.f.name=="length"){
				auto res = expressionSemantic(vt.num.copy(),sc,ConstResult.no);// TODO: preserve semantic on clone;
				res.type = ℕt(true);
				return expr=res;
			}else return noMember();
		}else if(auto r=builtIn(fe,sc)) return expr=r;
		else return noMember();
	}
	if(auto idx=cast(IndexExp)expr){
		bool replaceIndex=false;
		if(sc.indexToReplace){
			auto rid=getIdFromIndex(sc.indexToReplace);
			assert(rid && rid.meaning);
			if(auto cid=getIdFromIndex(idx)){
				if(rid.name==cid.name){
					if(!cid.meaning){
						cid.meaning=rid.meaning;
						replaceIndex=true;
					}
				}
			}
		}
		idx.e=expressionSemantic(idx.e,sc,ConstResult.yes);
		if(auto ft=cast(FunTy)idx.e.type){
			assert(!replaceIndex);
			Expression arg;
			if(!idx.trailingComma&&idx.a.length==1) arg=idx.a[0];
			else arg=new TupleExp(idx.a);
			arg.loc=idx.loc;
			auto ce=new CallExp(idx.e,arg,true,false);
			ce.loc=idx.loc;
			return expr=callSemantic(ce,sc,ConstResult.no);
		}
		if (auto tvTy=cast(TangentVectorTy)idx.e){
			assert(!replaceIndex);
			if (tvTy.isTypeBound) {
				if (idx.a.length != 1) {
					sc.error("tangent vector types can only be parameterized by a single argument.", idx.loc);
					idx.sstate = SemState.error;
					return idx;
				}
				auto arg = expressionSemantic(idx.a[0], sc, ConstResult.no);
				if (!isSubtype(arg.type, tvTy.bound)) {
					sc.error(format("tangent vector types can only be parameterized by a value of the corresponding manifold type %s not %s",
						tvTy.bound, arg.type), arg.loc);
					idx.sstate = SemState.error;
					return idx;
				}
				return expr=tangentVectorTy(arg, sc);
			}
		}
		// handle parameter set type expressions
		if (auto paramTy = cast(ParameterSetTy) idx.e) {
			return expr=parameterSetTyIndexSemantic(idx, paramTy, idx.a, sc);
		}
		// handle parameter set indexing
		if (auto paramTy = cast(ParameterSetTy) idx.e.type) {
			return expr=parameterSetIndexSemantic(idx, idx.a, sc);
		}
		if (auto tvTy = cast(TangentVectorTy) idx.e.type) {
			if (auto paramTy = cast(ParameterSetTy) tvTy.bound) {
				return expr=parameterSetIndexSemantic(idx, idx.a, sc);
			} else if (auto parameterSetHandleXp = cast(ParameterSetHandleExp) tvTy.bound) {
				return expr=parameterSetIndexSemantic(idx, idx.a, sc);
			} else if (auto parameterSetValue = cast(ParameterSetTy) tvTy.bound.type) {
				return expr=parameterSetIndexSemantic(idx, idx.a, sc);
			}
		}
		if(idx.e.type.isTypeTy){
			assert(!replaceIndex);
			if(auto tty=typeSemantic(expr,sc))
				return tty;
		}
		propErr(idx.e,idx);
		foreach(ref a;idx.a){
			a=expressionSemantic(a,sc,ConstResult.yes);
			propErr(a,idx);
		}
		if(idx.sstate==SemState.error)
			return idx;
		void check(Expression next){
			if(idx.a.length!=1){
				sc.error(format("only one index required to index type %s",idx.e.type),idx.loc);
				idx.sstate=SemState.error;
			}else{
				if(!isSubtype(idx.a[0].type,ℤt(true))&&!isSubtype(idx.a[0].type,Bool(false))&&!isInt(idx.a[0].type)&&!isUint(idx.a[0].type)){
					sc.error(format("index should be integer, not %s",idx.a[0].type),idx.loc);
					idx.sstate=SemState.error;
				}else{
					idx.type=next;
					if(!idx.a[0].type.isClassical()&&idx.type.hasClassicalComponent()){
						sc.error(format("cannot use quantum index to index array whose elements of type '%s' have classical components",idx.type),idx.loc);
						idx.sstate=SemState.error;
					}
				}
			}
		}
		Expression lengthOfRange(RangeExp range) {
			Expression newNum = new BinaryExp!(Tok!"-")(range.e2, range.e1);
			newNum = expressionSemantic(newNum, sc, constResult).eval();
			newNum.type=ℕt(true); // forces a positive num here, anything else fails at runtime anyway
			return newNum;
		}
		Expression checkAndDetermineTensorIndexType(VectorTy vecTy, int argumentIndex=0) {
			if (argumentIndex >= idx.a.length) {
				return vecTy;
			}
			auto a = idx.a[argumentIndex];
			// consider index range arguments here
			auto range = cast(RangeExp)a;

			// check index type
			if(!range&&!isSubtype(a.type,ℤt(true))&&!isSubtype(a.type,Bool(false))&&!isInt(a.type)&&!isUint(a.type)){
				sc.error(format("index should be an integer or index range, not %s",a.type),a.loc);
				idx.sstate=SemState.error;
				return unit;
			}
			// case: more indices were provided
			if (idx.a.length > argumentIndex+1) {
				if (auto nextVecTy=cast(VectorTy)vecTy.next) {
					// recursively check the next index argument with the next vector ty
					auto nextTy = checkAndDetermineTensorIndexType(nextVecTy, argumentIndex+1);
					if (range) {
						return vectorTy(nextTy, lengthOfRange(range));
					} else {
						return nextTy;
					}
				} else {
					sc.error(format("too many indices to index value of type %s",idx.e.type),idx.a[argumentIndex].loc);
					idx.sstate=SemState.error;
					return unit;
				}
			// case: no more indices given
			} else {
				if (range) {
					return vectorTy(vecTy.next, lengthOfRange(range));
				} else {
					return vecTy.next;
				}
			}
		}
		Expression indexedTyped = unalias(idx.e.type).eval();
		if(auto at=cast(ArrayTy)indexedTyped){
			check(at.next);
		}else if(auto vt=cast(VectorTy)indexedTyped){
			idx.type = checkAndDetermineTensorIndexType(vt);
		}else if(isInt(indexedTyped)||isUint(indexedTyped)){
			check(Bool(indexedTyped.isClassical()));
		}else if(auto tt=cast(TupleTy)indexedTyped){
			if(idx.a.length!=1){
				sc.error(format("only one index required to index type %s",tt),idx.loc);
				idx.sstate=SemState.error;
			// case 1: integer index
			} else if (auto lit=cast(LiteralExp)idx.a[0]) {
				if(!lit||lit.lit.type!=Tok!"0"){
					sc.error(format("index for type %s should be integer constant",tt),idx.loc); // TODO: allow dynamic indexing if known to be safe?
					idx.sstate=SemState.error;
				}else{
					auto c=ℤ(lit.lit.str);
					if(c<0||c>=tt.types.length){
						sc.error(format("index for type %s is out of bounds [0..%s)",tt,tt.types.length),idx.loc);
						idx.sstate=SemState.error;
					}else{
						idx.type=tt.types[cast(size_t)c.toLong()];
					}
				}
			// case 2: slice index
			} else if (auto range=cast(RangeExp)idx.a[0]) {
				auto llit=cast(LiteralExp)range.e1, rlit=cast(LiteralExp)range.e2;
				if(!llit||llit.lit.type!=Tok!"0"){
					sc.error(format("slice lower bound for type %s should be integer constant",cast(Expression)tt),idx.loc);
					idx.sstate=SemState.error;
				}
				if(!rlit||rlit.lit.type!=Tok!"0"){
					sc.error(format("slice upper bound for type %s should be integer constant",cast(Expression)tt),idx.loc);
					idx.sstate=SemState.error;
				}
				if(idx.sstate==SemState.error)
					return idx;
				auto lc=ℤ(llit.lit.str), rc=ℤ(rlit.lit.str);
				if(lc<0){
					sc.error(format("slice lower bound for type %s cannot be negative",tt),idx.loc);
					idx.sstate=SemState.error;
				}
				if(lc>rc){
					sc.error("slice lower bound exceeds slice upper bound",idx.loc);
					idx.sstate=SemState.error;
				}
				if(rc>tt.length){
					sc.error(format("slice upper bound for type %s exceeds %s",tt,tt.length),idx.loc);
					idx.sstate=SemState.error;
				}
				idx.type=tt[cast(size_t)lc..cast(size_t)rc];
			} else {
				sc.error(format(" type %s can only be indexed using constant indices or index ranges",cast(Expression)tt),idx.loc);
				idx.sstate=SemState.error;
			}
		}else{
			sc.error(format("type %s is not indexable",indexedTyped),idx.loc);
			idx.sstate=SemState.error;
		}
		if(replaceIndex){
			idx.byRef=true;
			if(idx != sc.indexToReplace){
				sc.error("indices for component replacement must be identical",idx.loc);
				sc.note("replaced component is here",sc.indexToReplace.loc);
				idx.sstate=SemState.error;
			}
			if(constResult){
				sc.error("replaced component must be consumed",idx.loc);
				sc.note("replaced component is here",sc.indexToReplace.loc);
				idx.sstate=SemState.error;
			}
			sc.indexToReplace=null;
		}
		return idx;
	}
	if(auto sl=cast(SliceExp)expr){
		sl.e=expressionSemantic(sl.e,sc,ConstResult.yes);
		propErr(sl.e,sl);
		sl.l=expressionSemantic(sl.l,sc,ConstResult.yes);
		propErr(sl.l,sl);
		sl.r=expressionSemantic(sl.r,sc,ConstResult.yes);
		propErr(sl.r,sl);
		if(sl.sstate==SemState.error)
			return sl;
		if(!isSubtype(sl.l.type,ℤt(true))){
			sc.error(format("lower bound should be classical integer, not %s",sl.l.type),sl.l.loc);
			sl.l.sstate=SemState.error;
		}
		if(!isSubtype(sl.r.type,ℤt(true))){
			sc.error(format("upper bound should be classical integer, not %s",sl.r.type),sl.r.loc);
			sl.r.sstate=SemState.error;
		}
		if(sl.sstate==SemState.error)
			return sl;
		if(auto at=cast(ArrayTy)sl.e.type){
			sl.type=at;
		}else if(auto vt=cast(VectorTy)sl.e.type){
			auto se=new NSubExp(sl.r,sl.l);
			se.type=ℕt(true);
			se.sstate=SemState.completed;
			sl.type=vectorTy(vt.next,se.eval());
		}else if(auto tt=sl.e.type.isTupleTy){
			auto llit=cast(LiteralExp)sl.l, rlit=cast(LiteralExp)sl.r;
			if(!llit||llit.lit.type!=Tok!"0"){
				sc.error(format("slice lower bound for type %s should be integer constant",cast(Expression)tt),sl.loc);
				sl.sstate=SemState.error;
			}
			if(!rlit||rlit.lit.type!=Tok!"0"){
				sc.error(format("slice upper bound for type %s should be integer constant",cast(Expression)tt),sl.loc);
				sl.sstate=SemState.error;
			}
			if(sl.sstate==SemState.error)
				return sl;
			auto lc=ℤ(llit.lit.str), rc=ℤ(rlit.lit.str);
			if(lc<0){
				sc.error(format("slice lower bound for type %s cannot be negative",tt),sl.loc);
				sl.sstate=SemState.error;
			}
			if(lc>rc){
				sc.error("slice lower bound exceeds slice upper bound",sl.loc);
				sl.sstate=SemState.error;
			}
			if(rc>tt.length){
				sc.error(format("slice upper bound for type %s exceeds %s",tt,tt.length),sl.loc);
				sl.sstate=SemState.error;
			}
			sl.type=tt[cast(size_t)lc..cast(size_t)rc];
		}else{ 
			sc.error(format("type %s is not sliceable",sl.e.type),sl.loc);
			sl.sstate=SemState.error;
		}
		sl.sstate=SemState.completed;
		return sl;
	}
	if(cast(CommaExp)expr){
		sc.error("nested comma expressions are disallowed",expr.loc);
		expr.sstate=SemState.error;
		return expr;
	}
	if(auto tpl=cast(TupleExp)expr){
		foreach(ref exp;tpl.e){
			exp=expressionSemantic(exp,sc,constResult);
			propErr(exp,tpl);
		}
		if(tpl.sstate!=SemState.error){
			tpl.type=tupleTy(tpl.e.map!(e=>e.type).array);
		}
		return tpl;
	}
	if(auto arr=cast(ArrayExp)expr){
		Expression t; bool tok=true;
		foreach(i,ref exp;arr.e){
			exp=expressionSemantic(exp,sc,constResult);
			propErr(exp,arr);
			auto nt = joinTypes(t, exp.type);
			if(!nt&&tok){
				Expression texp;
				foreach(j,oexp;arr.e[0..i]){
					if(!joinTypes(oexp, exp)){
						texp=oexp;
						break;
					}
				}
				if(texp){
					sc.error(format("incompatible types %s and %s in array literal",t,exp.type),texp.loc);
					sc.note("incompatible entry",exp.loc);
				}
				arr.sstate=SemState.error;
				tok=false;
			}else t=nt;
		}
		if(arr.e.length && t){
			if(arr.e[0].type) arr.type=arrayTy(t);
		}else arr.type=arrayTy(ℝ(true)); // TODO: type inference?
		return arr;
	}
	if(auto tae=cast(TypeAnnotationExp)expr){
		tae.e=expressionSemantic(tae.e,sc,constResult);
		tae.type=typeSemantic(tae.t,sc);
		propErr(tae.e,tae);
		propErr(tae.t,tae);
		if(!tae.type||tae.sstate==SemState.error)
			return tae;
		if(auto arr=cast(ArrayExp)tae.e){
			if(!arr.e.length){
				if(auto aty=cast(ArrayTy)tae.type)
					arr.type=aty;
				if(auto vty=cast(VectorTy)tae.type)
					arr.type=arrayTy(vty.next);
			}
		}
		if(auto ce=cast(CallExp)tae.e)
			if(auto id=cast(Identifier)ce.e){
				if(id.name=="sampleFrom"||id.name=="readCSV"&&tae.type==arrayTy(arrayTy(ℝ(true))))
					ce.type=tae.type;
			}
		bool typeExplicitConversion(Expression from,Expression to,TypeAnnotationType annotationType){
			if(isSubtype(from,to)) return true;
			if(from==dynamicTy) return true;
			if(annotationType>=annotationType.conversion){
				if(isSubtype(from,ℤt(true))&&(isUint(to)||isInt(to)))
					return true;
				if(isUint(from)&&isSubtype(ℕt(from.isClassical()),to))
					return true;
				if(isInt(from)&&isSubtype(ℤt(from.isClassical()),to))
					return true;
				if((isRat(from)||isFloat(from))&&isSubtype(ℚt(from.isClassical()),to))
					return true;
				auto ce1=cast(CallExp)from;
				if(ce1&&(isInt(ce1)||isUint(ce1))&&(isSubtype(vectorTy(Bool(ce1.isClassical()),ce1.arg),to)||isSubtype(arrayTy(Bool(ce1.isClassical())),to)))
					return true;
				auto ce2=cast(CallExp)to;
				if(ce2&&(isInt(ce2)||isUint(ce2))&&(isSubtype(from,vectorTy(Bool(ce2.isClassical()),ce2.arg))||annotationType==TypeAnnotationType.coercion&&isSubtype(from,arrayTy(Bool(ce2.isClassical())))))
					return true;
			}
			auto tpl1=from.isTupleTy(), tpl2=to.isTupleTy();
			if(tpl1&&tpl2&&tpl1.length==tpl2.length&&iota(tpl1.length).all!(i=>typeExplicitConversion(tpl1[i],tpl2[i],annotationType)))
				return true;
			auto arr1=cast(ArrayTy)from, arr2=cast(ArrayTy)to;
			if(arr1&&arr2&&typeExplicitConversion(arr1.next,arr2.next,annotationType))
				return true;
			auto vec1=cast(VectorTy)from, vec2=cast(VectorTy)to;
			if(vec1&&vec2&&vec1.num==vec2.num&&typeExplicitConversion(vec1.next,vec2.next,annotationType))
				return true;
			if(vec1&&arr2&&typeExplicitConversion(vec1.next,arr2.next,annotationType))
				return true;
			if(annotationType==TypeAnnotationType.coercion){
				if(vec1&&vec2&&typeExplicitConversion(vec1.next,vec2.next,annotationType))
					return true;
				if(arr1&&vec2&&typeExplicitConversion(arr1.next,vec2.next,annotationType))
					return true;
				if(vec1&&tpl2&&iota(tpl2.length).all!(i=>typeExplicitConversion(vec1.next,tpl2[i],annotationType)))
					return true;
				if(tpl1&&vec2&&iota(tpl1.length).all!(i=>typeExplicitConversion(tpl1[i],vec2.next,annotationType)))
					return true;
				if(from.isClassical()&&isSubtype(to.getClassical(),from)&&from.isNumeric) return true;
			}
			return false;
		}
		bool explicitConversion(Expression expr,Expression type,TypeAnnotationType annotationType){
			auto lit=cast(LiteralExp)expr;
			bool isLiteral=lit||cast(UMinusExp)expr&&cast(LiteralExp)(cast(UMinusExp)expr).e;
			if(isLiteral){
				if(isSubtype(expr.type,ℕt(false))&&(isUint(type)||isInt(type)))
					return true;
				if(isSubtype(expr.type,ℤt(false))&&isInt(type))
					return true;
				if(isSubtype(expr.type,ℝ(false))&&isSubtype(ℚt(true),type))
					return true;
				if(isSubtype(expr.type,ℝ(false))&&(isRat(type)||isFloat(type)))
					return true;
				if(lit&&cast(BoolTy)type&&lit.lit.type==Tok!"0"&&!lit.lit.str.canFind(".")){
					auto val=ℤ(lit.lit.str);
					if(val==0||val==1) return true;
				}
			}
			if(typeExplicitConversion(expr.type,type,annotationType)) return true;
			if(auto tpl1=cast(TupleExp)expr){
				if(auto tpl2=type.isTupleTy()){
					return tpl1.e.length==tpl2.length&&iota(tpl1.e.length).all!(i=>explicitConversion(tpl1.e[i],tpl2[i],annotationType));
				}
				if(auto arr=cast(ArrayTy)type){
					return iota(tpl1.e.length).all!(i=>explicitConversion(tpl1.e[i],arr.next,annotationType));
				}
				if(annotationType==TypeAnnotationType.coercion){
					if(auto vec2=cast(VectorTy)type){
						return iota(tpl1.e.length).all!(i=>explicitConversion(tpl1.e[i],vec2.next,annotationType));
					}
				}
			}
			return false;
		}
		if(!explicitConversion(tae.e,tae.type,tae.annotationType)){
			final switch(tae.annotationType){
				case TypeAnnotationType.annotation:
					sc.error(format("type is %s, not %s",tae.e.type,tae.type),tae.loc);
					if(explicitConversion(tae.e,tae.type,TypeAnnotationType.conversion))
						sc.note(format("explicit conversion possible, use '%s as %s'",tae.e,tae.type),tae.loc);
					else if(explicitConversion(tae.e,tae.type,TypeAnnotationType.coercion))
						sc.note(format("(unsafe type coercion possible)"),tae.loc);
					break;
				case TypeAnnotationType.conversion:
					sc.error(format("cannot convert from type %s to %s",tae.e.type,tae.type),tae.loc);
					if(explicitConversion(tae.e,tae.type,TypeAnnotationType.coercion))
						sc.note(format("(unsafe type coercion possible)"),tae.loc);
					break;
				case TypeAnnotationType.coercion:
					sc.error(format("cannot coerce type %s to %s",tae.e.type,tae.type),tae.loc);
					break;
			}
			tae.sstate=SemState.error;
		}
		return expr=tae;
	}

	Expression handleUnary(alias determineType)(string name,Expression e,ref Expression e1){
		e1=expressionSemantic(e1,sc,ConstResult.yes);
		propErr(e1,e);
		if(e.sstate==SemState.error)
			return e;
		e.type=determineType(e1.type);
		if(!e.type){
			sc.error(format("incompatible type %s for %s",e1.type,name),e.loc);
			e.sstate=SemState.error;
		}
		return e;
	}

	// performs the semantic processing for typing (multi-axes) shape expressions as embedded VectorTy s
	Expression tensorTypeSemantic(Expression dtype, Expression shape, Scope sc) {
		if (auto binExp = cast(BinaryExp!(Tok!"×"))shape) {
			auto dimExprs = findDimExprs(binExp, sc);
			bool success=true;
			foreach (ref dim; dimExprs) {
				dim = expressionSemantic(dim,sc,ConstResult.yes);
				if (!(isSubtype(dim.type,ℤt(true)) || isSubtype(dim.type,arrayTy(ℤt(true))))) {
					sc.error("not a valid shape expression", dim.loc);
					dim.sstate = SemState.error;
					success=false;
				}
			}
			if (!success) return null;
			return tensorTy(dtype, dimExprs);
		} else {
			Expression type=expressionSemantic(dtype, sc, ConstResult.yes);
			shape=expressionSemantic(shape, sc, ConstResult.yes);
			if (isSubtype(shape.type, ℕt(true)) || isSubtype(shape.type,arrayTy(ℕt(true)))) {
				return vectorTy(type, shape);
			} else {
				sc.error(format("vector length should be of type ℕ or ℕ[], not %s", shape.type), shape.loc);
				return null;
			}
		}
	}

	Expression handleBinary(alias determineType)(string name,ABinaryExp e,ref Expression e1,ref Expression e2, bool commutative=false){
		Expression processedE1=expressionSemantic(e1,sc,ConstResult.yes);
		propErr(processedE1,e);
		e.e1 = processedE1;
		
		if(e.sstate==SemState.error) {
			return e;
		}
		if(processedE1.type.isTypeTy&&name=="power"){
			if (auto vt = tensorTypeSemantic(processedE1, e2, sc)) {
				propErr(vt,e);
				e.type = typeTy;
				return vt;
			} else {
				e.sstate=SemState.error;
				return e;
			}
		} else {
			Expression processedE2=expressionSemantic(e2,sc,ConstResult.yes);
			propErr(processedE2,e);
			if (processedE1.type&&processedE2.type)
				e.type = determineType(processedE1.type,processedE2.type);
			e.e2 = processedE2;
			// check whether processedE1 explicitly supports the binary operator
			if (!e.type&&processedE1.type&&processedE2.type) {
				auto t1 = processedE1.type.eval(); auto t2 = processedE2.type.eval();
				if (t1.supportsBinaryOperatorImpl(e.opRep, t2)) {
					e.type = meetTypes(processedE1.type, processedE2.type);
				} else if (commutative&&(isNumeric(t1))) {
					// check for scalar commutative operations
					// also try operator check with switched operands, since op is commutative
					if (t2.supportsBinaryOperatorImpl(e.opRep, t1)) e.type = meetTypes(processedE2.type, processedE1.type);
				}
			}
			if(!e.type){
				sc.error(format("incompatible types %s and %s for %s",processedE1.type,processedE2.type,name),e.loc);
				e.sstate=SemState.error;
			}
		}
		return e;
	}
	if(auto ae=cast(AddExp)expr) return expr=handleBinary!(arithmeticType!false)("addition",ae,ae.e1,ae.e2);
	if(auto ae=cast(SubExp)expr) return expr=handleBinary!subtractionType("subtraction",ae,ae.e1,ae.e2);
	if(auto ae=cast(NSubExp)expr) return expr=handleBinary!nSubType("natural subtraction",ae,ae.e1,ae.e2);
	if(auto ae=cast(MulExp)expr) return expr=handleBinary!(arithmeticType!true)("multiplication",ae,ae.e1,ae.e2,true);
	if(auto ae=cast(DivExp)expr) return expr=handleBinary!divisionType("division",ae,ae.e1,ae.e2);
	if(auto ae=cast(IDivExp)expr) return expr=handleBinary!iDivType("integer division",ae,ae.e1,ae.e2);
	if(auto ae=cast(ModExp)expr) return expr=handleBinary!moduloType("modulo",ae,ae.e1,ae.e2);
	if(auto ae=cast(PowExp)expr) return expr=handleBinary!powerType("power",ae,ae.e1,ae.e2);
	if(auto ae=cast(BitOrExp)expr) return expr=handleBinary!(arithmeticType!true)("bitwise or",ae,ae.e1,ae.e2);
	if(auto ae=cast(BitXorExp)expr) return expr=handleBinary!(arithmeticType!true)("bitwise xor",ae,ae.e1,ae.e2);
	if(auto ae=cast(BitAndExp)expr) return expr=handleBinary!(arithmeticType!true)("bitwise and",ae,ae.e1,ae.e2);
	if(auto ae=cast(UMinusExp)expr) return expr=handleUnary!minusBitNotType("minus",ae,ae.e);
	if(auto ae=cast(UNotExp)expr){
		ae.e=expressionSemantic(ae.e,sc,ConstResult.yes);
		static if(language==silq) if(ae.e.type.isTypeTy){
			if(auto ty=typeSemantic(ae.e,sc)){
				if(ty.sstate==SemState.completed){
					if(auto r=ty.getClassical()){
						return expr=typeSemantic(r,sc);
					}else{
						// TODO: have explicit ClassicalTy
						sc.error(format("cannot make type %s classical",ae.e),ae.loc);
						ae.sstate=SemState.error;
						return ae;
					}
				}
			}
		}
		return expr=handleUnary!notType("not",ae,ae.e);
	}
	if(auto ae=cast(UBitNotExp)expr) return expr=handleUnary!minusBitNotType("bitwise not",ae,ae.e);
	static if(language==silq) if(auto ae=cast(UnaryExp!(Tok!"const"))expr){
		sc.error("invalid 'const' annotation", ae.loc);
		ae.sstate=SemState.error;
		return ae;
	}
	if(auto ae=cast(AndExp)expr) return expr=handleBinary!logicType("conjunction",ae,ae.e1,ae.e2);
	if(auto ae=cast(OrExp)expr) return expr=handleBinary!logicType("disjunction",ae,ae.e1,ae.e2);
	if(auto ae=cast(LtExp)expr) return expr=handleBinary!cmpType("'<'",ae,ae.e1,ae.e2);
	if(auto ae=cast(LeExp)expr) return expr=handleBinary!cmpType("'≤'",ae,ae.e1,ae.e2);
	if(auto ae=cast(GtExp)expr) return expr=handleBinary!cmpType("'>'",ae,ae.e1,ae.e2);
	if(auto ae=cast(GeExp)expr) return expr=handleBinary!cmpType("'≥'",ae,ae.e1,ae.e2);
	if(auto ae=cast(EqExp)expr) return expr=handleBinary!cmpType("'='",ae,ae.e1,ae.e2);
	if(auto ae=cast(NeqExp)expr) return expr=handleBinary!cmpType("'≠'",ae,ae.e1,ae.e2);

	if(auto ce=cast(CatExp)expr){
		ce.e1=expressionSemantic(ce.e1,sc,constResult);
		ce.e2=expressionSemantic(ce.e2,sc,constResult);
		propErr(ce.e1,ce);
		propErr(ce.e2,ce);
		if(ce.sstate==SemState.error)
			return ce;
		auto vt1=cast(VectorTy)ce.e1.type,vt2=cast(VectorTy)ce.e2.type;
		assert(!ce.type);
		if(vt1&&vt2){
			if(auto netype=joinTypes(vt1.next,vt2.next)){
				auto add=new AddExp(vt1.num,vt2.num);
				add.type=ℕt(true);
				add.sstate=SemState.completed;
				auto ntype=vectorTy(netype,add.eval()); // TODO: evaluation context
				ce.type=ntype;
			}
		}else{
			auto ntype=joinTypes(ce.e1.type,ce.e2.type);
			if(cast(ArrayTy)ntype)
				ce.type=ntype;
		}
		if(!ce.type){
			sc.error(format("incompatible types %s and %s for ~",ce.e1.type,ce.e2.type),ce.loc);
			ce.sstate=SemState.error;
		}
		return ce;
	}

	if (auto re=cast(RangeExp)expr) {
		re.e1 = expressionSemantic(re.e1, sc, constResult);
		propErr(re.e1,re);
		re.e2 = expressionSemantic(re.e2, sc, constResult);
		propErr(re.e2,re);

		if (!isSubtype(re.e1.type, ℤt(true))) {
			sc.error(text("the lower bound of an index range must be of type ℕ, not ", re.e1.type), re.e1.loc);
			re.sstate=SemState.error;
			return re;
		}
		if (!isSubtype(re.e2.type, ℤt(true))) {
			sc.error(text("the upper bound of an index range must be of type ℕ, not ", re.e2.type), re.e2.loc);
			re.sstate=SemState.error;
			return re;
		}
		re.sstate=SemState.completed;
		re.type=unit;
		return expr=re;
	}

	if(auto pr=cast(BinaryExp!(Tok!"×"))expr){
		// TODO: allow nested declarations
		expr.type=typeTy();
		auto t1=typeSemantic(pr.e1,sc);
		auto t2=typeSemantic(pr.e2,sc);
		
		if(!t1||!t2){
			expr.sstate=SemState.error;
			return expr;
		}
		auto l=t1.isTupleTy(),r=t2.isTupleTy();
		auto merge1=!pr.e1.brackets&&l&&l.length;
		auto merge2=!pr.e2.brackets&&r&&r.length;
		if(merge1 && merge2)
			return tupleTy(chain(iota(l.length).map!(i=>l[i]),iota(r.length).map!(i=>r[i])).array);
		if(merge1) return tupleTy(chain(iota(l.length).map!(i=>l[i]),only(t2)).array);
		if(merge2) return tupleTy(chain(only(t1),iota(r.length).map!(i=>r[i])).array);
		return tupleTy([t1,t2]);
	}
	if(auto ex=cast(BinaryExp!(Tok!"→"))expr){
		expr.type=typeTy();
		Q!(bool[],Expression) getConstAndType(Expression e){
			Q!(bool[],Expression) base(Expression e){
				static if(language==silq) if(auto ce=cast(UnaryExp!(Tok!"const"))e){
					return q([true],typeSemantic(ce.e,sc));
				}
				auto ty=typeSemantic(e,sc);
				return q([ty&&ty.impliesConst()||ex.isLifted],ty);
			}
			if(auto pr=cast(BinaryExp!(Tok!"×"))e){
				auto merge1=!pr.e1.brackets&&cast(BinaryExp!(Tok!"×"))pr.e1;
				auto t1=merge1?getConstAndType(pr.e1):base(pr.e1);
				auto merge2=!pr.e2.brackets&&cast(BinaryExp!(Tok!"×"))pr.e2;
				auto t2=merge2?getConstAndType(pr.e2):base(pr.e2);
				if(!t1[1]||!t2[1]){
					e.sstate=SemState.error;
					return q((bool[]).init,Expression.init);
				}
				auto l=t1[1].isTupleTy(),r=t2[1].isTupleTy();
				merge1&=l&&l.length;
				merge2&=r&&r.length;
				if(merge1 && merge2)
					return q(t1[0]~t2[0],cast(Expression)tupleTy(chain(iota(l.length).map!(i=>l[i]),iota(r.length).map!(i=>r[i])).array));
				if(merge1) return q(t1[0]~t2[0],cast(Expression)tupleTy(chain(iota(l.length).map!(i=>l[i]),only(t2[1])).array));
				if(merge2) return q(t1[0]~t2[0],cast(Expression)tupleTy(chain(only(t1[1]),iota(r.length).map!(i=>r[i])).array));
				return q(t1[0]~t2[0],cast(Expression)tupleTy([t1[1],t2[1]]));
			}
			return base(e);
		}
		auto t1=getConstAndType(ex.e1);
		auto t2=typeSemantic(ex.e2,sc);
		if(!t1[1]||!t2){
			expr.sstate=SemState.error;
			return expr;
		}
		static if(language==dp) return expr=funTy(t1[0],t1[1],t2,false,!!t1[1].isTupleTy()&&t1[0].length!=1,
			ex.annotation,false,true, false, true);
		else return expr=funTy(t1[0],t1[1],t2,false,!!t1[1].isTupleTy()&&t1[0].length!=1,ex.annotation,false);
	}
	if(auto fa=cast(RawProductTy)expr){
		expr.type=typeTy();
		auto fsc=new RawProductScope(sc,fa.annotation);
		scope(exit) fsc.forceClose();
		declareParameters(fa,fa.isSquare,fa.params,fsc); // parameter variables
		auto cod=typeSemantic(fa.cod,fsc);
		propErr(fa.cod,fa);
		if(fa.sstate==SemState.error) return fa;
		auto const_=fa.params.map!(p=>p.isConst).array;
		auto names=fa.params.map!(p=>p.getName).array;
		auto types=fa.params.map!(p=>p.vtype).array;
		assert(fa.isTuple||types.length==1);
		auto dom=fa.isTuple?tupleTy(types):types[0];
		static if(language==dp) return expr=productTy(const_,names,dom,cod,fa.isSquare,fa.isTuple,
			fa.annotation,false, true, false, true);
		else return expr=productTy(const_,names,dom,cod,fa.isSquare,fa.isTuple,fa.annotation,false);
	}
	if(auto ite=cast(IteExp)expr){
		ite.cond=conditionSemantic!true(ite.cond,sc);
		if(ite.then.s.length!=1||ite.othw&&ite.othw.s.length!=1){
			sc.error("branches of if expression must be single expressions;",ite.loc);
			ite.sstate=SemState.error;
			return ite;
		}
		static if(language==silq){
			auto quantumControl=ite.cond.type!=Bool(true);
			auto restriction_=quantumControl?Annotation.mfree:Annotation.none;
		}else{
			enum quantumControl=false;
			enum restriction_=Annotation.none;
		}
		Expression branchSemantic(Expression branch,Scope sc){
			if(auto ae=cast(AssertExp)branch){
				branch=statementSemantic(branch,sc);
				if(auto lit=cast(LiteralExp)ae.e)
					if(lit.lit.type==Tok!"0" && lit.lit.str=="0")
						branch.type=null;
			}else branch=expressionSemantic(branch,sc,constResult);
			return branch;
		}
		// initialize scopes, to allow captures to be inserted
		ite.then.blscope_=new BlockScope(sc,restriction_);
		if(ite.othw) ite.othw.blscope_=new BlockScope(sc,restriction_);
		ite.then.s[0]=branchSemantic(ite.then.s[0],ite.then.blscope_);
		static if(language==silq) ite.then.blscope_.pushConsumed();
		propErr(ite.then.s[0],ite.then);
		if(!ite.othw){
			sc.error("missing else for if expression",ite.loc);
			ite.sstate=SemState.error;
			return ite;
		}
		ite.othw.s[0]=branchSemantic(ite.othw.s[0],ite.othw.blscope_);
		static if(language==silq) ite.othw.blscope_.pushConsumed();
		propErr(ite.othw.s[0],ite.othw);
		propErr(ite.cond,ite);
		propErr(ite.then,ite);
		propErr(ite.othw,ite);
		if(ite.sstate==SemState.error)
			return ite;
		if(!ite.then.s[0].type) ite.then.s[0].type = ite.othw.s[0].type;
		if(!ite.othw.s[0].type) ite.othw.s[0].type = ite.then.s[0].type;
		auto t1=ite.then.s[0].type;
		auto t2=ite.othw.s[0].type;
		ite.type=joinTypes(t1,t2);
		if(t1 && t2 && !ite.type){
			sc.error(format("incompatible types %s and %s for branches of if expression",t1,t2),ite.loc);
			ite.sstate=SemState.error;
		}
		if(quantumControl&&ite.type&&ite.type.hasClassicalComponent()){
			// TODO: automatically promote to quantum if possible
			sc.error(format("type '%s' of if expression with quantum control has classical components",ite.type),ite.loc);
			ite.sstate=SemState.error;
		}
		if(sc.merge(quantumControl,ite.then.blscope_,ite.othw.blscope_)){
			sc.note("consumed in one branch of if expression", ite.loc);
			ite.sstate=SemState.error;
		}
		return ite;
	}
	if(auto lit=cast(LiteralExp)expr){
		switch(lit.lit.type){
		case Tok!"0",Tok!".0":
			if(!expr.type) 
				expr.type=lit.lit.str.canFind(".")?ℝ(true):lit.lit.str.canFind("-")?ℤt(true):ℕt(true); // TODO: type inference
			return expr;
		case Tok!"``":
			expr.type=stringTy(true);
			return expr;
		default: break; // TODO
		}
	}
	if(auto binaryPullbackCallExp=cast(BinaryPullbackCallExp)expr){
		binaryPullbackCallExp.v = expressionSemantic(binaryPullbackCallExp.v, sc, ConstResult.no);
		binaryPullbackCallExp.e1 = expressionSemantic(binaryPullbackCallExp.e1, sc, ConstResult.no);
		binaryPullbackCallExp.e2 = expressionSemantic(binaryPullbackCallExp.e2, sc, ConstResult.no);
		
		binaryPullbackCallExp.type = binaryPullbackTy(binaryPullbackCallExp, sc);

		if (!binaryPullbackCallExp.type) {
			sc.error("failed to type pullback expression", binaryPullbackCallExp.loc);
			binaryPullbackCallExp.type = unit;
		}
		
		if (binaryPullbackCallExp.e1.sstate != SemState.completed ||
			binaryPullbackCallExp.e2.sstate != SemState.completed || 
			binaryPullbackCallExp.v.sstate != SemState.completed) {
			
			binaryPullbackCallExp.sstate = SemState.error;
			return binaryPullbackCallExp;
		}

		return binaryPullbackCallExp;
	}
	if(auto pullExp=cast(PullExp)expr){
		propErr(pullExp.target, pullExp);
		pullExp.type=unit;

		CallExp isSquareCallExp(Expression e) {
			if (auto idx=cast(IndexExp)e) {
				auto ce = new CallExp(idx.e, idx.a.length>1?new TupleExp(idx.a):idx.a[0], true, true);
				ce.loc=idx.loc;
				return ce;
			}
			if (auto ce=cast(CallExp)e) if (ce.isSquare) return ce;
			return null;
		}

		CallExp ce=cast(CallExp)pullExp.target;
		if (!ce) ce = isSquareCallExp(pullExp.target);

		if (!ce) { // target should be a differentiable function reference (e.g. `pull f`)
			return pullExpSemantic(pullExp, expressionSemantic(pullExp.target, sc, constResult), sc);
		}
		
		if (!ce.isSquare) { // ce is (v) of f[x](v)
			CallExp innerCe = isSquareCallExp(ce?ce.e:null); // this is f[x] of f[x](v)
			// process inner call expression as non-squared function call (e.g. f(x) for f[x](v))
			innerCe.isSquare = false;
			innerCe = cast(CallExp)expressionSemantic(innerCe, sc, constResult);

			pullExp = pullExpSemantic(pullExp, innerCe.e, sc);

			CallExp pullCallExp;

			pullCallExp = new CallExp(
				new CallExp(pullExp, innerCe.arg, true, true), // pull f[x]
				ce.arg, false, true); // pull f[x](v)
			pullCallExp.loc=pullExp.loc;
			pullCallExp.e.loc=innerCe.loc;
			return expressionSemantic(pullCallExp, sc, constResult);
		} else { // ce.isSquare = false, ce is f[x] w/o (v)
			// process inner call expression as non-squared function call (e.g. f(x) for f[x](v))
			ce = cast(CallExp)expressionSemantic(ce, sc, constResult);

			pullExp = pullExpSemantic(pullExp, ce.e, sc);

			CallExp pullCallExp;

			pullCallExp = new CallExp(pullExp, ce.arg, true, true); // pull f[x]
			pullCallExp.loc=pullExp.loc;
			pullCallExp.e.loc=ce.loc;
			return expressionSemantic(pullCallExp, sc, constResult);
		}
	}
	if(auto untapeExp=cast(UntapeExp)expr){
		return untapeExp;
	}
	if(auto tapeExp=cast(TapeExp)expr){
		tapeExp.type=unit;
		tapeExp.e = expressionSemantic(tapeExp.e, sc, ConstResult.no);
		return tapeExp;
	}
	if(auto npt=cast(NoParamTypeExp)expr){
		npt.e = expressionSemantic(npt.e, sc, ConstResult.yes);
		ProductTy prodTy = cast(ProductTy)npt.e;
		if (!prodTy) {
			sc.error("operator noparam can only be applied to function type expressions", npt.loc);
			npt.sstate = SemState.error;
			return npt;
		}
		return expr=productTy(prodTy.isConst, prodTy.names, prodTy.dom, prodTy.cod, prodTy.isSquare,
			prodTy.isTuple, prodTy.annotation, prodTy.isClassical, false, false, prodTy.isDifferentiable);
	}
	if(auto ndt=cast(NonDiffTypeExp)expr){
		// handle case of nondiff lambda expressions
		if (auto le = cast(LambdaExp)ndt.e) {
			le.fd.isDifferentiable = false;
			return expr=expressionSemantic(ndt.e, sc, ConstResult.yes);
		}
		// handle nondiff as type operator
		ndt.e = expressionSemantic(ndt.e, sc, ConstResult.yes);
		if (ProductTy prodTy = cast(ProductTy)ndt.e) {
			return expr=productTy(prodTy.isConst, prodTy.names, prodTy.dom, prodTy.cod, prodTy.isSquare,
				prodTy.isTuple, prodTy.annotation, prodTy.isClassical, prodTy.isParameterized, prodTy.isInitialized, false);
		} else {
			sc.error("operator nondiff can only be applied to function type or lambda expressions", ndt.loc);
			ndt.sstate = SemState.error;
			return ndt;
		}
	}
	if (auto unparamExp=cast(UnparamExp)expr) {
		unparamExp.e = expressionSemantic(unparamExp.e, sc, ConstResult.yes);
		unparamExp.type = unit;
		
		ProductTy prodTy = cast(ProductTy)unparamExp.e.type;
		if (!prodTy) {
			sc.error(text("operator unparam can only be applied to function expressions, not expressions of type ", 
				unparamExp.e.type), unparamExp.loc);
			unparamExp.sstate = SemState.error;
			return unparamExp;
		}
		if (!prodTy.isParameterized) {
			sc.error(text("operator unparam can only be applied to parameterized function expressions, not ", 
				prodTy), unparamExp.loc);
			unparamExp.sstate = SemState.error;
			return unparamExp;
		}
		if (!prodTy.isInitialized) {
			sc.error(text("operator unparam can only be applied to initialized parametered function expressions, not ", 
				unparamExp.e.type), unparamExp.loc);
			unparamExp.sstate = SemState.error;
			return unparamExp;
		}
		auto unparamProdTy = unparam(prodTy, unparamExp, sc);
		unparamExp.type = unparamProdTy;
		return unparamExp;
	}
	// not exposed in syntax but may be emitted by lowering pass and reappear during AD
	if (auto initializedFunctionExp=cast(InitializedFunctionExp)expr) {
		initializedFunctionExp.f = expressionSemantic(initializedFunctionExp.f, sc, constResult);
		initializedFunctionExp.p = expressionSemantic(initializedFunctionExp.p, sc, constResult);
		
		auto prodTy = cast(ProductTy)initializedFunctionExp.f.type;
		if (!prodTy) return initializedFunctionExp;

		if (!prodTy.isParameterized) {
			sc.error("cannot initialize non-parameterized function", expr.loc);
			expr.sstate=SemState.error;
			return expr;
		}
		
		initializedFunctionExp.type = productTy(prodTy.isConst, prodTy.names, 
			prodTy.dom, prodTy.cod, prodTy.isSquare, prodTy.isTuple, prodTy.annotation, 
			prodTy.isClassical, true, true, prodTy.isDifferentiable, prodTy.isPullbackOf
		);
		return initializedFunctionExp;
	}
	if (auto gradExp=cast(GradExp)expr) {
		gradExp.e=expressionSemantic(gradExp.e, sc, constResult);
		gradExp.type=unit;
		
		auto ce=cast(CallExp)gradExp.e;
		if (!ce) {
			sc.error("the gradient operator can only be applied to function call expressions (e.g. grad f(x))", gradExp.loc);
			gradExp.sstate = SemState.error;
			return gradExp;
		}

		ProductTy ftype = cast(ProductTy)ce.e.type;
		if (!ftype) return ce;
		auto cod = ftype.cod;
		if (cod!=ℝ(true)) {
			sc.error("the gradient operator can only be applied to functions with co-domain ℝ", gradExp.loc);
			gradExp.sstate = SemState.error;
			return gradExp;
		}

		// turn f(x) into pull f[x](1.0)
		ce.isSquare = true;
		PullExp pullExp = new PullExp(new CallExp(ce, LiteralExp.makeFloat(1.0), false, true));
		propErr(pullExp, gradExp);
		return expressionSemantic(pullExp, sc, constResult);
	}
	if(auto initExp=cast(InitExp)expr){
		initExp.target=expressionSemantic(initExp.target, sc, ConstResult.yes);
		propErr(initExp.target, initExp);
		initExp.type=unit;

		if (auto ftype = cast(FunTy)initExp.target.type) {
			initExp.type = init(ftype, initExp, sc);
		} else if (auto ftype=cast(FunTy)initExp.target) {
			initExp.type = typeTy;
			return expr=init(ftype, initExp, sc);
		} else if (initExp.target.sstate!=SemState.error) {
			sc.error(format("cannot initialize expressions of type %s", initExp.target.type),initExp.target.loc);
			initExp.sstate=SemState.error;
		}
		return initExp;
	}
	if (auto paramSetHandleExp=cast(ParameterSetHandleExp)expr){
		paramSetHandleExp.target = expressionSemantic(paramSetHandleExp.target, sc, ConstResult.no);
		paramSetHandleExp.type = parameterSetTy(paramSetHandleExp.target, sc);
		return paramSetHandleExp;
	}
	if (auto nogradExp=cast(NoGradExp)expr) {
		return expr;
	}
	if(expr.kind=="expression") sc.error("unsupported",expr.loc);
	else sc.error(expr.kind~" cannot appear within an expression",expr.loc);
	expr.sstate=SemState.error;
	return expr;
}
PullExp pullExpSemantic(PullExp pullExp, Expression target, Scope sc) {
	auto ftype = cast(ProductTy)target.type;
	auto fname = target.toString;

	if (!ftype) {
		sc.error(format("can only call pullback of functions, not %s", target.type), target.loc);
		pullExp.sstate = SemState.error;
		return pullExp;
	}

	if (!ftype.isDifferentiable) {
		sc.error(format("non-differentiable %s does not have a pullback", fname), pullExp.loc);
		pullExp.sstate = SemState.error;
		return pullExp;
	}

	auto pty = pullbackTy(fname, ftype, sc, target);
	if (!pty) {
		sc.error(format("%s does not have a pullback", fname), target.loc);
		pullExp.sstate = SemState.error;
		return pullExp;
	}

	pullExp.target = target;
	pullExp.type = pullbackTy(fname, ftype, sc, target);
	pullExp.sstate = SemState.completed;

	return pullExp;
}

Expression conditionSemantic(bool allowQuantum=false)(Expression e,Scope sc){
	e=expressionSemantic(e,sc,ConstResult.yes);
	static if(language==silq) sc.pushConsumed();
	if(e.sstate==SemState.completed && (allowQuantum?!cast(BoolTy)e.type:e.type!=Bool(true))){
		static if(language==silq){
			static if(allowQuantum) sc.error(format("type of condition should be !𝔹 or 𝔹, not %s",e.type),e.loc);
			else sc.error(format("type of condition should be !𝔹, not %s",e.type),e.loc);
		}else sc.error(format("type of condition should be 𝔹, not %s",e.type),e.loc);
		e.sstate=SemState.error;
	}
	return e;
}

/// resolves only parameter members of A, given fe is access on type params[A] or params[a] where a:A (contextTy=params[A])
static if (language==dp) FieldExp parameterSetParamMemberSemantic(Expression contextTy, FieldExp fe, Scope sc) {
	auto paramSetTy=cast(ParameterSetTy)contextTy;
	if (!paramSetTy) return null;

	// determine underlying type of parameter set target expression
	Expression targetType;
	if (paramSetTy.isTypeBound) targetType = paramSetTy.target;
	else targetType = paramSetTy.target.type;

	// determine type of field expression in non-parameter context
	//  - construct dummy FieldExp of type targetType
	auto target = new Identifier("_"); target.type = targetType; target.sstate = SemState.completed;
	//  - semantically process dummy FieldExp on target to obtain member
	auto nonParamSetFieldExp = new FieldExp(target, new Identifier(fe.f.name));
	nonParamSetFieldExp = cast(FieldExp)expressionSemantic(nonParamSetFieldExp, sc, ConstResult.no);
	
	// not found in non-parameter context aggregate type
	if (nonParamSetFieldExp is null || nonParamSetFieldExp.sstate==SemState.error) return null;

	// otherwise, fe could be resolved in non-parameter context
	VarDecl decl = cast(VarDecl)nonParamSetFieldExp.f.meaning;
	// check that field resolves to valid parameter field (e.g. not a function member)
	if (decl is null) return null;

	// allowed members on param[A] are
	// 1. member of A, which refers to AggregateTy value with parameters itself
	if (auto aggrty = isDataTyId(decl.vtype)) {
		fe.f.type = parameterSetTy(aggrty, sc);
		fe.type = parameterSetTy(aggrty, sc);
	} else {
	// 2. member is parameter of A
		if (!decl.isParamDefinition) return null;
		fe.f.type = nonParamSetFieldExp.type;
		fe.type = nonParamSetFieldExp.type;
	}

	// if value-bound, refine type of fe by using information in paramSetTy (type of fe.e)
	// (e.g. a.f: params[F] becomes a.f: params[a.f] if a: params[a])
	// (case 2: e.g. a.f: params[F] becomes a.f: params[a.f] if a: params[A])
	if (paramSetTy.isValueBound&&cast(ParameterSetTy)fe.type) {
		auto continuedValueBound = expressionSemantic(new FieldExp(paramSetTy.target, new Identifier(fe.f.name)), sc, ConstResult.yes);
		fe.f.type = parameterSetTy(continuedValueBound, sc);
		fe.type = fe.f.type;
	}

	fe.f.meaning = decl;
	fe.sstate = SemState.completed;

	return fe;
}

// init operator on the type-level
static if (language==dp) ProductTy init(ProductTy ftype, InitExp initExp, Scope sc) {
	assert(!ftype.isInitialized, text("cannot reinitialize ", initExp.target));
	if (!ftype.isParameterized) {
		sc.error(format("cannot initialize non-parameterized function of type %s",ftype.toString),initExp.target.loc);
		initExp.sstate=SemState.error;
		return ftype;
	}

	return productTy(ftype.isConst, ftype.names, ftype.dom, ftype.cod, ftype.isSquare, 
		ftype.isTuple, ftype.annotation, ftype.isClassical, true, true, ftype.isDifferentiable);
}

// unparam operator on the type-level
static if (language==dp) ProductTy unparam(ProductTy prodTy, UnparamExp unparamExp, Scope sc) {
	assert(prodTy.names.length==0||prodTy.names[$-1]!="θ", text(" cannot unparam ", unparamExp));
	auto argtys = iota(prodTy.names.length).map!(i => prodTy.argTy(i)).array;
	auto extendedDomElements = argtys ~ cast(Expression[])[parameterSetTy(unparamExp.e, sc)];
	return productTy(prodTy.isConst ~ [true], prodTy.names ~ ["θ"], 
		tupleTyIfRequired(extendedDomElements),
		prodTy.cod, prodTy.isSquare, extendedDomElements.length > 1, prodTy.annotation, prodTy.isClassical, false, false, 
		prodTy.isDifferentiable, prodTy.isPullbackOf
	);
}

static if (language==dp) Expression parameterSetTangentVectorMemberSemantic(FieldExp fe, Scope sc) {
	TangentVectorTy tangentVecTy = cast(TangentVectorTy) fe.e.type;
	if (!tangentVecTy) return null;
	// replace tangentVecTy with evaluated TangentVectorTy instance
	if (auto evalutatedTvTy = cast(TangentVectorTy)tangentVecTy.eval()) tangentVecTy = evalutatedTvTy;

	// try to resolve fe.f on type A (assuming tangentVecTy.bound: params[A])
	FieldExp nonTangentVecField = parameterSetParamMemberSemantic(tangentVecTy.bound, fe.copy(), sc);
	if (!nonTangentVecField) return null;

	// derive actual fe.type by changing it to the corresponding .tangentVector type
	auto tangentFieldType = typeSemantic(new FieldExp(nonTangentVecField, new Identifier("tangentVector")), sc);
	assert(tangentFieldType);

	fe.f.type = tangentFieldType;
	fe.type = tangentFieldType;
	fe.f.meaning = nonTangentVecField.f.meaning;
	
	return fe;
}

static if (language==dp) Expression parameterSetMemberSemantic(FieldExp fe, Scope sc) {
	const auto memberName = fe.f.name;
	if (memberName != "params") {
		return null;
	}
	// case: parameterised AggrTy as manifolds
	if (auto aggrTy=isDataTyId(fe.e.type)) {
		if (aggrTy.isParameterized) {
			auto paramExp = new ParameterSetHandleExp(fe.e);
			return expressionSemantic(paramExp, sc, ConstResult.no);
		}
	}
	// case: direct reference AggrTy as manifolds
	if (auto aggrTy=isDataTyId(fe.e)) {
		if (aggrTy.isParameterized) {
			return parameterSetTy(fe.e, sc);
		}
	}
	// case: initialised functions as manifolds
	if (auto funTy=cast(FunTy)fe.e.type) {
		if (funTy.isParameterized && funTy.isInitialized) {
			auto paramExp = new ParameterSetHandleExp(fe.e);
			return expressionSemantic(paramExp, sc, ConstResult.no);
		}
	}
	return null;
}

Type typeOrDataType(Expression e) {
	if (auto ty=cast(Type)e) {
		return ty;
	}
	if (auto aggrTy=isDataTyId(e)) {
		return aggrTy;
	}
	return null;
}

static if (language==dp) Expression parameterSetTyIndexSemantic(IndexExp idx, ParameterSetTy paramTy, Expression[] args, Scope sc) {
	bool isValidBoundType(Expression bound) {
		if (auto id=cast(Identifier)bound) {
			// TODO: this is hack, we need some common supertype for all things parameterized
			return id.type.isTypeTy;
		}
		// can only specialize param types using record types
		return (cast(AggregateTy)typeOrDataType(bound)) !is null;
	}
	bool isValidBoundValue(Expression bound) {
		// can only specialize param types using records or references to initialized functions
		auto type = bound.type;
		if (auto ftype=cast(FunTy)type) {
			return ftype.isParameterized&&ftype.isInitialized;
		} else {
			return isValidBoundType(type);
		}
	}
	if (args.length != 1) {
		sc.error("parameter set types can only be specialized using a single type argument", idx.loc);
		idx.sstate = SemState.error;
		return idx;
	}
	if (paramTy.isValueBound) {
		sc.error(text("cannot specialize value-bound parameter set type ", paramTy, " any further"), idx.loc);
		idx.sstate = SemState.error;
		return idx;
	}
	auto typeBound = paramTy.target;
	auto newBound = expressionSemantic(args[0],sc,ConstResult.yes);
	// ignore errorneous index expressions 
	if (newBound.sstate==SemState.error) {
		return paramTy;
	}
	if (newBound.type.isTypeTy) { // new bound is type bound
		if (!isValidBoundType(newBound)) {
			sc.error(text("parameter set type ", paramTy, " can only be specialized using record types, initialized functions or records, not ", newBound), idx.loc);
			idx.sstate = SemState.error;
			return idx;
		}
		if (!isSubtype(newBound, typeBound)) {
			sc.error(text("parameter set type ", paramTy, " cannot be specialized with incompatible type ", newBound), idx.loc);
			idx.sstate = SemState.error;
			return idx;
		}
		return parameterSetTy(newBound, paramTy.sc);
	} else { // new bound is value bound
		if (!isValidBoundValue(newBound)) {
			sc.error(text("parameter set type ", paramTy, " can only be specialized using record types, initialized functions or records, not ", newBound), idx.loc);
			idx.sstate = SemState.error;
			return idx;
		}
		if (!isSubtype(newBound.type, typeBound)) {
			sc.error(text("parameter set type ", paramTy, " can only be specialized by expressions of type ", typeBound, ", not ", newBound.type), idx.loc);
			idx.sstate = SemState.error;
			return idx;
		}
		return parameterSetTy(newBound, paramTy.sc);
	}
	return idx;
}

static if (language==dp) Expression parameterSetIndexSemantic(IndexExp idx, Expression[] args, Scope sc) {
	if (args.length < 1) {
		sc.error("a parameter set expression must be indexed by a parameter declaration", idx.loc);
		idx.sstate = SemState.error;
		return idx;
	}
	if (args.length > 2) {
		sc.error("too many index arguments for a parameter set expression", idx.loc);
		idx.sstate = SemState.error;
		return idx;
	}
	// determine parameter name from first index argument
	auto paramRefExpression = expressionSemantic(args[0], sc, ConstResult.yes);
	if (!isSubtype(paramRefExpression.type, stringTy)) {
		sc.error(text("parameters in parameter sets must always be addressed by strings, not ", paramRefExpression.type), paramRefExpression.loc);
		idx.sstate = SemState.error;
		return idx;
	}

	Expression context=null;
	// if provided, handle parameter context expression
	if (args.length == 2) {
		context=expressionSemantic(args[1],sc,ConstResult.yes);
		if (!(isSubtype(context.type, ℕt) || isSubtype(context.type, stringTy))) {
			sc.error(format("parameter context must be a natural number or string not %s", context.type.toString()),context.loc);
			context.sstate=SemState.error;
			return idx;
		}
	}

	return new ParameterSetIndexExp(idx.e, paramRefExpression, context);
}

static if (language==dp) Expression manifoldMemberSemantic(Expression target, string memberName, Scope sc) {
	if (!["move", "tangentVector", "tangentZero"].any!(n => n == memberName)) {
		return null;
	}
	
	Expression resolveLocally(Expression target, Expression targetType, string memberName) {
		if(ManifoldDecl manifoldDecl=sc.getManifoldDecl()) { // check if we are in manifold decl)
			auto ident = cast(Identifier)manifoldDecl.typeName;
			bool identMatch = ident&&ident.name==targetType.toString;
			bool directMatch = manifoldDecl.typeName==targetType;
			bool aggrTyMatch = false;
			
			auto targetAsIdent=cast(Identifier)target;
			if (targetAsIdent&&target.type.isTypeTy) {
				auto declName = targetAsIdent.meaning.name;
				aggrTyMatch = ident&&declName.name==ident.name;
			}

			if (identMatch||directMatch) {
				if (memberName == "tangentVector") {
					assert(!!manifoldDecl.tangentVecExp, text("manifold declaration ", manifoldDecl.name, " is missing a tangent vector declaration"));
					return manifoldDecl.tangentVecExp=expressionSemantic(manifoldDecl.tangentVecExp, sc, ConstResult.yes);
				} else if (memberName == "tangentZero"||memberName == "move") {
					assert(!!manifoldDecl.tangentZeroDef, text("manifold declaration ", manifoldDecl.name, " is missing a tangentZero definition"));
					assert(!!manifoldDecl.moveOpDef, text("manifold declaration ", manifoldDecl.name, " is missing a move definition"));
					FunctionDef opDef;
					if (memberName=="tangentZero") {
						opDef = manifoldDecl.tangentZeroDef=functionDefSemantic(manifoldDecl.tangentZeroDef, sc);
					} else if (memberName=="move") {
						opDef = manifoldDecl.moveOpDef=functionDefSemantic(manifoldDecl.moveOpDef, sc);
					}

					auto id = new Identifier(memberName);
					id.meaning = opDef;
					auto fe = new FieldExp(target, id);
					fe.type = opDef.ftype.substitute(["this": target]);
					return fe;
				}
			}
		}
		return null;
	}

	// standard case (direct manifold declaration for target type)
	if (auto targetType=typeOrDataType(target.type)) {
		// check for type-level access (e.g. ℝ.tangentVector)
		if (targetType.isTypeTy) {
			// type-level access only exposes the .tangentVector member
			if (memberName!="tangentVector") return null;

			// check for recursive access (e.g. ℝ.tangentVector in manifold declaration for ℝ)
			if (auto res=resolveLocally(target, target, memberName)) {
				return res;
			}

			// handle direct type references
			if (auto tv = target.tangentVecTy(sc)) {	
				if (memberName == "tangentVector") 
					return tangentVectorTy(target, sc);
			}
		}

		// check for value-level recursive access (e.g. 1.0.tangentVector in manifold declaration for ℝ)
		if (auto res=resolveLocally(target, targetType, memberName)) {
			return res;
		}

		// check for value-level access (e.g. (1.0).tangentVector)
		if (auto manifoldImpl=targetType.manifold(sc)) {
			if (memberName == "move") {
				auto id = new Identifier(memberName);
				id.meaning = manifoldImpl.moveOpDef;
				auto fe = new FieldExp(target, id);
				fe.type = manifoldImpl.moveOpDef.ftype.substitute(["this": target]);
				return fe;
			} else if (memberName == "tangentVector") {
				return tangentVectorTy(target, sc).substitute(["this": target]);
			} else if (memberName == "tangentZero") {
				auto id = new Identifier(memberName);
				id.meaning = manifoldImpl.tangentZeroDef;
				auto fe = new FieldExp(target, id);
				fe.type = manifoldImpl.tangentZeroDef.ftype.substitute(["this": target]);
				return fe;
			}
		}
	}

	// special case: type of target expression is type variable
	if (auto typeVar=cast(Identifier)target.type) {
		if (cast(ManifoldTypeTy)typeVar.type) {
			auto tv = typeVar.tangentVecTy(sc);
			if (memberName=="tangentVector") {
				return tv;
			} else {
				// other manifold members need to be resolved dynamically at runtime
				auto fe = new FieldExp(target, new Identifier(memberName));
				if (memberName == "tangentZero") {
					fe.type=productTy([], [], unit, tangentVectorTy(target, sc), false, true, Annotation.none, true);
				} else if (memberName == "move") {
					fe.type=productTy([true], ["along"], tangentVectorTy(target, sc), unit, false, false, Annotation.none, true);
				} else {
					assert(false, "invalid manifold member name " ~ memberName);
				}
				return fe;
			}
		}
	}

	// special case: AggrTy instances as manifolds
	if (auto aggrTy=isDataTyId(target.type)) {
		if (aggrTy.isParameterized) {
			// TODO: think about whether this can be done in AggregateTy
			auto paramExp = new ParameterSetHandleExp(target);
			return expressionSemantic(new FieldExp(paramExp, new Identifier(memberName)), sc, ConstResult.no);
		}
	}
	// special case: direct AggrTy references (A.tangentVector)
	if (auto aggrTy=isDataTyId(target)) {
		// check for recursive access (e.g. ℝ.tangentVector in manifold declaration for ℝ)
		if (auto res=resolveLocally(target, aggrTy, memberName)) {
			return res;
		}
		if (aggrTy.isParameterized) {
			// TODO: think about whether this can be done in AggregateTy
			auto paramExp = parameterSetTy(target, sc);
			return expressionSemantic(new FieldExp(paramExp, new Identifier(memberName)), sc, ConstResult.no);
		}
	}
	// special case: initialised functions as manifolds
	if (auto funTy=cast(FunTy)target.type) {
		if (funTy.isParameterized && funTy.isInitialized) {
			// TODO: think about whether this can be done in ProductTy
			auto paramExp = new ParameterSetHandleExp(target);
			return expressionSemantic(new FieldExp(paramExp, new Identifier(memberName)), sc, ConstResult.no);
		}
	}
	return null;
}

// traverses the tree of BinaryExp at shapeExpression and 
// returns a flat list of Expressions
Expression[] findDimExprs(Expression shapeExpression, Scope sc) {
	if (auto binExp = cast(BinaryExp!(Tok!"×"))shapeExpression) {
		return findDimExprs(binExp.e1, sc) ~ [binExp.e2];
	} else {
		return [shapeExpression];
	}
}

bool setFtype(FunctionDef fd){
	if(fd.ftype) return true;
	if(!fd.ret) return false;

	bool[] pc;
	string[] pn;
	Expression[] pty;
	foreach(p;fd.params){
		if(!p.vtype){
			assert(fd.sstate==SemState.error);
			return false;
		}
		pc~=p.isConst;
		pn~=p.getName;
		pty~=p.vtype;
	}
	assert(fd.isTuple||pty.length==1);
	auto pt=fd.isTuple?tupleTy(pty):pty[0];

	if (language==dp) {
		// propagate 'nondiff' property of innermost function upwards in the case of higher-order functions
		auto retFun = cast(FunTy)fd.ret;
		bool returnTypeIsNonDifferentiableFunction=retFun&&!retFun.isDifferentiable;
		bool isDifferentiable = fd.isDifferentiable&&!returnTypeIsNonDifferentiableFunction;

		// lambdas are always initialised, top-level function defs are not
		bool isInitialized = fd.isExplicitLambda;

		fd.ftype=productTy(pc,pn,pt,fd.ret,fd.isSquare,fd.isTuple,
							fd.annotation,!fd.context||fd.context.vtype==contextTy(true), 
							!fd.isSquare&&fd.isParameterized, isInitialized, isDifferentiable);
		fd.isDifferentiable = isDifferentiable;
	} else {
		fd.ftype=productTy(pc,pn,pt,fd.ret,fd.isSquare,fd.isTuple,
							fd.annotation,!fd.context||fd.context.vtype==contextTy(true));
	}

	assert(fd.retNames==[]);
	if(!fd.retNames) fd.retNames = new string[](fd.numReturns);
	assert(fd.fscope_||fd.sstate==SemState.error);
	foreach(callback;fd.ftypeCallbacks)
		callback(fd.ftype);
	fd.ftypeCallbacks=[];
	return true;
}
FunctionDef functionDefSemantic(FunctionDef fd,Scope sc){
	assert(fd, "functionDef must not be null");
	if(fd.sstate==SemState.completed) return fd;
	if(!fd.fscope_) fd=cast(FunctionDef)presemantic(fd,sc); // TODO: why does checking for fd.scope_ not work? (test3.slq)
	auto fsc=fd.fscope_;
	++fd.semanticDepth;
	assert(!!fsc,text(fd));
	assert(fsc.allowsLinear());
	auto bdy=fd.body_?compoundExpSemantic(fd.body_,fsc):null;
	scope(exit){
		static if(language==silq) fsc.pushConsumed();
		if(fd.sstate==SemState.completed){
			foreach(id;fd.ftype.freeIdentifiers){
				// allow free varTy's w/o .meaning (may occur during subtype checking of synthesized manifold members)
				if (id.meaning is null && varTy(id.name, id.type) == id) continue;
				assert(!!id.meaning);
				if(cast(DatDecl)id.meaning) continue; // allow nested types to be returned from functions
				if(id.meaning.scope_.isNestedIn(fsc)){
					fsc.error(format("local variable '%s' appears in function return type", id.name), fd.loc);
					fd.sstate=SemState.error;
				}
				typeConstBlock(id.meaning,fd,sc);
			}
		}
		if(bdy){
			if(--fd.semanticDepth==0&&(fsc.merge(false,bdy.blscope_)||fsc.close())) fd.sstate=SemState.error;
		}else{
			fsc.forceClose();
		}
	}
	fd.body_=bdy;
	fd.type=unit;
	if(bdy){
		propErr(bdy,fd);
		if(!definitelyReturns(bdy)){
			if(!fd.ret || fd.ret == unit){
				auto tpl=new TupleExp([]);
				tpl.loc=fd.loc;
				auto rete=new ReturnExp(tpl);
				rete.loc=fd.loc;
				fd.body_.s~=returnExpSemantic(rete,fd.body_.blscope_);
			}else{
				sc.error("control flow might reach end of function (add return or assert(false) statement)",fd.loc);
				fd.sstate=SemState.error;
			}
		}
	}
	if(!fd.ret) fd.ret=unit; // TODO: add bottom type
	setFtype(fd);
	foreach(ref n;fd.retNames){
		if(n is null) n="r";
		else n=n.stripRight('\'');
	}
	void[0][string] vars;
	foreach(p;fd.params) vars[p.getName]=[];
	int[string] counts1,counts2;
	foreach(n;fd.retNames)
		++counts1[n];
	foreach(ref n;fd.retNames){
		if(counts1[n]>1)
			n~=lowNum(++counts2[n]);
		while(n in vars) n~="'";
		vars[n]=[];
	}
	static if(language==dp) {
		// check for captured initialized functions
		long numberOfCapturedInitializedFunctions = 0;
		foreach(id; fd.captures) {
			if (auto ftype=cast(FunTy)id.type) {
				if (ftype.isInitialized) numberOfCapturedInitializedFunctions += 1;
			}
		}
		if (numberOfCapturedInitializedFunctions>0&&!fd.isParameterized) {
			sc.note("gradients of captured initialized functions will be lost when differentiating, declare function as param to capture gradients", fd.loc);
		}

		// check for main function
		if (fd.name&&fd.name.name=="main") {
			if (fd.isParameterized) {
				sc.error("the main function cannot be parameterized (annotate as noparam def main)", fd.loc);
				return fd;
			}
		}
		
		// check for pullbacks
		if (fd.isPullback) {
			fd=pullbackSemantic(fd, sc);
		}
	}

	if(fd.sstate!=SemState.error)
		fd.sstate=SemState.completed;
	return fd;
}

bool linkAdjointPrimalFunctionDef(FunctionDef primal, FunctionDef adjoint) {
	while (primal&&adjoint) {
		// establish linking of functions
		adjoint.primal = primal;
		primal.adjoint = adjoint;

		// establish linking among all contained squared functions
		if (primal.isSquare) {
			primal = getSquareLambdaDelegate(primal);
			adjoint = getSquareLambdaDelegate(adjoint);
		} else {
			break;
		}
	}
	auto lastAdjointDelegate = getSquareLambdaDelegate(adjoint);
	return lastAdjointDelegate&&!lastAdjointDelegate.isSquare;
}

static if(language==dp) FunctionDef pullbackSemantic(FunctionDef fd, Scope sc) {
	assert(fd.isPullback);
	assert(fd.primalName !is null);
	assert(!fd.isDifferentiable, "pullbacks must not be declared differentiable");
	assert(!fd.isParameterized, "pullbacks must not be parameterized");

	FunctionDef primal = cast(FunctionDef)sc.lookup(fd.primalName,false,false,Lookup.probing);
	if (!primal) {
		sc.error(format("failed to resolve primal function %s", fd.primalName.toString), fd.name.loc);
		fd.sstate=SemState.error;
		return fd;
	}

	if (!primal.isDifferentiable) {
		sc.error(format("cannot define pullback for nondiff-annotated function %s.", 
			fd.primalName.toString), fd.loc);	
		return fd;
	}

	if (primal.isParameterized) {
		sc.error(format("cannot define explicit pullback for parameterized function (declare %s as noparam).", 
			fd.primalName.toString), fd.loc);	
		return fd;
	}

	// establish linking of functions
	auto linkSuccess = linkAdjointPrimalFunctionDef(functionDefSemantic(primal, sc), fd);
	if (!linkSuccess) {
		sc.error(format("internal error: failed to link pullback and primal functions for function %s", primal.name), primal.loc);
		return fd;
	}

	// check pullback ftype
	ProductTy pty = pullbackTy(primal, sc);
	if (!pty) {
		sc.error(format("failed to determine pullback signature for function %s with signature %s.", 
			fd.primalName.toString, primal), fd.loc);	
		return fd;
	}
	ProductTy fty = fd.ftype;

	// check pullback signature
	if (!isSubtype(fty, pty) || !isSubtype(pty, fty)) {
		sc.error(format("pullback for function %s requires signature %s not %s.", 
			fd.primalName.toString, pty.toString, fd.ftype.toString), fd.loc);	
		fd.sstate=SemState.error;
		return fd;
	}

	return fd;
}

DatDecl datDeclSemantic(DatDecl dat,Scope sc){
	bool success=true;
	if(!dat.dscope_) presemantic(dat,sc);
	auto bdy=compoundDeclSemantic(dat.body_,dat.dscope_);
	assert(!!bdy);
	dat.body_=bdy;
	dat.type=unit;
	return dat;
}

static if (language==dp) ManifoldDecl manifoldDeclSemantic(ManifoldDecl maniDecl, Scope sc){
	if (maniDecl.sstate == SemState.completed) return maniDecl;

	if(maniDecl.sstate == SemState.raw) {
		auto topScope = findTopMostScope(sc);
		maniDecl = manifoldDeclPresemantic(maniDecl, topScope);
	}

	if (maniDecl.sstate == SemState.error) {
		return maniDecl;
	}

	if (maniDecl.sstate == SemState.started) {
		sc.error("cyclic dependency on manifold declaration", maniDecl.loc);
		maniDecl.sstate = SemState.error;
		return maniDecl;
	}

	maniDecl.sstate = SemState.started;

	Type tangentVecTy = null;
	Type elementType = null;
	FunctionDef tangentZeroDef = null;
	
	// check correct resolution of manifold type
	auto const MANIFOLD_TYPE_ERROR_MSG = "manifold type must be an existing built-in or record type.";
	int nerr=sc.handler.nerrors; // TODO: this is a bit hacky
	auto typeRef = expressionSemantic(maniDecl.typeName, sc, ConstResult.yes);
	if(nerr!=sc.handler.nerrors){
		sc.note(MANIFOLD_TYPE_ERROR_MSG,maniDecl.typeName.loc);
		maniDecl.sstate = SemState.error;
		return maniDecl;
	}

	auto typeRefAsIdentifier = cast(Identifier)typeRef;
	auto typeRefAsType = cast(Type)typeRef;

	if (typeRefAsType) {
		elementType = typeRefAsType;
	} else if (auto datDecl = cast(DatDecl)(typeRefAsIdentifier ? typeRefAsIdentifier.meaning : null)) {
		elementType = datDecl.dtype;
	} else if (typeRef.sstate != SemState.error) {
		sc.error(MANIFOLD_TYPE_ERROR_MSG, maniDecl.typeName.loc);
		maniDecl.sstate = SemState.error;
		return maniDecl;
	}

	// globally flag type as manifold
	elementType.flagAsManifoldType();

	// type check tangent vector declaration
	if (auto tangentVectorExp=maniDecl.tangentVecExp) {
		tangentVecTy = typeOrDataType(typeSemantic(tangentVectorExp, maniDecl.declScope));
		if (tangentVecTy is null) {
			sc.error("manifold tangent vector must be a type", tangentVectorExp.loc);
			tangentVectorExp.sstate = SemState.error;
		}

		// check for minimal tangent vector arithmetic capabilities
		if (arithmeticType!(true)(tangentVecTy, tangentVecTy) is null) {
			sc.note("manifold tangent vectors which do not support addition may not be supported by automatic differentiation", tangentVectorExp.loc);
		} 
		if (arithmeticType!(true)(tangentVecTy, ℝ(true)) is null) {
			sc.note("manifold tangent vectors which do not support scalar multiplication may not be supported by automatic differentiation", tangentVectorExp.loc);
		}
	}
	// type check tangent zero declaration
	if ((tangentZeroDef=maniDecl.tangentZeroDef) !is null) {
		tangentZeroDef = functionDefSemantic(tangentZeroDef, maniDecl.declScope);
		if (tangentVecTy !is null) {	
			auto tangentZeroTy = productTy([], [], unit, tangentVecTy, false, true, Annotation.none, true);
			if (!isSubtype(tangentZeroDef.ftype, tangentZeroTy)) {
				sc.error(format("manifold tangentZero must be of type %s not %s", 
					tangentZeroTy.toString(), tangentZeroDef.ftype.toString()), tangentZeroDef.loc);
				maniDecl.sstate = SemState.error;
				return maniDecl;
			}
		}
	}
	// type check move operation signature and bind 'this' in move's function scope
	if (auto moveOpDef = maniDecl.moveOpDef) {
		if (tangentVecTy !is null)  {
			maniDecl.moveOpDef = manifoldMoveOpSemantic(moveOpDef, elementType, tangentVecTy, maniDecl.declScope);
		}
	}

	maniDecl.type = unit;
	maniDecl.mtype = new Manifold(elementType, maniDecl.moveOpDef, tangentVecTy, tangentZeroDef);
	maniDecl.mtype.manifoldDecl = maniDecl;

	if(maniDecl.sstate!=SemState.error)
		maniDecl.sstate=SemState.completed;

	return maniDecl;
}

static if (language==dp) FunctionDef manifoldMoveOpSemantic(FunctionDef moveOpDef, Type elementType, Type tangentVecTy, Scope sc) {
	auto moveOpTy = productTy([true], ["along"], tangentVecTy, unit, false, false, Annotation.none, true);
	
	moveOpDef.isManifoldOp = true;
	assert(!!moveOpDef.thisVar, "manifold move operation is missing thisVar");
	moveOpDef = functionDefSemantic(moveOpDef, sc);

	if (!isSubtype(moveOpDef.ftype, moveOpTy)) {
		sc.error(format("manifold move operation %s does not conform to required signature %s", moveOpDef.ftype, moveOpTy.toString()), moveOpDef.loc);
		moveOpDef.sstate = SemState.error;
	}

	return moveOpDef;
}

static if (language==dp) ManifoldDecl manifoldDeclPresemantic(ManifoldDecl maniDecl, Scope sc){
	if (maniDecl.sstate!=SemState.raw) return maniDecl;

	bool success=true;

	auto bdy = maniDecl.body_;
	auto declScope = new ManifoldDeclScope(sc, maniDecl);

	FunctionDef[Identifier] manifoldOpDefs;

	Expression[] tangentVectorExps = [];
	FunctionDef[] tangentZeroDecls = [];
	FunctionDef[] moveOpDecls = [];

	// collect operation definitions and pick-up tangentVector type definition
	foreach(ref e;bdy.s){
		if (auto funDef = cast(FunctionDef) e) {
			manifoldOpDefs[funDef.name] = funDef;
			if (funDef.name.name == "move") {
				// manifold members must always be non-parameterized
				funDef.isParameterized = false;
				funDef.isDifferentiable = false;
				moveOpDecls ~= funDef;
			} else if (funDef.name.name == "tangentZero") {
				// manifold members must always be non-parameterized
				funDef.isParameterized = false;
				funDef.isDifferentiable = false;
				tangentZeroDecls ~= funDef;
			} else {
				sc.error(text("not supported in manifold declaration ", e.toString, " (", typeid(e), ")"),e.loc);
			}
		} else if (auto defExp = cast(DefineExp) e) {
			e = makeDeclaration(defExp, success, declScope);
			auto singleDef = cast(SingleDefExp)e;
			if (!singleDef) {
				sc.error(text("not supported in manifold declaration ", e.toString, " (", typeid(e), ")"),e.loc);
				maniDecl.sstate = SemState.error;
			}
			auto name = singleDef.decl.name.name;
			if (name == "tangentVector") {
				tangentVectorExps ~= singleDef.initializer.e2;
			} else {
				sc.error(format("not a valid manifold property %s", name), e.loc);
				maniDecl.sstate = SemState.error;
			}
		} else {
			sc.error(text("not supported in manifold declaration ", e.toString, " (", typeid(e), ")"),e.loc);
			maniDecl.sstate = SemState.error;
		}
		propErr(e,bdy);
	}
	// check type and presence of manifold declarations
	if (tangentVectorExps.empty) {
		sc.error("manifold is missing a tangentVector type declaration", maniDecl.loc);
		maniDecl.sstate = SemState.error;
		return maniDecl;
	}
	if (tangentZeroDecls.empty) {
		sc.error("manifold is missing a tangentZero declaration", maniDecl.loc);
		maniDecl.sstate = SemState.error;
		return maniDecl;
	}
	if (moveOpDecls.empty) {
		sc.error("manifold is missing a move operation", maniDecl.loc);
		maniDecl.sstate = SemState.error;
		return maniDecl;
	}
	
	bdy.type=unit;
	maniDecl.body_=bdy;
	maniDecl.type=unit;
	maniDecl.declScope = declScope;
	
	// initialise additional properties based on new information
	maniDecl.tangentVecExp = tangentVectorExps.empty ? null : tangentVectorExps[0];
	// trigger presemantic processing of operation definitions
	maniDecl.moveOpDef = moveOpDecls.empty ? null : cast(FunctionDef)presemantic(moveOpDecls[0], declScope);
	maniDecl.tangentZeroDef = tangentZeroDecls.empty ? null : cast(FunctionDef)presemantic(tangentZeroDecls[0], declScope);

	if (maniDecl.sstate != SemState.error)
		maniDecl.sstate = SemState.presemantic;

	return maniDecl;
}

void determineType(ref Expression e,Scope sc,void delegate(Expression) future){
	if(e.type) return future(e.type);
	if(auto le=cast(LambdaExp)e){
		assert(!!le.fd);
		if(!le.fd.scope_){
			le.fd.scope_=sc;
			le.fd=cast(FunctionDef)presemantic(le.fd,sc);
			assert(!!le.fd);
		}
		if(auto ty=le.fd.ftype)
			return future(ty);
		le.fd.ftypeCallbacks~=future;
		return;
	}
	e=expressionSemantic(e,sc,ConstResult.no);
	return future(e.type);
}

ReturnExp returnExpSemantic(ReturnExp ret,Scope sc){
	if(ret.sstate==SemState.completed) return ret;
	ret.scope_=sc;
	auto fd=sc.getFunction();
	if(!fd){
		sc.error("return statement must be within function",ret.loc);
		ret.sstate=SemState.error;
		return ret;
	}
	if(!fd.rret && !fd.ret){
		determineType(ret.e,sc,(ty){
			fd.ret=ty;
			setFtype(fd);
		});
	}
	ret.e=expressionSemantic(ret.e,sc,ConstResult.no);
	propErr(ret.e,ret);
	if(cast(CommaExp)ret.e){
		sc.error("use parentheses for multiple return values",ret.e.loc);
		ret.sstate=SemState.error;
	}
	static if(language==silq){
		auto bottom=Dependency(false,SetX!string.init); // variable is a workaround for DMD regression
		if(ret.e.type&&ret.e.type.isClassical()&&sc.controlDependency!=bottom){
			sc.error("cannot return quantum-controlled classical value",ret.e.loc); // TODO: automatically promote to quantum?
			ret.sstate=SemState.error;
		}
	}
	if(ret.sstate==SemState.error)
		return ret;
	static if(language==silq) sc.pushConsumed();
	if(sc.close()){
		sc.note("at function return",ret.loc);
		ret.sstate=SemState.error;
		return ret;
	}
	if(!isSubtype(ret.e.type,fd.ret)){
		sc.error(format("%s is incompatible with return type %s",ret.e.type,fd.ret),ret.e.loc);
		ret.sstate=SemState.error;
		return ret;
	}
	ret.type=unit;
	Expression[] returns;
	if(auto tpl=cast(TupleExp)ret.e) returns=tpl.e;
	else returns = [ret.e];
	static string getName(Expression e){
		string candidate(Expression e,bool allowNum=false){
			if(auto id=cast(Identifier)e) return id.name;
			if(auto fe=cast(FieldExp)e) return fe.f.name;
			if(auto ie=cast(IndexExp)e){
				auto idx=candidate(ie.a[0],true);
				if(!idx) idx="i";
				auto low=toLow(idx);
				if(!low) low="_"~idx;
				auto a=candidate(ie.e);
				if(!a) return null;
				return a~low;
			}
			if(allowNum){
				if(auto le=cast(LiteralExp)e){
					if(le.lit.type==Tok!"0")
						return le.lit.str;
				}
			}
			return null;
		}
		auto r=candidate(e);
		if(util.among(r.stripRight('\''),"delta","sum","abs","log","lim","val","⊥","case","e","π","pi")) return null;
		return r;
	}
	if(returns.length==fd.retNames.length){
		foreach(i,e;returns)
			if(auto n=getName(e)) fd.retNames[i]=n;
	}else if(returns.length==1){
		if(auto name=getName(returns[0]))
			foreach(ref n;fd.retNames) n=name;
	}
	return ret;
}


Expression typeSemantic(Expression expr,Scope sc)in{assert(!!expr&&!!sc);}body{
	if(expr.type==typeTy) return expr;
	if(auto lit=cast(LiteralExp)expr){
		lit.type=typeTy;
		if(lit.lit.type==Tok!"0"){
			if(lit.lit.str=="1")
				return unit;
		}
	}
	auto at=cast(IndexExp)expr;
	if(at&&at.a==[]){
		expr.type=typeTy;
		auto next=typeSemantic(at.e,sc);
		propErr(at.e,expr);
		if(!next) return null;
		return arrayTy(next);
	}
	auto e=expressionSemantic(expr,sc,ConstResult.no);
	if(!e) return null;
	static if(language==dp) if(e.type==noGradTy) return noGradTy;
	if(e.type.isTypeTy) return e;
	if(expr.sstate!=SemState.error){
		auto id=cast(Identifier)expr;
		if(id&&id.meaning){
			auto decl=id.meaning;
			sc.error(format("%s %s is not a type",decl.kind,decl.name),id.loc);
			sc.note("declared here",decl.loc);
		}else sc.error("not a type",expr.loc);
		expr.sstate=SemState.error;
	}
	return null;
 }

Expression typeForDecl(Declaration decl){
	if(auto dat=cast(DatDecl)decl){
		if(!dat.dtype&&dat.scope_) dat=cast(DatDecl)presemantic(dat,dat.scope_);
		assert(cast(AggregateTy)dat.dtype);
		if(!dat.hasParams) return typeTy;
		foreach(p;dat.params) if(!p.vtype) return unit; // TODO: ok?
		assert(dat.isTuple||dat.params.length==1);
		auto pt=dat.isTuple?tupleTy(dat.params.map!(p=>p.vtype).array):dat.params[0].vtype;
		return productTy(dat.params.map!(p=>p.isConst).array,dat.params.map!(p=>p.getName).array,pt,typeTy,true,dat.isTuple,Annotation.qfree,true);
	}
	if(auto vd=cast(VarDecl)decl){
		return vd.vtype;
	}
	if(auto fd=cast(FunctionDef)decl){
		if(!fd.ftype&&fd.scope_) fd=functionDefSemantic(fd,fd.scope_);
		assert(!!fd);
		return fd.ftype;
	}
	return unit; // TODO
}

bool definitelyReturns(Expression e){
	if(auto ret=cast(ReturnExp)e)
		return true;
	bool isZero(Expression e){
		if(auto tae=cast(TypeAnnotationExp)e)
			return isZero(tae.e);
		if(auto le=cast(LiteralExp)e)
			if(le.lit.type==Tok!"0")
				if(le.lit.str=="0")
					return true;
		return false;
	}
	alias isFalse=isZero;
	bool isTrue(Expression e){
		if(auto le=cast(LiteralExp)e)
			if(le.lit.type==Tok!"0")
				return le.lit.str!="0";
		return false;
	}
	bool isPositive(Expression e){
		if(isZero(e)) return false;
		if(auto le=cast(LiteralExp)e)
			if(le.lit.type==Tok!"0")
				return le.lit.str[0]!='-';
		return false;
		}
	if(auto ae=cast(AssertExp)e)
		return isFalse(ae.e);
	if(auto oe=cast(ObserveExp)e)
		return isFalse(oe.e);
	if(auto ce=cast(CompoundExp)e)
		return ce.s.any!(x=>definitelyReturns(x));
	if(auto ite=cast(IteExp)e)
		return definitelyReturns(ite.then) && definitelyReturns(ite.othw);
	if(auto fe=cast(ForExp)e){
		/+auto lle=cast(LiteralExp)fe.left;
		auto rle=cast(LiteralExp)fe.right;
		if(lle && rle && lle.lit.type==Tok!"0" && rle.lit.type==Tok!"0"){ // TODO: parse values correctly
			ℤ l=ℤ(lle.lit.str), r=ℤ(rle.lit.str);
			l+=cast(long)fe.leftExclusive;
			r-=cast(long)fe.rightExclusive;
			return l<=r && definitelyReturns(fe.bdy);
		}+/
		return false;
	}
	if(auto we=cast(WhileExp)e)
		return isTrue(we.cond) && definitelyReturns(we.bdy);
	if(auto re=cast(RepeatExp)e)
		return isPositive(re.num) && definitelyReturns(re.bdy);
	return false;
}

static if(language==psi){
import dexpr;
struct VarMapping{
	DNVar orig;
	DNVar tmp;
}
struct SampleFromInfo{
	bool error;
	VarMapping[] retVars;
	DNVar[] paramVars;
	DExpr newDist;
}

import distrib; // TODO: separate concerns properly, move the relevant parts back to analysis.d
SampleFromInfo analyzeSampleFrom(CallExp ce,ErrorHandler err,Distribution dist=null){ // TODO: support for non-real-valued distributions
	Expression[] args;
	if(auto tpl=cast(TupleExp)ce.arg) args=tpl.e;
	else args=[ce.arg];
	if(args.length==0){
		err.error("expected arguments to sampleFrom",ce.loc);
		return SampleFromInfo(true);
	}
	auto literal=cast(LiteralExp)args[0];
	if(!literal||literal.lit.type!=Tok!"``"){
		err.error("first argument to sampleFrom must be string literal",args[0].loc);
		return SampleFromInfo(true);
	}
	VarMapping[] retVars;
	DNVar[] paramVars;
	DExpr newDist;
	import util.hashtable;
	HSet!(string,(a,b)=>a==b,a=>typeid(string).getHash(&a)) names;
	try{
		import dparse;
		auto parser=DParser(literal.lit.str);
		parser.skipWhitespace();
		parser.expect('(');
		for(bool seen=false;parser.cur()!=')';){
			parser.skipWhitespace();
			if(parser.cur()==';'){
				seen=true;
				parser.next();
				continue;
			}
			auto orig=cast(DNVar)parser.parseDVar();
			if(!orig) throw new Exception("TODO");
			if(orig.name in names){
				err.error(text("multiple variables of name \"",orig.name,"\""),args[0].loc);
				return SampleFromInfo(true);
			}
			if(!seen){
				auto tmp=dist?dist.getTmpVar("__tmp"~orig.name):null; // TODO: this is a hack
				retVars~=VarMapping(orig,tmp);
			}else paramVars~=orig;
			parser.skipWhitespace();
			if(!";)"[seen..$].canFind(parser.cur())) parser.expect(',');
		}
		parser.next();
		parser.skipWhitespace();
		if(parser.cur()=='⇒') parser.next();
		else{ parser.expect('='); parser.expect('>'); }
		parser.skipWhitespace();
		newDist=parser.parseDExpr();
	}catch(Exception e){
		err.error(e.msg,args[0].loc);
		return SampleFromInfo(true);
	}
	if(dist){
		foreach(var;retVars){
			if(!newDist.hasFreeVar(var.orig)){
				err.error(text("pdf must depend on variable ",var.orig.name,")"),args[0].loc);
				return SampleFromInfo(true);
			}
		}
		newDist=newDist.substituteAll(retVars.map!(x=>cast(DVar)x.orig).array,retVars.map!(x=>cast(DExpr)x.tmp).array);
	}
	if(args.length!=1+paramVars.length){
		err.error(text("expected ",paramVars.length," additional arguments to sampleFrom"),ce.loc);
		return SampleFromInfo(true);
	}
	return SampleFromInfo(false,retVars,paramVars,newDist);
}

Expression handleSampleFrom(CallExp ce,Scope sc){
	auto info=analyzeSampleFrom(ce,sc.handler);
	if(info.error){
		ce.sstate=SemState.error;
	}else{
		 // TODO: this special casing is not very nice:
		ce.type=info.retVars.length==1?ℝ(true):tupleTy((cast(Expression)ℝ(true)).repeat(info.retVars.length).array);
	}
	if(auto tpl=cast(TupleExp)ce.arg){
		foreach(ref arg;tpl.e[1..$]){
			arg=expressionSemantic(arg,sc,ConstResult.yes);
			propErr(arg,ce.arg);
		}
	}
	propErr(ce.arg,ce);
	return ce;
}
}else static if(language==silq){

string getQuantumOp(Expression qpArg){
	auto opExp=qpArg;
	if(auto tpl=cast(TupleExp)opExp){
		enforce(tpl.e.length==1);
		opExp=tpl.e[0];
	}
	auto opLit=cast(LiteralExp)opExp;
	enforce(!!opLit&&opLit.lit.type==Tok!"``");
	return opLit.lit.str;
}
Expression handleQuantumPrimitive(CallExp ce,Scope sc){
	Expression[] args;
	if(auto tpl=cast(TupleExp)ce.arg) args=tpl.e;
	else args=[ce.arg];
	if(args.length==0){
		sc.error("expected argument to quantumPrimitive",ce.loc);
		ce.sstate=SemState.error;
		return ce;
	}
	auto literal=cast(LiteralExp)args[0];
	if(!literal||literal.lit.type!=Tok!"``"){
		sc.error("first argument to quantumPrimitive must be string literal",args[0].loc);
		ce.sstate=SemState.error;
		return ce;
	}
	auto op=literal.lit.str;
	switch(op){
		case "dup":
			ce.type = productTy([true],["`τ"],typeTy,funTy([true],varTy("`τ",typeTy),varTy("`τ",typeTy),false,false,Annotation.qfree,true),true,false,Annotation.qfree,true);
			break;
		case "array":
			ce.type = productTy([true],["`τ"],typeTy,funTy([true,true],tupleTy([ℕt(true),varTy("`τ",typeTy)]),arrayTy(varTy("`τ",typeTy)),false,true,Annotation.qfree,true),true,false,Annotation.qfree,true);
			break;
		case "vector":
			ce.type = productTy([true],["`τ"],typeTy,productTy([true,true],["`n","`x"],tupleTy([ℕt(true),varTy("`τ",typeTy)]),vectorTy(varTy("`τ",typeTy),varTy("`n",ℕt(true))),false,true,Annotation.qfree,true),true,false,Annotation.qfree,true);
			break;
		case "reverse":
			ce.type = productTy([true,true,true],["`τ","`χ","`φ"],tupleTy([typeTy,typeTy,typeTy]),funTy([true],funTy([true,false],tupleTy([varTy("`τ",typeTy),varTy("`χ",typeTy)]),varTy("`φ",typeTy),false,true,Annotation.mfree,true),funTy([true,false],tupleTy([varTy("`τ",typeTy),varTy("`φ",typeTy)]),varTy("`χ",typeTy),false,true,Annotation.mfree,true),false,false,Annotation.qfree,true),true,true,Annotation.qfree,true);
			break;
		case "M":
			ce.type = productTy([true],["`τ"],typeTy,funTy([false],varTy("`τ",typeTy),varTy("`τ",typeTy,true),false,false,Annotation.none,true),true,false,Annotation.qfree,true);
			break;
		case "H","X","Y","Z":
			ce.type = funTy([false],Bool(false),Bool(false),false,false,op=="X"?Annotation.qfree:Annotation.mfree,true);
			break;
		case "P":
			ce.type = funTy([true],ℝ(true),unit,false,false,Annotation.mfree,true);
			break;
		case "rX","rY","rZ":
			ce.type = funTy([true,false],tupleTy([ℝ(true),Bool(false)]),Bool(false),false,true,Annotation.mfree,true);
			break;
		default:
			sc.error(format("unknown quantum primitive %s",literal.lit.str),literal.loc);
			ce.sstate=SemState.error;
			break;
	}
	return ce;
}

Expression handleQuery(CallExp ce,Scope sc){
	Expression[] args;
	if(auto tpl=cast(TupleExp)ce.arg) args=tpl.e;
	else args=[ce.arg];
	if(args.length==0){
		sc.error("expected argument to __query",ce.loc);
		ce.sstate=SemState.error;
		return ce;
	}
	auto literal=cast(LiteralExp)args[0];
	if(!literal||literal.lit.type!=Tok!"``"){
		sc.error("first argument to __query must be string literal",args[0].loc);
		ce.sstate=SemState.error;
		return ce;
	}
	switch(literal.lit.str){
		case "dep":
			if(args.length!=2||!cast(Identifier)args[1]){
				sc.error("expected single variable as argument to 'dep' query", ce.loc);
				ce.sstate=SemState.error;
				break;
			}else{
				args[1]=expressionSemantic(args[1],sc,ConstResult.yes);
				auto dep="{}";
				if(auto id=cast(Identifier)args[1]){
					if(id.sstate==SemState.completed){
						auto dependency=sc.getDependency(id);
						if(dependency.isTop) dep="⊤";
						else dep=dependency.dependencies.to!string;
					}
				}
				Token tok;
				tok.type=Tok!"``";
				tok.str=dep;
				auto nlit=New!LiteralExp(tok);
				nlit.loc=ce.loc;
				nlit.type=stringTy(true);
				nlit.sstate=SemState.completed;
				return nlit;
			}
		default:
			sc.error(format("unknown query '%s'",literal.lit.str),literal.loc);
			ce.sstate=SemState.error;
			break;
	}
	return ce;
}

}


// prepends the given type 'first' to a ProductTy domain as given by 'dom'
static if(language==dp) private Expression prependingToDomain(Expression first, Expression dom) {
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

static if(language==dp) Expression[] argTys(ProductTy ftype) {
	return iota(ftype.names.length).map!(i => ftype.argTy(i)).array;
}

static if(language==dp) Expression tupleTyIfRequired(T)(T[] types) {
	if (types.length>1) {
		return tupleTy(cast(Expression[])types);
	} else if (types.length==1) {
		return types[0];
	} else {
		return unit;
	}
}

static if(language==dp) bool hasManifoldImpl(Expression e, Scope sc) {
	if (auto ty=typeOrDataType(e)) {
		if (auto aggrty = cast(AggregateTy)ty) {
			return aggrty.isParameterized;
		}
		return ty.isManifoldType;
	} else if (e.type==manifoldTypeTy) {
		return true;
	} else if (e.isManifoldType) {
		return true;
	}
	return false;
}

static if(language==dp) ProductTy pullbackTy(FunctionDef primalFd, Scope sc) {
    // skip manifold member operations
    if (primalFd.isManifoldOp) {
        //writeln(format("Skipping pullback generation for manifold member: %s", primalFd.name.toString));
        return null;
    }

    // skip dat constructors
    if (primalFd.isConstructor) {
        //writeln(format("Skipping pullback generation for constructor: %s", primalFd.name.toString));
        return null;
    }

    // skip pullback functions
    if (primalFd.isPullback) {
        return null;
    }

	// no pullbacks for nondiff-annotated functions
    if (!primalFd.isDifferentiable) {
        return null;
    }

	auto name = primalFd.name !is null ? primalFd.name.name : primalFd.toString;
	return pullbackTy(name, primalFd.ftype, sc, primalFd);
}

static if(language==dp) ProductTy pullbackTy(string name, ProductTy ftype, Scope sc, Node errNode) {
	string[][] paramNames = collectAllParameterNames(ftype);
	bool[][] isConst = collectAllParametersIsConst(ftype);
	
	// switch around dom/cod since the pullback goes the other way round
	Expression[] domTypes = [findFinalFunTyInSquaredFunTy(ftype).cod];
	if (auto tupTy=cast(TupleTy)ftype.cod) domTypes = tupTy.types;
	Expression[][] codTuples = collectCompleteFunTyDom(ftype);

	// keep track of all differentiable types of co-domain/domain and their primal names
	Expression[] pullbackCodTangentTypes;
	string[] pullbackCodPrimalParamName;

	Expression[] pullbackDomTangentTys = [];
	// no pullback for functions w/o return type/parameters
	if (domTypes.length==0||codTuples[0].length==0) {
		return null;
	}
	// no pullback for non-differentiable functions
	if (!ftype.isDifferentiable) {
		return null;
	}

	foreach(domType; domTypes) {
		// malformed ftype
		if (domType is null) {
			return null;
		}
		// no pullbacks for functions w/o arguments
		if (domType==unit) {
			return null;
		}

		auto tangentVecTy = domType.tangentVecTy(sc);

		if (tangentVecTy is null) {
			AggregateTy aggrty = cast(AggregateTy)domType;
			if (!aggrty) aggrty = isDataTyId(domType);
			// parameterised AggregateTy return types are also fine
			if (aggrty) {
				if (aggrty.isParameterized) {
					// use type-constraint param[A] manifold
					tangentVecTy = parameterSetTy(aggrty, sc).tangentVecTy(sc);
				}
			}
		}

		if (tangentVecTy is null) {
			sc.error(format("failed to determine pullback signature for function %s with" ~ 
				" non-differentiable return type %s.", name, domType.toString), errNode.loc);
			return null;
		}

		pullbackDomTangentTys ~= [tangentVecTy];
	}

	foreach(idx, codType; codTuples[$-1]) {
		// malformed ftype
		if (codType is null) {
			return null;
		}
		// no pullbacks for functions w/o return types
		if (codType==unit) {
			return null;
		}
		// exclude parameters of non-differentiable type
		if (!hasManifoldImpl(codType, sc)) {
			pullbackCodTangentTypes ~= [noGradTy];
			pullbackCodPrimalParamName ~= [paramNames[$-1][idx]];
		} else {
			pullbackCodTangentTypes ~= [codType];
			pullbackCodPrimalParamName ~= [paramNames[$-1][idx]];
		}
	}
	
	auto pullbackSquareDoms = codTuples.map!(t => tupleTyIfRequired(t)).array;
	bool[] squareDomIsTuple = paramNames.map!(n => n.length > 1).array;

	auto pullbackParamNames = ["v"];
	auto pullbackDom = tupleTyIfRequired(pullbackDomTangentTys);

	Expression pullbackCod;
	Expression[] pullbackCodComponents;
	foreach(idx, param; pullbackCodPrimalParamName) {
		if (param=="") param = "#"~to!string(idx);

		auto type = pullbackCodTangentTypes[idx];

		if (type==noGradTy) {
			pullbackCodComponents ~= [noGradTy];
			continue;
		}

		Expression bound = new Identifier(param);
		bound.type = type;

		if (auto paramFtype=cast(FunTy)type) {
			bound = new ParameterSetHandleExp(bound);
			bound.type = parameterSetTy(bound, sc);
		}
		pullbackCodComponents ~= [tangentVectorTy(bound, sc)];
	}

	if (pullbackCodComponents.length == 1) {
		pullbackCod = pullbackCodComponents[0];
	} else {
		pullbackCod = tupleTy(pullbackCodComponents);
	}

	auto pullbackOpTy = productTy([true], pullbackParamNames, pullbackDom, pullbackCod, false, false, 
								  Annotation.none, true, false, false, false, ftype);
	return createChainOfSquaredProductTy(isConst, squareDomIsTuple, paramNames, pullbackSquareDoms, pullbackOpTy);
}

static if(language==dp) ProductTy createChainOfSquaredProductTy(bool[][] isConst, bool[] isTuple, string[][] paramNames, Expression[] pullbackSquareDom, ProductTy nextProductTy) {
	ulong length = isConst.length;
	assert(length==isTuple.length);
	assert(length==paramNames.length);
	assert(length==pullbackSquareDom.length);

	if (length==0) {
		return nextProductTy;
	} else {
		auto fty = productTy(isConst[$-1], paramNames[$-1], pullbackSquareDom[$-1], nextProductTy, 
			true, isTuple[$-1], Annotation.none, true, false, false, false);
		return createChainOfSquaredProductTy(isConst[0..$-1], isTuple[0..$-1], paramNames[0..$-1], pullbackSquareDom[0..$-1], fty);
	}
}

static if(language==dp) string[][] collectAllParameterNames(ProductTy ftype) {
	if (ftype.isSquare) {
		auto nextOrderFtype = cast(ProductTy)ftype.cod;
		assert(!!nextOrderFtype);
		return [ftype.names] ~ collectAllParameterNames(nextOrderFtype);
	} else {
		return [ftype.names.array];
	}
}

static if(language==dp) bool[][] collectAllParametersIsConst(ProductTy ftype) {
	if (ftype.isSquare) {
		auto nextOrderFtype = cast(ProductTy)ftype.cod;
		assert(!!nextOrderFtype);
		return [ftype.isConst] ~ collectAllParametersIsConst(nextOrderFtype);
	} else {
		return [ftype.isConst];
	}
}

static if(language==dp) ProductTy findFinalFunTyInSquaredFunTy(FunTy ftype) {
	if (ftype.isSquare) {
		auto nextOrderFtype = cast(ProductTy)ftype.cod;
		assert(!!nextOrderFtype);
		return findFinalFunTyInSquaredFunTy(nextOrderFtype);
	} else {
		return ftype;
	}
}

static if(language==dp) Expression[][] collectCompleteFunTyDom(FunTy ftype) {
	if (ftype.isSquare) {
		auto nextOrderFtype = cast(ProductTy)ftype.cod;
		assert(!!nextOrderFtype);
		return [argTys(ftype)] ~ collectCompleteFunTyDom(nextOrderFtype);
	} else {
		if (ftype.names.length > 1) {
			return [argTys(ftype)];
		} else {
			return [[ftype.dom]];
		}
	}
}

static if(language==dp) Expression binaryPullbackTy(BinaryPullbackCallExp binaryPullbackCallExp, Scope sc) {
	auto domT1 = binaryPullbackCallExp.e1.type;
	auto domT2 = binaryPullbackCallExp.e2.type;

	Expression[] tangentCod;

	foreach(dom; [domT1, domT2]) {
		if (!dom) {
			tangentCod ~= unit;
			sc.error(format("failed to determine pullback type for binary operation %s with" ~ 
				" non-handled operand type %s.", binaryPullbackCallExp.op, dom), binaryPullbackCallExp.loc);
			binaryPullbackCallExp.sstate = SemState.error;
		} else if (auto tv = dom.tangentVecTy(sc)) {
			tangentCod ~= tv;
		} else {
			// non-differentiable operands have unit tangent vector type
			tangentCod ~= unit;
		}
	}

	return tupleTy(tangentCod);
}