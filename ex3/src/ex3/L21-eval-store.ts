// L2-eval-box.ts
// L2 with mutation (set!) and env-box model
// Direct evaluation of letrec with mutation, define supports mutual recursion.

import { map, reduce, repeat, zipWith } from "ramda";
import { isBoolExp, isCExp, isLitExp, isNumExp, isPrimOp, isStrExp, isVarRef,
         isAppExp, isDefineExp, isIfExp, isLetExp, isProcExp, Binding, VarDecl, CExp, Exp, IfExp, LetExp, ProcExp, Program,
         parseL21Exp, DefineExp, isSetExp, SetExp} from "./L21-ast";
import { applyEnv, makeExtEnv, Env, Store, setStore, extendStore, ExtEnv, theGlobalEnv, globalEnvAddBinding, theStore, isGlobalEnv, applyStore } from "./L21-env-store";
import { isClosure, makeClosure, Closure, Value } from "./L21-value-store";
import { applyPrimitive } from "./evalPrimitive-store";
import { first, rest, isEmpty } from "../shared/list";
import { Result, bind, safe2, mapResult, makeFailure, makeOk, isOk, either } from "../shared/result";
import { parse as p } from "../shared/parser";
import { connect } from "node:http2";
import { setBox } from "../shared/box";

// ========================================================
// Eval functions

const applicativeEval = (exp: CExp, env: Env): Result<Value> =>{
    console.log(exp)
    return isNumExp(exp) ? makeOk(exp.val) :
    isBoolExp(exp) ? makeOk(exp.val) :
    isStrExp(exp) ? makeOk(exp.val) :
    isPrimOp(exp) ? makeOk(exp) :
    isVarRef(exp) ? bind(applyEnv(env,exp.var), num => applyStore(theGlobalEnv.store ,num)):
    isSetExp(exp) ? evalSet(exp,env):
    isLitExp(exp) ? makeOk(exp.val as Value) :
    isIfExp(exp) ? evalIf(exp, env) :
    isProcExp(exp) ? evalProc(exp, env) :
    isLetExp(exp) ? evalLet(exp, env) :
    isAppExp(exp) ? safe2((proc: Value, args: Value[]) => applyProcedure(proc, args))
                        (applicativeEval(exp.rator, env), mapResult((rand: CExp) => applicativeEval(rand, env), exp.rands)) :
    exp;
}
export const isTrueValue = (x: Value): boolean =>
     (x === true);

const evalIf = (exp: IfExp, env: Env): Result<Value> =>
    bind(applicativeEval(exp.test, env),
         (test: Value) => isTrueValue(test) ? applicativeEval(exp.then, env) : applicativeEval(exp.alt, env));

const evalProc = (exp: ProcExp, env: Env): Result<Closure> =>
    makeOk(makeClosure(exp.args, exp.body, env));


// KEY: This procedure does NOT have an env parameter.
//      Instead we use the env of the closure.
const applyProcedure = (proc: Value, args: Value[]): Result<Value> =>
    isPrimOp(proc) ? applyPrimitive(proc, args) :
    isClosure(proc) ? applyClosure(proc, args) :
    makeFailure(`Bad procedure ${JSON.stringify(proc)}`);

const applyClosure = (proc: Closure, args: Value[]): Result<Value> => {
    const vars = map((v: VarDecl) => v.var, proc.params);
    const addresses:number[] =  reduce(reduce_func, [],args);
    //console.log(addresses)
    //console.log(vars)
    const newEnv: ExtEnv = makeExtEnv(vars, addresses, proc.env)
    return evalSequence(proc.body, newEnv);
}

const reduce_func =(acc:number[], curr:Value):number[]=>{
    
    theGlobalEnv.store = extendStore(theGlobalEnv.store ,curr );
    const addr = theGlobalEnv.store.vals.length-1;
    return acc.concat([addr]);
}

// Evaluate a sequence of expressions (in a program)
export const evalSequence = (seq: Exp[], env: Env): Result<Value> =>
    isEmpty(seq) ? makeFailure("Empty program") :
    evalCExps(first(seq), rest(seq), env);
    
const evalCExps = (first: Exp, rest: Exp[], env: Env): Result<Value> =>
    isDefineExp(first) ? evalDefineExps(first, rest) :
    isCExp(first) && isEmpty(rest) ? applicativeEval(first, env) :
    isCExp(first) ? bind(applicativeEval(first, env), _ => evalSequence(rest, env)) :
    first;

const evalDefineExps = (def: DefineExp, exps: Exp[]): Result<Value> =>
    bind(applicativeEval(def.val, theGlobalEnv),
            (rhs: Value) => {   
                                //console.log("val: "+rhs)
                                globalEnvAddBinding(def.var.var, theGlobalEnv.store.vals.length);
                                theGlobalEnv.store = extendStore(theGlobalEnv.store , rhs)
                                return evalSequence(exps, theGlobalEnv); }); 
// const evalDefineExps = (def: DefineExp, exps: Exp[]): Result<Value> =>
//     {
//         const value  = applicativeEval(def.val,theGlobalEnv);
//         bind(value,(val1:Value)=> (makeOk(theGlobalEnv.store = extendStore(theGlobalEnv.store ,val1 ))));
//         const addr = theGlobalEnv.store.vals.length;
//         globalEnvAddBinding(def.var.var,addr);
//         return evalSequence(exps,theGlobalEnv);
//     }

// Main program
// L2-BOX @@ Use GE instead of empty-env
export const evalProgram = (program: Program): Result<Value> =>
    evalSequence(program.exps, theGlobalEnv);

export const evalParse = (s: string): Result<Value> =>
    bind(bind(p(s), parseL21Exp), (exp: Exp) => evalSequence([exp], theGlobalEnv));

//
 const evalSet = (exp: SetExp, env: Env): Result<void> =>{ 
    const value:Result<Value> = applicativeEval(exp.val,env)
    console.log(value)
    return bind(applyEnv(env, exp.var.var), num => bind( value,val=> makeOk(setStore(theGlobalEnv.store,num,val))))
 }
  


const set = (num:number):number =>{
    return num;
}

// LET: Direct evaluation rule without syntax expansion
// compute the values, extend the env, eval the body.
const evalLet = (exp: LetExp, env: Env): Result<Value> => {
    const vals = mapResult((v: CExp) => applicativeEval(v, env), map((b: Binding) => b.val, exp.bindings));
    const vars = map((b: Binding) => b.var.var, exp.bindings);

    return bind(vals, (vals: Value[]) => {
        const addresses:number[] = reduce(reduce_func,[],vals)
        console.log(theGlobalEnv.store)
        console.log(addresses)
        const newEnv = makeExtEnv(vars, addresses, env)
        return evalSequence(exp.body, newEnv);
    })
}
    
