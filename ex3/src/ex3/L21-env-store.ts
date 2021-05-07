import { add, map, zipWith } from "ramda";
import { Value } from './L21-value-store';
import { Result, makeFailure, makeOk, bind, either } from "../shared/result";

// ========================================================
// Box datatype
// Encapsulate mutation in a single type.
type Box<T> = T[];
const makeBox = <T>(x: T): Box<T> => ([x]);
const unbox = <T>(b: Box<T>): T => b[0];
const setBox = <T>(b: Box<T>, v: T): void => { b[0] = v; return; }

// ========================================================
// Store datatype
export interface Store {
    tag: "Store";
    vals: Box<Value>[];
}

export const isStore = (x: any): x is Store => x.tag === "Store";
export const makeEmptyStore = (): Store => ({tag: "Store",vals:[]});
export const theStore: Store = makeEmptyStore();
export const extendStore = (s: Store, val: Value): Store =>
    ({tag: "Store",vals:s.vals.concat([makeBox(val)])});

    
export const applyStore = (store: Store, address: number): Result<Value> =>
    makeOk(unbox(store.vals[address]));

    
export const setStore = (store: Store, address: number, val: Value): void => 
    setBox(store.vals[address],val)


// ========================================================
// Environment data type
// export type Env = EmptyEnv | ExtEnv;
export type Env = GlobalEnv | ExtEnv;

interface GlobalEnv {
    tag: "GlobalEnv";
    vars: Box<string[]>;
    addresses: Box<number[]>
    store:Store
}

export interface ExtEnv {
    tag: "ExtEnv";
    vars: string[];
    addresses: number[];
    nextEnv: Env;
}

const makeGlobalEnv = (): GlobalEnv =>
    ({tag: "GlobalEnv", vars: makeBox([]), addresses:makeBox([]),store:theStore});

export const isGlobalEnv = (x: any): x is GlobalEnv => x.tag === "GlobalEnv";

// There is a single mutable value in the type Global-env
export const theGlobalEnv = makeGlobalEnv();

export const makeExtEnv = (vs: string[], addresses: number[], env: Env): ExtEnv =>
    ({tag: "ExtEnv", vars: vs, addresses: addresses, nextEnv: env});

const isExtEnv = (x: any): x is ExtEnv => x.tag === "ExtEnv";

export const isEnv = (x: any): x is Env => isGlobalEnv(x) || isExtEnv(x);

// Apply-env
export const applyEnv = (env: Env, v: string): Result<number> =>
    isGlobalEnv(env) ? applyGlobalEnv(env, v) :
    applyExtEnv(env, v);

const applyGlobalEnv = (env: GlobalEnv, v: string): Result<number> => 
    unbox(env.vars).includes(v) ? makeOk(unbox(env.addresses)[unbox(env.vars).indexOf(v)]) :
    makeFailure("value was not found :(");


export const globalEnvAddBinding = (v: string, addr: number): void =>
    {
        setBox(theGlobalEnv.vars,unbox(theGlobalEnv.vars).concat([v]));
        setBox(theGlobalEnv.addresses,unbox(theGlobalEnv.addresses).concat([addr]));
    }

const applyExtEnv = (env: ExtEnv, v: string): Result<number> =>
    env.vars.includes(v) ? makeOk(env.addresses[env.vars.indexOf(v)]) :
    applyEnv(env.nextEnv, v);
