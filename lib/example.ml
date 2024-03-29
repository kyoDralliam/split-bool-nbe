open Term
open Nbe


(* An instance of a typechecking problem consists of a named context (last entry at the top), a type and a term *)

type inst = { ctx : (string * tm) list ; ty : tm ; tm : tm }

let print_res names (ct : (int*NeNf.ne,NeNf.pnf) Splitter.case_tree) = 
  let names = List.map (fun x -> Some x) names in
  let pp_pnf fmt (t : NeNf.pnf) = pp_tm ~names fmt (t :> tm) in
  let pp_lvl_ne fmt ((i,ne) : int * NeNf.ne) = Format.fprintf fmt "%d:%a" i (pp_tm ~names) (ne :> tm) in
  Format.printf "%a" (Splitter.pp_case_tree pp_lvl_ne pp_pnf) ct

let norm_inst (inst : inst) = 
  M.run @@ norm (List.map snd inst.ctx) inst.ty inst.tm

(* Print the result of normalizing *)
let print_inst (inst : inst) = 
  print_res (List.map fst inst.ctx) (norm_inst inst)

(* Typechecks an instance *)
let check_inst (inst : inst) =
  Typecheck.full_check_tm (List.map snd inst.ctx) inst.tm inst.ty

(* Typechecks an instance and return the intermediate components for the context, type and term *)
let check_inst_dbg (inst : inst) =
  Typecheck.full_check_tm_dbg (List.map snd inst.ctx) inst.tm inst.ty

(* Infers the type of the term of the instance disregarding the provided type *)
let infer_inst (inst : inst) =
  Typecheck.full_infer (List.map snd inst.ctx) inst.tm



(* Writing terms *)
let ( @* ) fn arg = App {fn ; arg}
let pi dom cod = Pi {dom ; cod}
let lam ty body = Lam { ty ; body}
let ifte discr brT brF = Ifte { discr ; brT ; brF }



let ex1 = {
  ctx = ["b", Bool] ;
  ty = Bool ;
  tm = Var 0 ;
}

let ex2 = {
  ctx = ["x", Bool ; "f", pi Bool Bool ] ;
  ty = Bool ;
  tm = Var 1 @* Var 0 ;
}

let ex3 = {
  ctx = ["x", Bool ; "f", pi Bool Bool ] ;
  ty = Bool ;
  tm = 
    let f = Var 1 in
    let x = Var 0 in
    f @* (f @* (f @* x)) ;
}

let ex4 = {
  ctx = ["f", pi Bool Bool] ;
  ty = pi Bool Bool ;
  tm = 
    let f = Var 1 in
    let x = Var 0 in
    lam Bool (f @* (f @* (f @* x))) ;
}

let ex5 = {
  ctx = ["f", pi Bool Bool] ;
  ty = pi Bool Bool ;
  tm = Var 0  ;
} 

let id_bool_inst = {
  ctx = [] ;
  ty = pi Bool Bool ;
  tm = lam Bool (Var 0)
}

let boolExt1 = {
  ctx = ["aT", U ; "b", Bool] ;
  ty = U ;
  tm = 
    let b = Var 1 in
    let aT = Var 0 in 
    ifte b (ifte b aT True) aT
}

let boolExt2 = {
  ctx = ["a", Var 0; "aT", U ; "b", Bool] ;
  ty = 
    (let b = Var 2 in
    let aT = Var 1 in 
    ifte b (ifte b aT True) aT) ;
  tm = Var 0 ;
}

open Typecheck
(* composition of (deeply-embedded) functions *)
let comp dom t1 t2 = lam dom (wk1 t1 @* (wk1 t2 @* Var 0)) 

let boolExt3 = {
  ctx = [
    "x", Var 1 @* Var 0 ;
    "f", pi Bool Bool ;
    "P", pi (pi Bool Bool) U
  ] ;
  ty = (let p = Var 2 in let f = Var 1 in p @* (comp Bool f (comp Bool f f)));
  tm = Var 0
}

let untyped_subtm = {
  ctx = [ "b", Bool ] ;
  ty = Bool ;
  tm = ifte (Var 0) True (ifte (Var 0) (U @* U) False)
}

let delta = lam Bool (Var 0 @* Var 0)
let omega = delta @* delta

let may_diverge = {
  ctx = [ "b", Bool ] ;
  ty = Bool ;
  tm = ifte (Var 0) True (ifte (Var 0) omega False)
}

let btob = pi Bool Bool
let funFunny = {
  ctx = [
    "f", ifte (Var 0) (pi btob Bool) (pi btob btob) ;
    "b", Bool
  ] ;
  ty = ifte (Var 1) (pi btob Bool) (pi btob btob) ;
  tm = Var 0
}

let appFunFunny = {
  ctx = [
    "f", ifte (Var 0) (pi btob Bool) (pi btob btob) ;
    "b", Bool
  ] ;
  ty = ifte (Var 1) Bool btob ;
  tm = Var 0 @* (lam Bool (Var 0))
}

let examples = [ ex1 ; ex2 ; ex3 ; ex4 ; ex5 ; id_bool_inst ; boolExt1 ; boolExt2 ; boolExt3 ; untyped_subtm ; may_diverge ; funFunny ; appFunFunny ]

let check_all_examples () = List.for_all check_inst examples




