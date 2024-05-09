open InferTerm
open Nbe


(* An instance of a typechecking problem consists of a named context (last entry at the top), a type and a term *)

type inst = { ctx : (string * itm) list ; ty : itm ; tm : itm }

let pp_ctx = 
  let pp_sep fmt () = Format.fprintf fmt "," in
  let pp_ctx_entry fmt ((name, ty), names) = 
    Format.fprintf fmt "%s:%a" name (pp_tm ~names) ty
  in
  Format.pp_print_list ~pp_sep pp_ctx_entry

let last i l = 
  let rec aux i acc l = 
    if i = 0 then acc else aux (i -1) (List.hd l :: acc) (List.tl l)
  in aux i [] (List.rev l)

let print_res fmt ctx (ct : (int*NeNf.ne,NeNf.pnf) Splitter.CT.case_tree) = 
  let names = List.map (fun x -> Some (fst x)) ctx in
  let pp_pnf fmt (t : NeNf.pnf) = Term.pp_tm ~names fmt (t :> Term.tm) in
  let pp_lvl_ne fmt ((i,ne) : int * NeNf.ne) = 
    let names = last (i+1) names  in
    Format.fprintf fmt "%d:%a" i (Term.pp_tm ~names) (ne :> Term.tm) in
  let ctx' =
    let map_smff = List.map (fun x -> Some (fst (fst x))) in
    List.fold_right (fun x l -> (x, map_smff l) :: l) ctx []
  in
  Format.fprintf fmt "%a |-@\n%a"
    pp_ctx (List.rev ctx')
    (Splitter.pp_case_tree pp_lvl_ne pp_pnf) ct

let norm_inst (inst : inst) = 
  M.run @@ norm (List.map (fun x -> itm_tm @@ snd x) inst.ctx) (itm_tm inst.ty) (itm_tm inst.tm)

let pp_inst fmt (inst : inst) = 
  print_res fmt inst.ctx (norm_inst inst)
(* Print the result of normalizing *)
let print_inst = pp_inst Format.std_formatter

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

let funFunnyTy = {
  ctx = [
    "f", ifte (Var 0) (pi btob Bool) (pi btob btob) ;
    "b", Bool
  ] ;
  ty = U ;
  tm = ifte (Var 1) (pi btob Bool) (pi btob btob) ;
}


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

let examples = 
  [ ex1 ; ex2 ; ex3 ; ex4 ; ex5 ; 
    id_bool_inst ;
    boolExt1 ; boolExt2 ; boolExt3 ;  
    funFunnyTy ; funFunny ; appFunFunny ; 
    may_diverge ; untyped_subtm ]

let check_all_examples () = List.for_all check_inst examples

let print_all_examples () = 
  List.iter (fun i -> print_inst i ; Format.print_newline () ; Format.print_newline ()) examples



