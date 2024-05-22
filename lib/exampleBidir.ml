open Bidir


(* An instance of a typechecking problem consists of a named context (last entry at the top), a type and a term *)

type inst = { ctx : (string * ctm) list ; ty : ctm ; tm : ctm }
(* Typechecks an instance *)
let check_inst (inst : inst) =
  SemanticTypecheck.check_full (List.map snd inst.ctx) inst.tm inst.ty

let debug_inst (inst : inst) =
  let (_ctx, _ty, tm, _res) = SemanticTypecheck.check_full_debug (List.map snd inst.ctx) inst.tm inst.ty in
  let open Nbe.M in
  pp (fun fmt _ -> Format.fprintf fmt "()") Format.std_formatter tm

(* Printing instances *)
(* let pp_ctx = 
  let pp_sep fmt () = Format.fprintf fmt "," in
  let pp_ctx_entry fmt ((name, ty), names) = 
    Format.fprintf fmt "%s:%a" name (pp_tm ~names) ty
  in
  Format.pp_print_list ~pp_sep pp_ctx_entry

let last i l = 
  let rec aux i acc l = 
    if i = 0 then acc else aux (i -1) (List.hd l :: acc) (List.tl l)
  in aux i [] (List.rev l)

let print_res fmt ctx (ct : (int*Term.NeNf.ne,Term.NeNf.pnf) CaseTree.case_tree) = 
  let names = List.map (fun x -> Some (fst x)) ctx in
  let pp_pnf fmt (t : Term.NeNf.pnf) = Term.pp_tm ~names fmt (t :> Term.tm) in
  let pp_lvl_ne fmt ((i,ne) : int * Term.NeNf.ne) = 
    let names = last (i+1) names  in
    Format.fprintf fmt "%d:%a" i (Term.pp_tm ~names) (ne :> Term.tm) in
  let ctx' =
    let map_smff = List.map (fun x -> Some (fst (fst x))) in
    List.fold_right (fun x l -> (x, map_smff l) :: l) ctx []
  in
  Format.fprintf fmt "%a |-@\n%a"
    pp_ctx (List.rev ctx')
    (CaseTree.pp_case_tree pp_lvl_ne pp_pnf) ct

let norm_inst (inst : inst) = 
  M.run M.Map.empty (fun _ -> failwith "Run None!") @@ 
    norm (List.map (fun x -> itm_tm @@ snd x) inst.ctx) (itm_tm inst.ty) (itm_tm inst.tm)

let pp_inst fmt (inst : inst) = 
  print_res fmt inst.ctx (norm_inst inst)
(* Print the result of normalizing *)
let print_inst = pp_inst Format.std_formatter *)




(* Writing terms *)

let ( @* ) fn arg = App {fn ; arg}
let ( @: ) tm ty = Ascr { tm ; ty }
let app dom cod tm arg = App { fn = tm @:  Pi { dom ; cod }  ; arg}
let pi dom cod = Pi {dom ; cod}
let lam body = Lam body
let ifte discr brT brF = Ifte { discr ; brT ; brF }
let ifty discr tyT tyF = IfTy { discr ; tyT ; tyF }

let tt = True @: Bool
let ff = False @: Bool


let ex1 = {
  ctx = ["b", Bool] ;
  ty = Bool ;
  tm = Inj (Var 0) ;
}

let ex2 = {
  ctx = ["x", Bool ; "f", pi Bool Bool ] ;
  ty = Bool ;
  tm = Inj (Var 1 @* Inj (Var 0)) ;
}

let ex3 = {
  ctx = ["x", Bool ; "f", pi Bool Bool ] ;
  ty = Bool ;
  tm = 
    let f = Var 1 in
    let x = Inj (Var 0) in
    Inj (f @* Inj (f @* Inj (f @* x))) ;
}

let ex4 = {
  ctx = ["f", pi Bool Bool] ;
  ty = pi Bool Bool ;
  tm = 
    let f = Var 1 in
    let x = Inj (Var 0) in
    lam @@ Inj (f @* Inj (f @* Inj (f @* x))) ;
}

let ex5 = {
  ctx = ["f", pi Bool Bool] ;
  ty = pi Bool Bool ;
  tm = Inj (Var 0)  ;
} 

let id_bool_inst = {
  ctx = [] ;
  ty = pi Bool Bool ;
  tm = lam  (Inj (Var 0))
}

let boolExt1 = {
  ctx = ["aT", U ; "b", Bool] ;
  ty = U ;
  tm = 
    let b = Inj (Var 1) in
    let aT = Var 0 in 
    Inj (ifte b (ifte b aT (True @: Bool)) aT)
}

let boolExt2 = {
  ctx = ["a", Inj (Var 0); "aT", U ; "b", Bool] ;
  ty = 
    (let b = Inj (Var 2) in
    let aT = Var 1 in 
    Inj (ifte b (ifte b aT (True @: Bool)) aT)) ;
  tm = Inj (Var 0) ;
}

(* composition of (deeply-embedded) functions *)
let comp t1 t2 = lam @@ Inj (iwk1 t1 @* Inj (iwk1 t2 @* Inj (Var 0))) 

let boolExt3 = {
  ctx = [
    "x", Inj (Var 1 @* Inj (Var 0)) ;
    "f", pi Bool Bool ;
    "P", pi (pi Bool Bool) U
  ] ;
  ty = (let p = Var 2 in let f = Var 1 in Inj (p @* (comp f (comp f f @: pi Bool Bool))));
  tm = Inj (Var 0)
}

let untyped_subtm = {
  ctx = [ "b", Bool ] ;
  ty = Bool ;
  tm = let b = Inj (Var 0) in 
    Inj (ifte b tt (ifte b ((U @: U) @* U) ff))
}

let delta = lam (Inj (Var 0 @* Inj (Var 0)))
let omega = (delta @: pi Bool Bool) @* delta

let may_diverge = {
  ctx = [ "b", Bool ] ;
  ty = Bool ;
  tm = let b = Inj (Var 0) in Inj (ifte b tt (ifte b omega ff))
}

let btob = pi Bool Bool
let delta' = Inj (lam (Inj ((Inj (Var 0) @: btob) @* Inj (Var 0))) @: btob) @: Bool

let should_typecheck = {
  ctx = [ "b", Bool ] ;
  ty = Bool ;
  tm = let b = Inj (Var 0) in Inj (ifte b tt (ifte b delta' ff))
}

let funFunnyTy = {
  ctx = [
    "f", ifty (Inj (Var 0)) (pi btob Bool) (pi btob btob) ;
    "b", Bool
  ] ;
  ty = U ;
  tm = Inj (ifte (Inj (Var 1)) (pi btob Bool @: U) (pi btob btob @: U)) ;
}


let funFunny = {
  ctx = [
    "f", ifty (Inj (Var 0)) (pi btob Bool) (pi btob btob) ;
    "b", Bool
  ] ;
  ty = ifty (Inj (Var 1)) (pi btob Bool) (pi btob btob) ;
  tm = Inj (Var 0)
}

let appFunFunny = {
  ctx = [
    "f", ifty (Inj (Var 0)) (pi btob Bool) (pi btob btob) ;
    "b", Bool
  ] ;
  ty = ifty (Inj (Var 1)) Bool btob ;
  tm = Inj (Var 0 @* (lam (Inj (Var 0))))
}

let examples = 
  [ ex1 ; ex2 ; ex3 ; ex4 ; ex5 ; 
    id_bool_inst ;
    boolExt1 ; boolExt2 ; boolExt3 ;  
    funFunnyTy ; funFunny ; appFunFunny ; 
    may_diverge ; untyped_subtm ]

let check_all_examples () = List.map check_inst examples




