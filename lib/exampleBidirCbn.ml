open Bidir

module D = DomainCbn
module TC = SemanticTypecheckAlt

(* An instance of a typechecking problem consists of a named context (last entry at the top), a type and a term *)

type pb = Infer of itm | Check of { tm : ctm ; ty : ctm } | CheckTy of ctm | ConvTy of ctm * ctm [@@deriving show]

type inst = { name : string; ctx : (string * ctm) list ; pb : pb } [@@deriving show]

let print_solution fmt inst =
  let ctx = List.map snd inst.ctx in
  Format.fprintf fmt "Instance %a:@\n" pp_inst inst ;
  let none fmt () = Format.fprintf fmt "context did not typecheck! @\n" in
  match inst.pb with
  | Infer t -> 
    let res = TC.infer_full_debug ctx t in
    Format.pp_print_option ~none (fun fmt (sctx, ty) -> 
      Format.fprintf fmt "Ctx: %a@\nInferred type: %a@\n@\n@\n" 
      TC.SCtx.pp sctx  
      D.pp_comp ty) fmt res
  | Check { tm ; ty } ->
    let res = TC.check_full_debug ctx tm ty in
    Format.pp_print_option ~none (fun fmt (sctx, ty, b) -> 
      Format.fprintf fmt "Ctx: %a@\nTy: %a@\nResult: %a@\n@\n@\n" 
        TC.SCtx.pp sctx 
        D.pp_comp ty 
        Format.pp_print_bool b) fmt res
  | CheckTy t ->
    let res = TC.check_ty_full_debug ctx t in
    Format.pp_print_option ~none (fun fmt (sctx, b, ty) -> 
      Format.fprintf fmt "Ctx: %a@\nResult: %a@\nTy: %a@\n@\n@\n" 
        TC.SCtx.pp sctx 
        Format.pp_print_bool b 
        D.pp_comp ty) fmt res
  | ConvTy (t1, t2) ->
    let res = TC.conv_ty_full_debug ctx t1 t2 in 
    Format.pp_print_option ~none (fun fmt (sctx, b, nfty1, nfty2) -> 
      Format.fprintf fmt "Ctx: %a@\nResult: %a@\nTy1: %a@\nTy2: %a@\n@\n@\n" 
        TC.SCtx.pp sctx 
        Format.pp_print_bool b 
        (D.Quote.M.pp Tm.NeNf.pp_pnf) nfty1 
        (D.Quote.M.pp Tm.NeNf.pp_pnf) nfty2) fmt res


(* Typechecks an instance *)

exception NotYetImplemented

let check_inst (inst : inst) =
  let ctx = List.map snd inst.ctx in
  match inst.pb with
  | Check {ty ; tm} -> TC.check_full ctx tm ty
  | _ -> raise NotYetImplemented

(* let debug_inst (inst : inst) =
  Format.printf "Instance %a:@\n" pp_inst inst ;
  match TC.check_full_debug (List.map snd inst.ctx) inst.tm inst.ty with
  | None  -> Format.printf "context did not typecheck! @\n"
  | Some (ctx, ty, res) ->
    Format.printf "Ctx: %a@\nTy: %a@\nResult: %a@\n" TC.SCtx.pp ctx D.pp_comp ty Format.pp_print_bool res *)

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
  name = "ex1" ;
  ctx = ["b", Bool] ;
  pb = Check {
    ty = Bool ;
    tm = Inj (Var 0) ;
  }
}

let ex2 = {
  name = "ex2" ;
  ctx = ["x", Bool ; "f", pi Bool Bool ] ;
  pb = Check {
    ty = Bool ;
    tm = Inj (Var 1 @* Inj (Var 0)) ;
  }
}

let ex3 = {
  name = "ex3";
  ctx = ["x", Bool ; "f", pi Bool Bool ] ;
  pb = Check {
    ty = Bool ;
    tm = 
      let f = Var 1 in
      let x = Inj (Var 0) in
      Inj (f @* Inj (f @* Inj (f @* x))) ;
  }
}

let ex4 = {
  name = "ex4" ;
  ctx = ["f", pi Bool Bool] ;
  pb = Check {
    ty = pi Bool Bool ;
    tm = 
      let f = Var 1 in
      let x = Inj (Var 0) in
      lam @@ Inj (f @* Inj (f @* Inj (f @* x))) ;
  }
}

let ex5 = {
  name = "ex5" ;
  ctx = ["f", pi Bool Bool] ;
  pb = Check {
    ty = pi Bool Bool ;
    tm = Inj (Var 0)  ;
  }
} 

let id_bool_inst = {
  name = "id_bool_inst" ;
  ctx = [] ;
  pb = Check {
    ty = pi Bool Bool ;
    tm = lam  (Inj (Var 0))
  }
}

let boolExt1 = {
  name = "boolExt1" ;
  ctx = ["aT", U ; "b", Bool] ;
  pb = Check {
    ty = U ;
    tm = 
      let b = Inj (Var 1) in
      let aT = Var 0 in 
      Inj (ifte b (ifte b aT (True @: Bool)) aT)
  }
}

let boolExt2 = {
  name = "boolExt2" ;
  ctx = ["a", Inj (Var 0); "aT", U ; "b", Bool] ;
  pb = Check {
    ty = 
      (let b = Inj (Var 2) in
      let aT = Var 1 in 
      Inj (ifte b (ifte b aT (True @: Bool)) aT)) ;
    tm = Inj (Var 0) ;
  }
}

(* composition of (deeply-embedded) functions *)
let comp t1 t2 = lam @@ Inj (iwk1 t1 @* Inj (iwk1 t2 @* Inj (Var 0))) 

let boolExt3 = {
  name = "boolExt3" ;
  ctx = [
    "x", Inj (Var 1 @* Inj (Var 0)) ;
    "f", pi Bool Bool ;
    "P", pi (pi Bool Bool) U
  ] ;
  pb = Check {
    ty = (let p = Var 2 in let f = Var 1 in Inj (p @* (comp f (comp f f @: pi Bool Bool))));
    tm = Inj (Var 0)
  }
}

let untyped_subtm = {
  name = "untyped_subtm" ;
  ctx = [ "b", Bool ] ;
  pb = Check {
    ty = Bool ;
    tm = let b = Inj (Var 0) in 
      Inj (ifte b tt (ifte b ((U @: U) @* U) ff))
  }
}

let delta = lam (Inj (Var 0 @* Inj (Var 0)))
let omega = (delta @: pi Bool Bool) @* delta

let may_diverge = {
  name = "may_diverge" ;
  ctx = [ "b", Bool ] ;
  pb = Check {
    ty = Bool ;
    tm = let b = Inj (Var 0) in Inj (ifte b tt (ifte b omega ff))
  }
}

let btob = pi Bool Bool
let delta' = Inj (lam (Inj ((Inj (Var 0) @: btob) @* Inj (Var 0))) @: btob) @: Bool

let should_typecheck = {
  name = "should_typecheck" ;
  ctx = [ "b", Bool ] ;
  pb = Check {
    ty = Bool ;
    tm = let b = Inj (Var 0) in Inj (ifte b tt (ifte b delta' ff))
  }
}

let funFunnyTy = {
  name = "funFunnyTy" ;
  ctx = [
    "f", ifty (Inj (Var 0)) (pi btob Bool) (pi btob btob) ;
    "b", Bool
  ] ;
  pb = Check {
    ty = U ;
    tm = Inj (ifte (Inj (Var 1)) (pi btob Bool @: U) (pi btob btob @: U)) ;
  }
}


let funFunny = {
  name = "funFunny" ;
  ctx = [
    "f", ifty (Inj (Var 0)) (pi btob Bool) (pi btob btob) ;
    "b", Bool
  ] ;
  pb = Check {
    ty = ifty (Inj (Var 1)) (pi btob Bool) (pi btob btob) ;
    tm = Inj (Var 0)
  }
}

let appFunFunny = {
  name = "appFunFunny" ;
  ctx = [
    "f", ifty (Inj (Var 0)) (pi btob Bool) (pi btob btob) ;
    "b", Bool
  ] ;
  pb = Check {
    ty = ifty (Inj (Var 1)) Bool btob ;
    tm = Inj (Var 0 @* (lam (Inj (Var 0))))
  }
}

let boolExt1Infer = {
  name = "boolExt1Infer" ;
  ctx = ["aT", U ; "b", Bool] ;
  pb = Infer (
      let b = Inj (Var 1) in
      let aT = Var 0 in 
      ifte b (ifte b aT (True @: Bool)) aT)
}


let examples = 
  [ ex1 ; ex2 ; ex3 ; ex4 ; ex5 ; 
    id_bool_inst ;
    boolExt1 ; boolExt2 ; boolExt3 ;  
    funFunnyTy ; funFunny ; appFunFunny ; 
    may_diverge ; untyped_subtm ]

let check_all_examples () = List.map check_inst examples

let check_out filename =
  let cout = open_out filename in
  let fmt = Format.formatter_of_out_channel cout in
  Fun.protect 
    ~finally:(fun () -> close_out cout) 
    (fun () -> List.iter (print_solution fmt) examples)


