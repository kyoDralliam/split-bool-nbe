open Splitter

module Tm = Term
module NeNf = Tm.NeNf

module LevelNeOrd  =
struct
  type t = int * NeNf.ne
  [@@deriving show]
  let compare (k1,ne1) (k2,ne2) =
    let ck = Int.compare k1 k2 in
    if ck = 0 then Tm.NeOrd.compare ne1 ne2 else ck
end

module M = TreeSplitterLazy(LevelNeOrd)
module MN = Monad.Notations(M)
open MN

open Domain

let curry f (x,y) = f x y

let from_case_tree = CT.fold (fun lbl -> NeNf.case (snd lbl)) NeNf.pnf_nf

let rec read_back_case_tree env i m = 
  let+ ct = M.filter (fun x -> assert (fst x <= i) ; fst x = i) env m in
  from_case_tree ct

and read_back_bool_ne : type a. bool M.Map.t -> int -> ne -> a M.t -> a M.t -> a M.t =
  fun env i nev onl onr ->
  let* ne = read_back_ne env i nev in
  let (j, stne) = NeNf.to_canonical_index ne in
  M.split (i - j,stne) onl onr

and read_back_m : type a b. bool M.Map.t -> int -> (a -> b M.t) -> a Eval.E.t -> b M.t =
  fun env i f em ->
  CT.fold (read_back_bool_ne env i) (function Either.Left x -> f x | Either.Right s -> M.fail s) em
  

and read_back_ty env i ty : NeNf.pnf M.t =
  match ty with
  | NfPi { dom ; cod } ->
    let var0 = NfNe { ty = dom ; ne = NeVar i } in
    let* dom  = read_back_ty env i dom in
    let* cod = read_back_case_tree env i (read_back_m env (i+1) (read_back_ty env (i+1)) (Eval.do_clos cod var0)) in 
    M.ret @@ NeNf.pi dom cod
  | NfBool -> 
    M.ret @@ NeNf.bool
  | NfU -> 
    M.ret @@ NeNf.univ
  | NfNe { ty = _ ; ne } -> 
    M.map (fun x -> NeNf.ne_pnf NeNf.univ x) (read_back_ne env i ne)
  | _ -> 
    M.fail "Not a valid code of universe"


and read_back_pnf env i ty t : NeNf.pnf M.t =
  match ty with
  | NfPi { dom ; cod } ->
      let var0 = NfNe { ty = dom ; ne = NeVar i } in
      (* let* dom  = read_back_ty i dom in *)
      let* body = 
        let body =
          let open Eval in
          let* ty = do_clos cod var0 in 
          let* tm = do_app t var0 in
          E.ret (ty, tm)
        in 
        read_back_case_tree env i (read_back_m env (i+1) (curry @@ read_back_pnf env (i+1)) body)
      in 
      M.ret @@ NeNf.lam body
  | NfU -> 
    begin match t with
    | NfPi { dom ; cod } ->
      let var0 = NfNe { ty = dom ; ne = NeVar i } in
      let* dom  = read_back_ty env i dom in
      let* cod = read_back_case_tree env i (read_back_m env (i+1) (read_back_ty env (i+1)) (Eval.do_clos cod var0)) in 
      M.ret @@ NeNf.pi dom cod
    | NfBool -> 
      M.ret @@ NeNf.bool
    | NfNe { ty = _ ; ne } -> 
      M.map (fun x -> NeNf.ne_pnf NeNf.univ x) (read_back_ne env i ne)
    | NfU ->  
      M.fail  "Type in Type"
    | _ -> 
      M.fail "Not a valid code of universe"
    end
  | NfBool -> 
    begin match t with
    | NfTrue -> M.ret NeNf.btrue
    | NfFalse -> M.ret NeNf.bfalse
    | NfNe { ne ; _ } -> read_back_bool_ne env i ne (M.ret NeNf.btrue) (M.ret NeNf.bfalse)
    | _ -> M.fail "Not a valid boolean value"
    end
  | NfNe { ne = ty ; _ } ->
    begin match t with
    | NfNe { ne ; _ } ->
      let* ty = 
        M.map (fun x -> NeNf.ne_pnf NeNf.univ x) @@ read_back_ne env i ty
      in
      let* t = read_back_ne env i ne in
      M.ret @@ NeNf.ne_pnf ty t
    | _ -> 
      M.fail "Not a valid element of a neutral type"
    end
  | _ -> 
    M.fail "Not a valid type"

and read_back_ne env i ne : NeNf.ne M.t =
  match ne with
  | NeVar k -> M.ret @@ NeNf.var (i - k)
  | NeApp {fn ; arg = Normal { ty ; tm }} -> 
    let* f = read_back_ne env i fn in
    let* arg = read_back_pnf env i ty tm in
    M.ret @@ NeNf.app f arg



let reify_ty env i = read_back_m env i (read_back_ty env i)
let reify env i = read_back_m env i (curry @@ read_back_pnf env i)

let norm_ty cstr (env : env) (ty : Tm.tm) : NeNf.pnf M.t =
  let i = List.length env in
  reify_ty cstr i (Eval.eval ty env)

let norm cstr (env : env) (ty : Tm.tm) (t : Tm.tm) : NeNf.pnf M.t =
  let i = List.length env in
  reify cstr i @@
    let open Eval in 
    let* ty = eval ty env in 
    let* tm = eval t env in
    E.ret (ty,tm)
   
