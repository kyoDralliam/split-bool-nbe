open Splitter

module Tm = Term
module NeNf = Tm.NeNf

module M = TreeSplitter(Term.NeOrd)
module MN = Notations(M)
open MN

open Domain

(*
module type NbeSpec = sig
  
  val do_app : int -> t -> t -> t M.t
  val do_split : int -> ne -> t M.t
  val do_clos : int -> clos -> t -> t M.t
  val eval : int -> Tm.tm -> env -> t M.t
  
  val read_back_nf : int -> nf -> Tm.NeNf.nf M.t

  val from_case_tree : (NeNf.ne, NeNf.pnf) case_tree -> NeNf.nf

  val read_back_case_tree : int -> nf M.t -> NeNf.nf
  val read_back_pnf : int -> t -> t -> Tm.NeNf.pnf M.t
  val read_back_ne : int -> t -> ne -> Tm.NeNf.ne M.t

end*)

let rec from_case_tree = function
  | Leaf t -> NeNf.pnf_nf t
  | Split {lbl ; onl ; onr } ->
    NeNf.case lbl (from_case_tree onl) (from_case_tree onr)

let rec do_app i (fn : t) (arg : t) =
  match fn with
  | NfLam c -> do_clos i c arg
  | NfNe { ty = NfPi {dom ; cod} ; ne } -> 
    let* ty = do_clos i cod arg in
    let arg = Normal { ty = dom ; tm = arg } in
    let ne = NeApp { fn = ne ; arg } in
    M.ret @@ NfNe { ty ; ne }
  | _ -> failwith "Not a function"

(* and do_split i (ne : ne) = ? *)
and do_clos i (Clos { env ; body }) arg = 
  eval i body (arg :: env)

and eval i t env = 
  match t with
  | Tm.Var i -> M.ret @@ List.nth env i
  | Tm.Pi { dom ; cod } ->
    let* dom = eval i dom env in
    let cod = Clos { env ; body = cod } in
    M.ret @@ NfPi { dom; cod }
  | Tm.Lam { ty = _ ; body } -> 
    M.ret @@ NfLam (Clos { env ; body })
  | Tm.App {fn ; arg} ->
    let* f = eval i fn env in
    let* arg = eval i arg env in
    do_app i f arg
  | Tm.Bool ->
    M.ret @@ NfBool
  | Tm.True ->
    M.ret @@ NfTrue
  | Tm.False ->
    M.ret @@ NfFalse
  | Tm.Ifte { discr ; brT ; brF } ->
    let* b = eval i discr env in
    begin match b with
    | NfTrue -> eval i brT env
    | NfFalse -> eval i brF env
    | NfNe { ty = _ ; ne } ->
      let* tne = read_back_ne i ne in
      let+ b = M.get_split tne in 
      if b then NfTrue else NfFalse
    | _ -> failwith "Discriminee does not evaluate to a boolean"
    end
  | U -> 
    M.ret @@ NfU

(* and read_back_nf i nf = ? *)

and read_back_case_tree i m = 
  let m =
    let* (Normal { ty ; tm }) = m in
    read_back_pnf i ty tm 
  in 
  let+ ct = M.filter (NeNf.contains_var 0) m in
  from_case_tree ct

and read_back_pnf i ty t : NeNf.pnf M.t =
  match ty with
  | NfPi { dom ; cod } ->
      let var0 = NfNe { ty = dom ; ne = NeVar i } in
      let* dom  = read_back_pnf i NfU dom in
      let* body = 
        let body =
          let* ty = do_clos (i+1) cod var0 in 
          let* tm = do_app (i+1) t var0 in
          M.ret @@ Normal {ty ; tm}
        in 
        read_back_case_tree i body
      in 
      M.ret @@ NeNf.lam dom body
  | NfU -> 
    begin match t with
    | NfPi { dom ; cod } ->
      let var0 = NfNe { ty = dom ; ne = NeVar i } in
      let* dom  = read_back_pnf i NfU dom in
      let* cod = 
        do_clos (i+1) cod var0
        |> M.map (fun tm -> Normal { ty = NfU ; tm })
        |> read_back_case_tree i 
      in
      M.ret @@ NeNf.pi dom cod
    | NfBool -> 
      M.ret @@ NeNf.bool
    (* Type in Type ??? *)
    | NfU -> 
      M.ret @@ NeNf.univ
    | NfNe { ty = _ ; ne } -> 
      M.map (NeNf.ne_pnf NeNf.univ) (read_back_ne i ne)
    | _ -> failwith "Not a valid type"
    end
  | NfBool -> 
    begin match t with
    | NfTrue -> 
      M.ret @@ NeNf.btrue
    | NfFalse ->
      M.ret @@ NeNf.bfalse
    | NfNe { ty = _ ; ne } -> 
      let* tne = read_back_ne i ne in 
      let+ b = M.get_split tne in 
      if b then NeNf.btrue else NeNf.bfalse
    | _ -> failwith "Not a valid bool"
    end
  | NfNe { ne = ty ; _ } ->
    begin match t with
    | NfNe { ne ; _ } ->
      let* ty = 
        M.map (NeNf.ne_pnf NeNf.univ) @@ read_back_ne i ty
      in
      let* t = read_back_ne i ne in
      M.ret @@ NeNf.ne_pnf ty t
    | _ -> failwith "Not a valid element of a neutral type"
    end
  | _ -> failwith "Not a valid type"

and read_back_ne i ne =
  match ne with
  | NeVar k -> M.ret @@ NeNf.var (i - k - 1)
  | NeApp {fn ; arg = Normal { ty ; tm }} -> 
    let* f = read_back_ne i fn in
    let* arg = read_back_pnf i ty tm in
    M.ret @@ NeNf.app f arg



let norm (ctx : Tm.tm list) (ty : Tm.tm) (t : Tm.tm) : NeNf.pnf M.t =
  let* (i, env) = 
    let fold_fun ty m = 
      let* (i, env) = m in
      let* ty = eval i ty env in
      let vari = NfNe { ty ; ne = NeVar i } in
      M.ret @@ (i+1, vari :: env)
    in
    List.fold_right fold_fun ctx (M.ret (0, []))
  in 
  let* ty = eval i ty env in 
  let* tm = eval i t env in
  read_back_pnf i ty tm 


(*
and read_back_pnf i ty t =
  match t with
  | NfPi { dom ; cod } ->
    let var0 = NeNf { ty = dom ; ne = NeVar i } in
    let* dom  = read_back_pnf i NfU dom in
    let* cod = 
      do_clos (i+1) cod var0
      |> M.map (fun tm -> Normal { ty = NfU ; tm })
      |> read_back_case_tree i 
    in
    M.ret @@ NeNf.pi dom cod
  | NfLam t ->
    begin match ty with
    | NfPi { dom ; cod } -> 
      let var0 = NeNf { ty = dom ; ne = NeVar i } in
      let* dom  = read_back_pnf i NfU dom in
      let* body = 
        let body =
          let* ty = do_clos (i+1) cod var0 in 
          let* tm = do_clos (i+1) t var0 in
          Normal {ty ; tm}
        in 
        read_back_case_tree i body
      in 
      M.ret @@ NeNf.lam dom body
    | _ -> failwith "In RB pnf: not a Pi"
    end
  | NfBool -> 
    M.ret @@ NeNf.bool
  | NfU ->
    M.ret @@ NeNf.univ
  | NfNe { ty ; ne } -> 
    read_back_ne i ty ne
  | NfTrue -> 
    M.ret @@ NeNf.btrue
  | NfFalse ->
    M.ret @@ NeNf.bfalse

and read_back_ne i ty ne =
  match ty with
  | NfPi { dom ; cod } -> ?
  | NfU -> 
    match ne with
    | NeVar k -> NeNf.var (i - k - 1)
    | NeApp { fn ; arg } -> 
  | NfBool -> ?
  | NfNe { ty = _ ; ne } -> ?


*)