open Splitter

module Tm = Term
module NeNf = Tm.NeNf

module LevelNeOrd : Map.OrderedType with type t = (int * NeNf.ne) =
struct
  type t = int * NeNf.ne
  let compare (k1,ne1) (k2,ne2) =
    let ck = Int.compare k1 k2 in
    if ck = 0 then Tm.NeOrd.compare ne1 ne2 else ck
end

module M = TreeSplitter(LevelNeOrd)
module MN = Notations(M)
open MN

open Domain


let rec from_case_tree = function
  | Leaf t -> NeNf.pnf_nf t
  | Split {lbl ; onl ; onr } ->
    NeNf.case (snd lbl) (from_case_tree onl) (from_case_tree onr)

let rec do_app i (fn : t) (arg : t) =
  match fn with
  | NfLam c -> do_clos i c arg
  | NfNe { ty = NfPi {dom ; cod} ; ne } -> 
    let* ty = do_clos i cod arg in
    let arg = Normal { ty = dom ; tm = arg } in
    let ne = NeApp { fn = ne ; arg } in
    M.ret @@ NfNe { ty ; ne }
  | _ -> failwith "Not a function"

and do_clos i (Clos { env ; body }) arg = 
  eval i body (arg :: env)

and do_split : type a. int -> ne -> a -> a -> a M.t = 
  fun i ne brT brF ->
  let* tne = read_back_ne i ne in
  let (j, stne) = NeNf.to_canonical_index tne in
  M.split (i - j,stne) (M.ret brT) (M.ret brF)

and eval i t env = 
  match t with
  | Tm.Var i -> 
    (* Format.printf "Var : %d, #|env| : %d@\n" i (List.length env) ;  *)
    M.ret @@ List.nth env i
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
      let* onT = eval i brT env in
      let* onF = eval i brF env in
      do_split i ne onT onF
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
  let+ ct = M.filter (fun x -> fst x = i) m in
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
      M.map (fun x -> NeNf.ne_pnf NeNf.univ x) (read_back_ne i ne)
    | _ -> failwith "Not a valid code of universe"
    end
  | NfBool -> 
    begin match t with
    | NfTrue -> 
      M.ret @@ NeNf.btrue
    | NfFalse ->
      M.ret @@ NeNf.bfalse
    | NfNe { ty = _ ; ne } -> 
      do_split i ne NeNf.btrue NeNf.bfalse
    | _ -> failwith "Not a valid bool"
    end
  | NfNe { ne = ty ; _ } ->
    begin match t with
    | NfNe { ne ; _ } ->
      let* ty = 
        M.map (fun x -> NeNf.ne_pnf NeNf.univ x) @@ read_back_ne i ty
      in
      let* t = read_back_ne i ne in
      M.ret @@ NeNf.ne_pnf ty t
    | _ -> failwith "Not a valid element of a neutral type"
    end
  | _ -> failwith "Not a valid type"

and read_back_ne i ne : NeNf.ne M.t =
  match ne with
  | NeVar k -> M.ret @@ NeNf.var (i - k)
  | NeApp {fn ; arg = Normal { ty ; tm }} -> 
    let* f = read_back_ne i fn in
    let* arg = read_back_pnf i ty tm in
    M.ret @@ NeNf.app f arg


let norm_ty i (env : env) (ty : Tm.tm) : NeNf.pnf M.t =
  let* sty = eval i ty env in
  read_back_pnf i NfU sty

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