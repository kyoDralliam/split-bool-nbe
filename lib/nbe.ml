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

module M = TreeSplitter(LevelNeOrd)
module MN = Monad.Notations(M)
open MN

open Domain


let rec from_case_tree = function
  | CT.Leaf t -> NeNf.pnf_nf t
  | CT.Split {lbl ; onl ; onr } ->
    NeNf.case (snd lbl) (from_case_tree onl) (from_case_tree onr)

let rec do_app i (fn : t) (arg : t) =
  match fn with
  | NfLam c -> do_clos i c arg
  | NfNe { ty = NfPi {dom ; cod} ; ne } -> 
    let* ty = do_clos i cod arg in
    let arg = Normal { ty = dom ; tm = arg } in
    let ne = NeApp { fn = ne ; arg } in
    M.ret @@ NfNe { ty ; ne }
  | nf ->
    Format.fprintf Format.err_formatter "Not a function: %a" pp nf ;
    M.fail  "Not a function"

and do_clos i (Clos { env ; body }) arg = 
  eval i body (arg :: env)

and do_split : type a. int -> ne -> a M.t -> a M.t -> a M.t = 
  fun i ne brT brF ->
  let* tne = read_back_ne i ne in
  let (j, stne) = NeNf.to_canonical_index tne in
  M.split (i - j,stne) brT brF

and do_ifte : type a. int -> t -> a M.t -> a M.t -> a M.t =
  fun i b brT brF ->
    match b with
    | NfTrue -> brT
    | NfFalse -> brF
    | NfNe { ty = _ ; ne } ->
      do_split i ne brT brF
    | _ -> M.fail "Not a valid boolean value"

and eval i t env = 
  match t with
  | Tm.Var i -> 
    (* Format.printf "Var : %d, #|env| : %d@\n" i (List.length env) ;  *)
    M.ret @@ List.nth env i
  | Tm.Pi { dom ; cod } ->
    let* dom = eval i dom env in
    let cod = Clos { env ; body = cod } in
    M.ret @@ NfPi { dom; cod }
  | Tm.Lam body -> 
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
    do_ifte i b (eval i brT env) (eval i brF env)
    (* failwith "Discriminee does not evaluate to a boolean" *)
  | U -> 
    M.ret @@ NfU

(* and read_back_nf i nf = ? *)

and read_back_case_tree i m = 
  let+ ct = M.filter M.Map.empty (fun x -> assert (fst x <= i) ; fst x = i) m in
  from_case_tree ct

and read_back_ty i ty : NeNf.pnf M.t =
  match ty with
  | NfPi { dom ; cod } ->
    let var0 = NfNe { ty = dom ; ne = NeVar i } in
    let* dom  = read_back_ty i dom in
    let* cod = read_back_case_tree i (let* tm = do_clos (i+1) cod var0 in read_back_ty (i+1) tm) in
    M.ret @@ NeNf.pi dom cod
  | NfBool -> 
    M.ret @@ NeNf.bool
  | NfU -> 
    M.ret @@ NeNf.univ
  | NfNe { ty = _ ; ne } -> 
    M.map (fun x -> NeNf.ne_pnf NeNf.univ x) (read_back_ne i ne)
  | _ -> 
    M.fail "Not a valid code of universe"


and read_back_pnf i ty t : NeNf.pnf M.t =
  match ty with
  | NfPi { dom ; cod } ->
      let var0 = NfNe { ty = dom ; ne = NeVar i } in
      (* let* dom  = read_back_ty i dom in *)
      let* body = 
        let body =
          let* ty = do_clos (i+1) cod var0 in 
          let* tm = do_app (i+1) t var0 in
          read_back_pnf (i+1) ty tm
        in 
        read_back_case_tree i body
      in 
      M.ret @@ NeNf.lam body
  | NfU -> 
    begin match t with
    | NfPi { dom ; cod } ->
      let var0 = NfNe { ty = dom ; ne = NeVar i } in
      let* dom  = read_back_ty i dom in
      let* cod = 
        read_back_case_tree i (let* t = do_clos (i+1) cod var0 in read_back_ty (i+1) t)
      in
      M.ret @@ NeNf.pi dom cod
    | NfBool -> 
      M.ret @@ NeNf.bool
    | NfNe { ty = _ ; ne } -> 
      M.map (fun x -> NeNf.ne_pnf NeNf.univ x) (read_back_ne i ne)
    | NfU ->  
      M.fail "Type in Type"
    | _ -> 
      M.fail "Not a valid code of universe"
    end
  | NfBool -> do_ifte i t (M.ret NeNf.btrue) (M.ret NeNf.bfalse)
  | NfNe { ne = ty ; _ } ->
    begin match t with
    | NfNe { ne ; _ } ->
      let* ty = 
        M.map (fun x -> NeNf.ne_pnf NeNf.univ x) @@ read_back_ne i ty
      in
      let* t = read_back_ne i ne in
      M.ret @@ NeNf.ne_pnf ty t
    | _ -> 
      M.fail "Not a valid element of a neutral type"
    end
  | _ -> M.fail "Not a valid type"

and read_back_ne i ne : NeNf.ne M.t =
  match ne with
  | NeVar k -> M.ret @@ NeNf.var (i - k)
  | NeApp {fn ; arg = Normal { ty ; tm }} -> 
    let* f = read_back_ne i fn in
    let* arg = read_back_pnf i ty tm in
    M.ret @@ NeNf.app f arg


let norm_ty i (env : env) (ty : Tm.tm) : NeNf.pnf M.t =
  let* sty = eval i ty env in
  read_back_ty i sty

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