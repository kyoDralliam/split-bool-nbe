module Tm = Term
module CT = CaseTree


open Domain

module CTE =
struct
  type err = string 
  type 'a t = (ne, 'a) CT.case_tree
  let ret = CT.ret
  let bind = CT.bind
end

module E = Monad.ExcT(CTE)

let ( let* ) = E.bind
let ( let+ ) m f = E.map f m


let rec do_app (fn : t) (arg : t) =
  match fn with
  | NfLam c -> do_clos c arg
  | NfNe { ty = NfPi {dom ; cod} ; ne } -> 
    let* ty = do_clos cod arg in
    let arg = Normal { ty = dom ; tm = arg } in
    let ne = NeApp { fn = ne ; arg } in
    E.ret @@ NfNe { ty ; ne }
  | nf ->
    E.fail ("Not a function: " ^ show nf)
     

and do_clos (Clos { env ; body }) arg = 
  eval body (arg :: env)

and do_ifte : type a. t -> a E.t -> a E.t -> a E.t =
  fun b onl onr ->
    match b with
    | NfTrue -> onl
    | NfFalse -> onr
    | NfNe { ty = _ ; ne } ->
      CT.Split { lbl = ne ; onl ; onr }
    | _ -> E.fail "Not a boolean value"

and eval t env = 
  match t with
  | Tm.Var i -> 
    begin match List.nth_opt env i with
    | Some x -> E.ret x
    | None -> E.fail (Format.sprintf "Unbound variable %d, #|env| = %d" i (List.length env))
    end
  | Tm.Pi { dom ; cod } ->
    let* dom = eval dom env in
    let cod = Clos { env ; body = cod } in
    E.ret @@ NfPi { dom; cod }
  | Tm.Lam body -> 
    E.ret @@ NfLam (Clos { env ; body })
  | Tm.App {fn ; arg} ->
    let* f = eval fn env in
    let* arg = eval arg env in
    do_app f arg
  | Tm.Bool ->
    E.ret @@ NfBool
  | Tm.True ->
    E.ret @@ NfTrue
  | Tm.False ->
    E.ret @@ NfFalse
  | Tm.Ifte { discr ; brT ; brF } ->
    let* b = eval discr env in
    do_ifte b (eval brT env) (eval brF env)
  | U -> 
    E.ret @@ NfU
