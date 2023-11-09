open Term
open Nbe

open Splitter.Notations(M)
module D = Domain


type r = unit option
let success : r M.t = M.ret @@ Some ()
let fail : r M.t = M.ret None

let ret x = M.ret @@ Some x

let ( let$ ) (m : ('a option) M.t) (f : 'a -> ('b option) M.t) : ('b option) M.t = 
  let* opt = m in
  match opt with
  | None -> M.ret None
  | Some a -> f a

type ctx = { len : int ; ctx : tm list ; sctx : D.env }

let empty_ctx = { len = 0 ; ctx = [] ; sctx = [] }
let push { len ; ctx ; sctx } ty = 
  let* sty = eval len ty sctx in
  let vari = D.NfNe { ty = sty ; ne = D.NeVar len } in
  M.ret { len = len + 1; ctx = ty :: ctx ; sctx = vari :: sctx }

let rec wk k t n = 
  match t with
  | Var i -> if i <= k then Var i else Var (i+n)
  | Pi {dom; cod} -> Pi { dom = wk k dom n ; cod = wk (k+1) cod n }
  | Lam {ty ; body} -> Lam {ty = wk k ty n ; body = wk (k+1) body n }
  | App {fn ; arg} -> App {fn = wk k fn n ; arg = wk k arg n}
  | Ifte { discr ; brT ; brF } -> 
    Ifte { discr = wk k discr n ; brT = wk k brT n ; brF = wk k brF n }
  | cst -> cst

let wk1 t = wk 0 t 1

let rec subst k t u = 
  match t with
  | Var i -> if i = k then u else Var i
  | Pi {dom; cod} -> Pi { dom = subst k dom u ; cod = subst (k+1) cod (wk1 u) }
  | Lam {ty ; body} -> Lam {ty = subst k ty u ; body = subst (k+1) body (wk1 u) }
  | App {fn ; arg} -> App {fn = subst k fn u ; arg = subst k arg u}
  | Ifte { discr ; brT ; brF } -> 
    Ifte { discr = subst k discr u ; brT = subst k brT u ; brF = subst k brF u }
  | cst -> cst

let subst0 t u = subst 0 t u

let conv_ty  (ctx : ctx) (a : tm) (b : tm) : r M.t =
  let* na = norm_ty ctx.len ctx.sctx a in
  let* nb = norm_ty ctx.len ctx.sctx b in 
  if na = nb then success else fail

(* let conv_sty i (a : D.t) (b : D.t) : bool M.t =
  let* na = read_back_pnf i NfU a in
  let* nb = read_back_pnf i NfU b in
  M.ret @@ (na = nb) *)



let rec infer (ctx : ctx) (t : tm) : (tm option) M.t =
  match t with
  | Var i -> M.ret @@ List.nth_opt ctx.ctx i
  | Pi { dom ; cod } ->
    let$ () = check ctx dom U in
    let* ctx' = push ctx dom in 
    let$ () = check ctx' cod U in
    ret U
  | Lam { ty ; body } ->
    let$ () = check_ty ctx ty in
    let* ctx' = push ctx ty in
    let$ cod = infer ctx' body in
    ret @@ Pi { dom = ty ;  cod }
  | App { fn ; arg } ->
    let$ fnty = infer ctx fn in
    let* fnty = norm_ty ctx.len ctx.sctx fnty in
    begin match (fnty :> tm) with
    | Pi { dom ; cod } -> 
      let$ () = check ctx arg dom in
      ret (subst0 cod arg)
    | _ -> M.ret None
    end
  | Bool -> ret U
  | True -> ret Bool
  | False -> ret Bool
  | Ifte { discr ; brT ; brF } ->
    let$ () = check ctx discr Bool in
    let$ tyT = infer ctx brT in
    let$ tyF = infer ctx brF in
    ret @@ Ifte {discr; brT = tyT ; brF = tyF}
  | U -> M.ret None

and check (ctx : ctx) (t : tm) (ty : tm) : r M.t =
  let$ ty' = infer ctx t in
  conv_ty ctx ty ty'

and check_ty (ctx : ctx) (ty : tm) : r M.t =
  match ty with
  | Pi { dom ; cod } -> 
    let$ () = check_ty ctx dom in
    let* ctx' = push ctx dom in
    check_ty ctx' cod
  | Bool -> success
  | U -> success
  | t -> check ctx t U


let check_ctx (ctx : tm list) : (ctx option) M.t =
  let fold_fun ty m = 
    let$ ctx = m in
    let$ () = check_ty ctx ty in
    let* ctx' = push ctx ty in
    ret ctx'
  in
  List.fold_right fold_fun ctx @@ ret empty_ctx

let full_check_ty (ctx : tm list) (ty : tm) : bool =
  let mb = 
    let$ ctx = check_ctx ctx in
    check_ty ctx ty
  in 
  mb = success

let full_check_tm (ctx : tm list) (t : tm) (ty : tm) : bool =
  let mb = 
    let$ ctx = check_ctx ctx in
    let$ () = check_ty ctx ty in
    check ctx t ty
  in 
  mb = success
