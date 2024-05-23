module D = DomainCbn
module CT = CaseTree

let curry f (x,y) = f x y


let ( let$ ) = Option.bind

open Bidir
module NeNf = Term.NeNf

open D.Quote
module M = D.Quote.M
module E =  D.Eval.E
open MN

let guard b err_msg th = if b then th () else M.fail err_msg


module SCtx = 
struct
  type t = {
    ctx : D.comp list ;
    len : int ;
    env : D.env ;
    cstr : bool M.Map.t
  } [@@deriving show]

  let empty = { ctx = [] ; len = 0 ; env = [] ; cstr = M.Map.empty }

  let push ctx (sty : D.vl E.t) =
    let vari : D.vl E.t = 
      let open D.Eval in
      let+ ty = sty in 
      let ne = D.NeVar ctx.len in
      D.NfNe {ty ; ne}
    in
    { ctx with 
      ctx = sty :: ctx.ctx ; 
      len = ctx.len + 1;
      env = vari :: ctx.env }

  let force (ne,b) ctx = { ctx with cstr = M.Map.add ne b ctx.cstr}
  let force_all cstrs ctx = List.fold_right force cstrs ctx 
  let force_cstrs cstrs ctx = { ctx with cstr = M.Map.union (fun _ x _ -> Some x) ctx.cstr cstrs }
end



let nf_tm = function | D.Normal x -> x.tm
let nf_ty = function | D.Normal x -> x.ty

let success = M.ret ()

let empty_ctx = []

type sty = D.vl M.t

let eval ctx t = D.Eval.eval (ctm_tm t) ctx.SCtx.env

let to_sty (ctx : SCtx.t) (vty : D.comp) : sty  =
  read_back_m ctx.cstr ctx.len M.ret vty



let conv_ty (ctx : SCtx.t) (a : D.vl M.t) (b : D.vl M.t) =
  (* reify_ty ctx.cstr ctx.len a = reify_ty ctx.cstr ctx.len b *)
  (* ERROR ! We shouldn't be able to compare two M.t structurally !!! They are not yet normalized ! *)
  (* Instead use the provided comparison function *)
  let norm_ty ty = M.bind ty (read_back_ty ctx.cstr ctx.len) in
  M.equiv ctx.cstr (norm_ty a) (norm_ty b)

let rec check_ty (ctx : SCtx.t) (t : ctm) : bool =
  match t with
  | Pi {dom ; cod} -> 
    check_ty ctx dom &&
    let vdom = eval ctx dom in
    check_ty (SCtx.push ctx vdom) cod
  | U -> true
  | Bool -> true
  | IfTy {discr; tyT; tyF} ->
    check_head ctx discr D.NfBool &&
    let@ (cstrs,b) = norm_tm ctx.cstr ctx.env ctx.len (E.ret D.NfBool) (ctm_tm discr) , ctx.cstr in 
    let ctx = SCtx.force_cstrs cstrs ctx in
    begin match (b :> Tm.tm) with
    | Tm.True -> check_ty ctx tyT
    | Tm.False -> check_ty ctx tyF
    | _ -> false
    (* should not be a neutral case *)
    end
  | Inj t -> 
    let@ (_cstrs, tT) = infer ctx t, ctx.cstr in
    tT = D.NfU
  | True | False | Lam _ -> false

and check (ctx : SCtx.t) (t : ctm) (ty : D.vl M.t) : bool =
  match t with
  | Inj t -> 
    let tT = infer ctx t in
    conv_ty ctx tT ty
  | _ -> 
    let@ (cstrs, ty) = ty, ctx.cstr in
    let ctx = SCtx.force_cstrs cstrs ctx in
    check_head ctx t ty

and check_head (ctx : SCtx.t) (t : ctm) (ty : D.vl): bool =
  match t, ty with
  | Pi {dom ; cod}, NfU -> 
    check_head ctx dom D.NfU &&
    let vdom = eval ctx dom in
    check_head (SCtx.push ctx vdom) cod D.NfU
  | Bool, NfU -> true
  | True, NfBool -> true
  | False, NfBool -> true
  | Lam t, NfPi {dom ; cod} ->
    let ctx' = SCtx.push ctx (E.ret dom) in
    let vcod = to_sty ctx' @@ D.Eval.do_clos cod (List.hd @@ ctx'.env) in
    check ctx' t vcod
  | Inj t, _ -> 
    let tT = infer ctx t in
    conv_ty ctx tT (M.ret ty)
  | _, _ -> false

and infer (ctx : SCtx.t) (t : itm) : sty =
  match t with
  | Var i ->
    let default = M.fail @@ Format.sprintf "Unbound variable %d" i in
    Option.value (Option.map (to_sty ctx) @@ List.nth_opt ctx.ctx i) ~default
  | App { fn ; arg } ->
    let fnT = infer ctx fn in
    let isPi (_, ty) = match ty with D.NfPi _ -> true | _ -> false in
    let proj_dom ty = match ty with D.NfPi x -> x.dom | _ -> assert false in
    guard (M.forall ctx.cstr isPi fnT) "Not a Π" @@ fun () ->
    let dom = M.map proj_dom fnT in
    guard (check ctx arg dom) "Domain ill formed"  @@ fun () ->
    let* ty = fnT in 
    begin match ty with 
    | D.NfPi x -> to_sty ctx @@ D.Eval.do_clos x.cod (eval ctx arg) 
    | _ -> assert false
    end
  | Ifte { discr ; brT ; brF } -> 
    guard (check_head ctx discr D.NfBool) "Discriminee is not a bool" @@ fun () ->
    let* b = to_sty ctx @@ eval ctx discr in
    let* b = read_back_pnf ctx.cstr ctx.len D.NfBool b in
    begin match (b :> Tm.tm) with
    | True -> infer ctx brT
    | False -> infer ctx brF
    | _ -> M.fail "Not a boolean value when typechecking"
    end
  | Ascr { tm ; ty } ->
    guard (check_ty ctx ty) "Ascription does not typecheck" @@ fun () ->
    let vty = to_sty ctx @@ eval ctx ty in 
    guard (check ctx tm vty) "Ascription checking failed" @@ fun () ->
    vty


open Monad.Notations(struct include Option let ret = some end)

 


let check_ctx (ctx : ctm list) : SCtx.t option =
  let check_eval_push cty sctxopt = 
    let* sctx = sctxopt in
    if check_ty sctx cty 
    then Some (SCtx.push sctx (eval sctx cty))
    else None
  in
  List.fold_right check_eval_push ctx (Some SCtx.empty)


let check_full (ctx : ctm list) (tm : ctm) (ty : ctm) : bool =
  Option.value ~default:false @@
  let+ sctx = check_ctx ctx in
  check_ty sctx ty && check sctx tm (to_sty sctx @@ eval sctx ty)

let check_full_debug (ctx : ctm list) (tm : ctm) (ty : ctm) : (SCtx.t * sty * bool) option =
  let+ sctx = check_ctx ctx in
  if check_ty sctx ty
  then
    let vty = to_sty sctx @@ eval sctx ty in
    (sctx, vty, check sctx tm vty)
  else (sctx, M.fail "Not well formed type", false)

let infer_full_debug (ctx : ctm list) (tm : itm) : (SCtx.t * sty) option =
  let+ sctx = check_ctx ctx in
  (sctx, infer sctx tm)

let check_ty_full_debug (ctx : ctm list) (ty : ctm) = 
  let+ sctx = check_ctx ctx in
  let b = check_ty sctx ty in
  (sctx, b, if b then eval sctx ty else E.fail "Not well formed type")

let conv_ty_full_debug (ctx : ctm list) (ty1 : ctm) (ty2 : ctm) =
  let+ sctx = check_ctx ctx in
  let norm_ty t = reify_ty sctx.cstr sctx.len (eval sctx t) in
  let ty1 = norm_ty ty1 in
  let ty2 = norm_ty ty2 in
  (sctx, M.equiv sctx.cstr ty1 ty2, ty1, ty2)



