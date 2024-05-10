module D = Domain
open Nbe
open Bidir
open Nbe.MN
type sctx = D.nf list


let nf_tm = function | D.Normal x -> x.tm
let nf_ty = function | D.Normal x -> x.ty

let to_env (ctx : sctx) : D.env  = List.map nf_tm ctx

let success = M.ret ()
let from_opt = function Some x -> M.ret x | None -> M.fail

let empty_ctx = []
let push ctx sty = 
  let vari = D.NfNe { ty = sty ; ne = D.NeVar (List.length ctx) } in
  D.Normal { ty = sty ; tm  = vari } :: ctx


let conv_ty  (ctx : sctx) (a : D.t) (b : D.t) =
  let i = List.length ctx in
  let* na = read_back_ty i a in
  let* nb = read_back_ty i b in  
  if na = nb then success else M.fail




let rec check_ty (ctx : sctx) (t : ctm) : unit M.t =
  match t with
  | Pi {dom ; cod} -> 
    let* () = check_ty ctx dom in
    let* vdom = eval (List.length ctx) (ctm_tm dom) (to_env ctx) in
    check_ty (push ctx vdom) cod
  | U -> success
  | Bool -> success
  | IfTy {discr; tyT; tyF} ->
    let* () = check ctx discr D.NfBool in
    let* vdiscr = eval (List.length ctx) (ctm_tm discr) (to_env ctx) in
    do_ifte (List.length ctx) vdiscr (check_ty ctx tyT) (check_ty ctx tyF)
  | Inj t -> 
    let* tT = infer ctx t in
    begin match tT with
    | D.NfU -> success
    | _ ->  M.fail
    end
  | True | False | Lam _ -> M.fail

and check (ctx : sctx) (t : ctm) (ty : D.t): unit M.t =
  match t, ty with
  | Pi {dom ; cod}, NfU -> 
    let* () = check ctx dom D.NfU in
    let* vdom = eval (List.length ctx) (ctm_tm dom) (to_env ctx) in
    check (push ctx vdom) cod D.NfU
  | Bool, NfU -> success
  | True, NfBool -> success
  | False, NfBool -> success
  | Lam t, NfPi {dom ; cod} ->
    let ctx' = push ctx dom in
    let* vcod = do_clos (List.length ctx') cod (nf_tm @@ List.hd ctx') in
    check ctx' t vcod
  | Inj t, tT' -> 
    let* tT = infer ctx t in
    conv_ty ctx tT tT'
  | _, _ -> M.fail

and infer (ctx : sctx) (t : itm) : D.t M.t =
  match t with
  | Var i ->
    begin match List.nth_opt ctx i with
    | None -> M.fail
    | Some (Normal x) -> M.ret x.ty
    end
  | App { fn ; arg } ->
    let* fnT = infer ctx fn in
    begin match fnT with
    | D.NfPi { dom ; cod } -> 
      let* () = check ctx arg dom in
      let* varg = eval (List.length ctx) (ctm_tm arg) (to_env ctx) in
      do_clos (List.length ctx) cod varg
    | _ -> M.fail
    end
  | Ifte { discr ; brT ; brF } -> 
    let* () = check ctx discr NfBool in
    let* vdiscr = eval (List.length ctx) (ctm_tm discr) (to_env ctx) in
    do_ifte (List.length ctx) vdiscr (infer ctx brT) (infer ctx brF)
  | Ascr { tm ; ty } ->
    let* () = check_ty ctx ty in
    let* vty = eval (List.length ctx) (ctm_tm ty) (to_env ctx) in 
    let* () = check ctx tm vty in
    M.ret vty
    
let check_eval_ty ctx ty : D.t M.t = 
  let* () = check_ty ctx ty in
  eval (List.length ctx) (ctm_tm ty) (to_env ctx)

let check_ctx (ictx : ctm list) : sctx M.t =
  let check_eval_ty ty mctx = 
    let* ctx = mctx in
    let* vty = check_eval_ty ctx ty in
    M.ret @@ push ctx vty
  in
  List.fold_right check_eval_ty ictx (M.ret [])

let check_full (ictx : ctm list) (itm : ctm) (ity : ctm) : bool =
  success = 
    let* ctx = check_ctx ictx in
    let* ty = check_eval_ty ctx ity in
    check ctx itm ty
