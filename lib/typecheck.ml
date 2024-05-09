open Term
open Nbe

open Splitter.Notations(M)
module D = Domain

module IT = InferTerm

type r = unit
let success : r M.t = M.ret ()
let fail : r M.t = M.fail

let ret x = M.ret x

let from_opt = function Some x -> M.ret x | None -> M.fail

(* let ( let$ ) (m : ('a option) M.t) (f : 'a -> ('b option) M.t) : ('b option) M.t = 
  let* opt = m in
  match opt with
  | None -> M.ret None
  | Some a -> f a *)

exception LocalEscape

let distr (m : 'a M.t) : ('a M.t) option =
  try Some Splitter.CT.(let* x = m in match x with None -> raise LocalEscape | Some x -> M.ret x)
  with LocalEscape -> None 

type ctx = { len : int ; ctx : tm list ; sctx : D.env }

let empty_ctx = { len = 0 ; ctx = [] ; sctx = [] }
let push { len ; ctx ; sctx } ty = 
  let* sty = eval len ty sctx in
  let vari = D.NfNe { ty = sty ; ne = D.NeVar len } in
  M.ret { len = len + 1; ctx = ty :: ctx ; sctx = vari :: sctx }

let conv_ty  (ctx : ctx) (a : tm) (b : tm) : r M.t =
  let* na = norm_ty ctx.len ctx.sctx a in
  let* nb = norm_ty ctx.len ctx.sctx b in 
  if na = nb then success else fail

(* let conv_sty i (a : D.t) (b : D.t) : bool M.t =
  let* na = read_back_pnf i NfU a in
  let* nb = read_back_pnf i NfU b in
  M.ret @@ (na = nb) *)

let rec reify_case_tree (m : (LevelNeOrd.t, tm) Splitter.CT.case_tree) : tm =
  let open Splitter.CT in
  match m with
  | Leaf t -> t
  | Split { lbl ; onl ; onr } ->
      Ifte { discr = (snd lbl :> tm) ; brT = reify_case_tree onl ; brF = reify_case_tree onr }



let rec infer (ctx : ctx) (t : IT.itm) : tm M.t =
  match t with
  | Var i -> 
    List.nth_opt ctx.ctx i
    |> Option.map (wkn (i+1)) 
    |> from_opt
  | Pi { dom ; cod } ->
    let* () = check ctx dom U in
    let* ctx' = push ctx (IT.itm_tm dom) in 
    let* () = check ctx' cod U in
    ret U
  | Lam { ty ; body } ->
    let* () = check_ty ctx ty in
    let ty = IT.itm_tm ty in
    let* ctx' = push ctx ty in
    let cod0 = infer ctx' body in
    let* cod = M.filter (fun lvl -> fst lvl = ctx'.len) cod0 in
    ret @@ Pi { dom = ty ; cod = reify_case_tree cod }
  | App { fn ; arg } ->
    let* fnty = infer ctx fn in
    let* fnty = norm_ty ctx.len ctx.sctx fnty in
    begin match (fnty :> tm) with
    | Pi { dom ; cod } -> 
      let* () = check ctx arg dom in
      ret (subst0 cod (IT.itm_tm arg))
    | _ -> M.fail
    end
  | Bool -> ret U
  | True -> ret Bool
  | False -> ret Bool
  | Ifte { discr ; brT ; brF } ->
    let* () = check ctx discr Bool in
    let* b = norm ctx.ctx Bool (IT.itm_tm discr) in
    begin match (b :> tm) with 
    | True -> infer ctx brT
    | False -> infer ctx brF
    | _ -> failwith "Not a valid boolean value"
    end
  | U -> M.fail

and check (ctx : ctx) (t : IT.itm) (ty : tm) : r M.t =
  let* ty' = infer ctx t in
  conv_ty ctx ty ty'

and check_ty (ctx : ctx) (ty : IT.itm) : r M.t =
  match ty with
  | Pi { dom ; cod } -> 
    let* () = check_ty ctx dom in
    let* ctx' = push ctx (IT.itm_tm dom) in
    check_ty ctx' cod
  | Bool -> success
  | U -> success
  | Ifte { discr ; brT ; brF } ->
    let* () = check ctx discr Bool in
    (* let$ () = check_ty ctx brT in
    let$ () = check_ty ctx brF in
    success *)
    let* b = norm ctx.ctx Bool (IT.itm_tm discr) in
    begin match (b :> tm) with 
    | True -> check_ty ctx brT
    | False -> check_ty ctx brF
    | _ -> failwith "Not a valid boolean value"
    end
  | t -> check ctx t U


let check_ctx (ctx : IT.itm list) : ctx M.t =
  let fold_fun ty m = 
    let* ctx = m in
    let* () = check_ty ctx ty in
    let* ctx' = push ctx (IT.itm_tm ty) in
    ret ctx'
  in
  List.fold_right fold_fun ctx @@ ret empty_ctx

let full_check_ty (ctx : IT.itm list) (ty : IT.itm) : bool =
  let mb = 
    let* ctx = check_ctx ctx in
    check_ty ctx ty
  in 
  mb = success

let full_check_tm (ctx : IT.itm list) (t : IT.itm) (ty : IT.itm) : bool =
  let mb = 
    let* ctx = check_ctx ctx in
    let* () = check_ty ctx ty in
    check ctx t (IT.itm_tm ty)
  in 
  mb = success

let full_check_tm_dbg (ctx : IT.itm list) (t : IT.itm) (ty : IT.itm) =
  let ctx' = check_ctx ctx in
  let ty' = let* ctx = ctx' in check_ty ctx ty in
  let t' = let* ctx = ctx' in check ctx t (IT.itm_tm ty) in 
  (ctx', ty', t', t' = success)

let full_infer (ctx : IT.itm list) (t : IT.itm) : (tm M.t) option =
  let mty =
    let* ctx = check_ctx ctx in
    infer ctx t
  in distr mty

