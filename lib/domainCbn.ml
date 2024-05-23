module Tm = Term
module CT = CaseTree

module E = 
struct
  include Either
  let pp left right = Format.pp_print_either ~left ~right
end

type nfvl = Normal of { ty : vl ; tm : vl }

and vl =
  | NfPi of { dom : vl ; cod : clos }
  | NfLam of clos
  | NfBool
  | NfU
  | NfNe of { ty : vl ; ne : nevl }
  | NfTrue
  | NfFalse

and nevl =
  | NeVar of int
  | NeApp of { fn : nevl ; arg : nfvl }

and comp = (nevl, (vl,string) E.t) CT.case_tree

and env = comp list

and clos = Clos of { env : env ; body : Tm.tm }
[@@deriving show]


module Eval = 
struct 
  module CTE =
  struct
    type err = string 
    type 'a t = (nevl, 'a) CT.case_tree
    let ret = CT.ret
    let bind = CT.bind
  end

  module E = Monad.ExcT(CTE)
  include Monad.Notations(E)


  let rec do_app (fn : vl) (arg : comp) =
    match fn with
    | NfLam c -> do_clos c arg
    | NfNe { ty = NfPi {dom ; cod} ; ne } -> 
      let* ty = do_clos cod arg in
      let* arg = arg in
      let arg = Normal { ty = dom ; tm = arg } in
      let ne = NeApp { fn = ne ; arg } in
      E.ret @@ NfNe { ty ; ne }
    | nf ->
      E.fail ("Not a function: " ^ show_vl nf)
      
  and do_clos (Clos { env ; body }) arg = 
    eval body (arg :: env)

  and do_ifte : type a. comp -> a E.t -> a E.t -> a E.t =
    fun discr onl onr ->
      let* b = discr in
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
      | Some x -> x
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
      do_app f (eval arg env)
    | Tm.Bool ->
      E.ret @@ NfBool
    | Tm.True ->
      E.ret @@ NfTrue
    | Tm.False ->
      E.ret @@ NfFalse
    | Tm.Ifte { discr ; brT ; brF } ->
      do_ifte (eval discr env) (eval brT env) (eval brF env)
    | U -> 
      E.ret @@ NfU

end


module Quote = 
struct

  module NeNf = Tm.NeNf

  module LevelNeOrd  =
  struct
    type t = int * NeNf.ne
    [@@deriving show]
    let compare (k1,ne1) (k2,ne2) =
      let ck = Int.compare k1 k2 in
      if ck = 0 then Tm.NeOrd.compare ne1 ne2 else ck
  end

  module M = Splitter.TreeSplitterLazy(LevelNeOrd)
  module MN = struct include Monad.Notations(M) let (let@) (m,env) p = M.forall env p m  end
  open MN

  let curry f (x,y) = f x y

  let from_case_tree = CT.fold (fun lbl -> NeNf.case (snd lbl)) NeNf.pnf_nf

  let rec read_back_case_tree env i m = 
    let+ ct = M.filter env (fun x -> assert (fst x <= i) ; fst x = i) m in
    from_case_tree ct

  and read_back_bool_ne : type a. bool M.Map.t -> int -> nevl -> a M.t -> a M.t -> a M.t =
    fun env i nev onl onr ->
    let* ne = read_back_ne env i nev in
    let (j, stne) = NeNf.to_canonical_index ne in
    M.split (i - j,stne) onl onr

  and read_back_m : type a b. bool M.Map.t -> int -> (a -> b M.t) -> a Eval.E.t -> b M.t =
    fun env i f em ->
    CT.fold (read_back_bool_ne env i) (function Either.Left x -> f x | Either.Right s -> M.fail s) em
    
  and reify_ty env i = read_back_m env i (read_back_ty env i)
  and reify env i = read_back_m env i (curry @@ read_back_pnf env i)


  and read_back_ty env i ty : NeNf.pnf M.t =
    match ty with
    | NfPi { dom ; cod } ->
      let var0 = Eval.E.ret (NfNe { ty = dom ; ne = NeVar i }) in
      let* dom  = read_back_ty env i dom in
      let* cod = read_back_case_tree env i (reify_ty env (i+1) (Eval.do_clos cod var0)) in 
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
        let var0 = Eval.E.ret @@ NfNe { ty = dom ; ne = NeVar i } in
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
        let var0 = Eval.E.ret @@ NfNe { ty = dom ; ne = NeVar i } in
        let* dom  = read_back_ty env i dom in
        let* cod = read_back_case_tree env i (reify_ty env (i+1) (Eval.do_clos cod var0)) in 
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



  let norm_ty cstr (env : env) (ty : Tm.tm) : NeNf.pnf M.t =
    let i = List.length env in
    reify_ty cstr i (Eval.eval ty env)

  let norm_tm cstr (env : env) i ty (t : Tm.tm) : NeNf.pnf M.t =
    reify cstr i @@
      let open Eval in 
      let* ty = ty in 
      let* tm = eval t env in
      E.ret (ty,tm)

  let norm cstr (env : env) (ty : Tm.tm) (t : Tm.tm) : NeNf.pnf M.t =
    let i = List.length env in
    reify cstr i @@
      let open Eval in 
      let* ty = eval ty env in 
      let* tm = eval t env in
      E.ret (ty,tm)
end 