
(*

module Domain =
struct

type nft = Normal of { ty : nf ; tm : nf }

and nfbasety = NfbtU

and pnf =
  | NfPi of { dom : pnf ; cod : nf }
  | NfLam of nf
  | NfBool
  | NfBaseTy of nfbasety
  | NfNe of { ty : nfbasety ; ne : ne }
  | NfTrue
  | NfFalse

and ne =
  | NeVar of int (* level *)
  | NeApp of { fn : ne ; arg : pnf }

and nf = (ne, pnf) case_tree [@@ deriving ord]

module NeOrd : Map.OrderedType = struct type t = ne let compare = compare_ne end

type env = list nft

let nfU = NfBaseTy NfU

end

module M = TreeSplitter(Domain.NeOrd)

open Domain

let rec ne_contains_var k ne =
  match ne with
  | NeVar n -> k = n
  | NeApp { fn ; arg } ->
    ne_contains_var k fn && pnf_contains_var k arg

and pnf_contains_var k pnf =
  match pnf with
  | NfPi { dom ; cod } ->
    pnf_contains_var k dom && nf_contains_var k cod
  | NfLam t -> nf_contains_var k t
  | NfNe { ne ; _ } -> ne_contains_var k ne
  | _ -> false

and nf_contains_var k = M.exists (pnf_contains_var k)

let combine (m n : 'a M.t) : 'a M.t = let* x = m in let+ y = n in (x,y)

let rec pnf_read_back (n : int) (ty : pnf) (t : pnf) : Tm.tm M.t =
  match ty with
  | NfPi dom cod ->
    let var0 = mk_var dom n in
    let* dom = pnf_read_back n dom in
    let body =
      let* cod = do_app cod var0 in
      let* body = do_app t var0 in
      pnf_read_back (n+1) cod body
    in
    let* body_ct = M.filter (ne_contains_var n) body in
    let+ body = read_back_case_tree (n+1) cod_body_ct in
    Tm.Lam dom rb_body
  | NfBool ->
    begin match t with
      | NfTrue -> M.ret Tm.True
      | NfFalse -> M.ret Tm.False
      | NfNe { ne ; _ } -> ne_read_back n ne
      | _ -> failwith "not a bool"
    end
  | NfBaseTy NfbtU ->
    begin match t with
      | NfBool -> M.ret Tm.Bool
      | NfPi { dom ; cod } ->
        let var0 = mk_var dom n in
        let* dom = pnf_read_back n dom in
        let* cod_ct = M.filter (ne_contains_var n) (combine (M.ret nfU) (do_app cod var0)) in
        let+ cod = read_back_case_tree (n+1) cod_ct in
        Tm.Pi dom rb_cod
      | NfBaseTy NfbtU -> failwith "Type in type"
      | _ -> failwith "not a type"
    end
  | NfNe _ ->
    begin match t with
    | NfNe { ne ; _ } -> ne_read_back n ne
    | _ -> failwith "Not a value of a neutral type"
    end
  | _ -> failwith "Not a type"

and ne_read_back (n : int) (ne : ne) : Tm.tm M.t =
  match ne with
  | NeVar k -> M.ret (Tm.Var (n - k - 1))
  | NeApp { fn ; arg } ->
    let* f = ne_read_back n fn in
    let+ a = pnf_read_back n arg in
    Tm.App f a

and read_back_case_tree (n : int) (ct : (ne, pnf * pnf) case_tree) : Tm.tm M.t =
  match t with
  | Leaf (ty, tm) -> pnf_read_back n ty tm
  | Split { lbl ; onl ; onr } ->
    let* discr = ne_read_back n lbl in
    let* brT = read_back_case_tree n onl in
    let* brF = read_back_case_tree n onr in
    M.ret (Tm.Ifte {discr; brT ; brF})






let rec reflect (l : int) (env : env) (ne : ne) (t : pnf) : pnf M.t =
  match t with
  | NfBool -> let+ b = M.get_split ne in if b then NeTrue else NeFalse
  | NfBaseTy ty -> M.ret (NfNe { ty ; ne })
  | NfPi { dom ; cod } ->
    let var0 = reflect (NeVar (l+1)) dom
    let cod = eval (l+1) (mk_var dom (l+1) :: env) cod NfU in

    NfLam 

let rec eval (i : int) (rho : env) 





type nf = Normal of { ty : t ; tm : t }

and t =
  | NfPi of { dom : t ; cod : clos }
  | NfLam of clos
  | NfBool
  | NfU
  | NfNe of { ty : t ; ne : ne }
  (* | NfCase { discr : ne ; onl : nf ; onr : nf } *)

and ne =
  | NeVar of int
  | NeApp of { fn : ne ; arg : v }
  | NeTrue
  | NeFalse

and v =
  | VPi of v * v case_tree
  | VLam of v case_tree
  | VBool
  | VU
  | VNe of ne

and env = t list

and clos = Clos of { env : env ; body : Tm.tm } [@@ deriving ord]

and 'a case_tree =
  | Split of { discr : ne ; onl : 'a case_tree ; onr : 'a case_tree }
  | Leaf of 'a



let mk_var ty i = NfNe { ty ; ne = NeVar i }


let rec contains_ne_var i ne =
  match ne with
  | NeVar k -> i = k
  | NeApp { fn ; arg } -> contains_ne_var i fn || contains_v_var i arg
  | NeTrue | NeFalse -> false
and contains_v_var i (v : v) =
  match v with
  | VPi (dom, cod) -> contains_v_var i dom || contains_case_tree_var (i+1) cod
  | VLam t -> contains_case_tree_var (i+1) t
  | VNe ne -> contains_ne_var i ne
  | VBool | VU -> false
and contains_case_tree_var i ct =
  match ct with
  | Leaf t -> contains_v_var i t
  | Split { discr ; onl ; onr } ->
    contains_ne_var i discr ||
    contains_case_tree_var i onl ||
    contains_case_tree_var i onr







module Nbe (M : NeSplitter) = struct

exception FailedNbe of string

let ( let+ ) m f = M.map f m
let ( let* ) = M.bind

let ne_from_bool b =
  if b then NeTrue else NeFalse

let split_bool ty ne =
  match ty with
  | NfBool ->
    let+ b = M.get_split ne in
    NfNe { ty ; ne = ne_from_bool b }
  | ty -> M.ret (NfNe { ty ; ne })

let rec do_app n fn arg : t M.t =
  match fn with
  | NfLam c -> do_clos c arg
  | NfNe { ty ; ne } ->
    begin match ty with
      | NfPi { dom ; cod} ->
        let* arg = force n dom arg in
        let ne = NeApp { fn = ne ; arg } in
        let* r = do_clos cod arg in
        split_bool r ne
      | _ -> raise (FailedNbe "In do_app, not a Pi")
    end
  | _ -> raise (FailedNbe "In do_app, not a function")

and do_clos (Clos { env ; body ; ct = _ }) arg : t M.t =
  eval body (arg :: env)

and do_case b onl onr =
  match b with
  | NeTrue -> M.ret onl
  | NeFalse -> M.ret onr
  | ne ->
    let+ b = M.get_split ne in
    if b then onl else onr

and force (n : int) (ty x : t) : v M.t =
  match ty with
  | NfPi {dom ; cod } ->
    let arg = mk_var dom size in
    let cod = force_clos (n+1) cod arg in
    let t = force do_app x arg in
    let+ ct = M.filter (contains_ne_var size) (do_app tm arg) in
    let body = read_back_case_tree (size+1) cod ct in

  | _ -> 

and eval tm env : t M.t =
  match tm with
  | Tm.Var i -> M.ret (List.nth env i)
  | Tm.U -> M.ret NfU
  | Tm.Pi { dom ; cod } ->
    let* dom = eval dom env in
    let+ cod = eval_clos_body dom cod env in
    NfPi { dom ; cod }
  | Tm.Lam { ty ; body } ->
    let* ty = eval ty env in
    let+ clos = eval_clos_body ty body env in
    NfLam clos
  | Tm.App { fn ; arg } ->
    let* fn = eval fn env in
    let* arg = eval arg env in
    do_app fn arg
  | Tm.Bool -> M.ret NfBool
  | Tm.True -> M.ret (NfNe { ty = NfBool ; ne = NeTrue })
  | Tm.False -> M.ret (NfNe { ty = NfBool ; ne = NeFalse })
  | Tm.Ifte { discr ; brT ; brF } ->
    let* b = eval discr env in
    begin match b with
    | NfNe { ty = _ ; ne } ->
      let* onl = eval brT env in
      let* onr = eval brF env in
      do_case ne onl onr
    | _ -> raise (FailedNbe "Boolean not evaluating to a neutral")
    end


let rec read_back size (Normal { ty ; tm } : nf) : Tm.tm M.t =
  match ty, tm with
  | NfPi { dom ; cod = Clos c }, _ ->
    let* ty = read_back size (Normal { ty = NfU ; tm = dom}) in
    let cod = read_back_case_tree (size+1) c.ct in
    let arg = mk_var dom size in
    let+ ct = M.filter (contains_ne_var size) (do_app tm arg) in
    let body = read_back_case_tree (size+1) cod ct in
    Tm.Lam { ty ; body }
  | _ -> failwith "todo"

and read_back_case_tree size ty m : Tm.tm M.t =
  match m with
  | Leaf tm -> read_back size (Normal { ty ; tm })
  | Split { discr ; onl ; onr } ->
    Tm.Ifte {
      discr = read_back_ne size discr ;
      brT = read_back_case_tree size onl ;
      brF = read_back_case_tree size onr
    }
and read_back_ne size ne =
  match ne with
  | NeVar i -> Tm.Var i
  | NeApp { fn ; arg } -> Tm.App { fn = read_back_ne size fn ; arg = read_back size arg }
  | NeTrue -> Tm.True
  | NeFalse -> Tm.False

end

*)