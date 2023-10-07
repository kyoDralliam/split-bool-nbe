
module Tm =
struct

type tm =
 | Var of int
 | Pi of { dom : tm ; cod : tm }
 | Lam of { ty : tm ; body : tm }
 | App of { fn : tm ; arg : tm }
 | Bool
 | True
 | False
 | Ifte of { discr : tm ; brT : tm ; brF : tm }
 | U [@@ deriving ord]

let rec contains_var i t =
  match t with
  | Var k -> i = k
  | Pi { dom ; cod } -> contains_var i dom || contains_var (i+1) cod
  | Lam { ty ; body } -> contains_var i ty || contains_var (i+1) body
  | App { fn ; arg } -> contains_var i fn || contains_var i arg
  | Ifte { discr ; brT ; brF } ->
    contains_var i discr || contains_var i brT || contains_var i brF
  | Bool | True | False | U -> false

end

type nf = Normal of { ty : t ; tm : t }

and t =
  | NfPi of { dom : t ; cod : clos }
  | NfLam of clos
  | NfBool
  | NfU
  | NfNe of { ty : t ; ne : ne }
  (* | NfCase { discr : ne ; on_true : nf ; on_false : nf } *)

and ne =
  | NeVar of int
  | NeApp of { fn : ne ; arg : nf }
  | NeTrue
  | NeFalse

and env = t list

and clos = Clos of { env : env ; body : Tm.tm } [@@ deriving ord]

and 'a case_tree =
  | Split of { discr : ne ; on_true : 'a case_tree ; on_false : 'a case_tree }
  | Leaf of 'a




module type NeSplitter = sig
  type 'a t
  val ret : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  (* val lookup : ne -> (bool option) t *)
  (* val split : ne -> unit t *)
  val get_split : ne -> bool t
  val filter : (ne -> bool) -> 'a t -> ('a case_tree) t
end

module M : NeSplitter =
struct

  module M = Map.Make(struct type t = ne let compare = compare_ne end)

  type 'a t = 'a case_tree

  let ret x = Leaf x

  let rec normalize (env : bool M.t) (m : 'a t) =
    match m with
    | Leaf x -> Leaf x
    | Split { discr ; on_true ; on_false } ->
      match M.find_opt discr env with
      | None -> Split {
          discr ;
          on_true = normalize (M.add discr true env) on_true ;
          on_false = normalize (M.add discr false env) on_false
        }
      | Some true -> normalize env on_true
      | Some false -> normalize env on_false

  let rec bind_aux m f =
    match m with
    | Leaf x -> f x
    | Split r -> Split {
        r with
        on_true = bind_aux r.on_true f ;
        on_false = bind_aux r.on_false f
      }

  let bind m f = normalize M.empty (bind_aux m f)

  let get_split discr = Split {
      discr ;
      on_true = Leaf true ;
      on_false = Leaf false
    }


  let (let*) = bind

  let rec filter p (m : 'a t) : ('a case_tree) t  =
    match m with
    | Split { discr ; on_true ; on_false } ->
      let on_true = filter p on_true in
      let on_false = filter p on_false in
      if p discr
      then
        let* on_true = on_true in
        let* on_false = on_false in
        ret (Split {discr ; on_true ; on_false })
      else Split { discr ; on_true ; on_false }
    | Leaf x -> Leaf (Leaf x)

end


module NBe (M : NeSplitter) = struct

exception FailedNbe of string

let (let*) = M.bind

let ne_from_bool b =
  if b then NeTrue else NeFalse

let split_bool ty ne =
  match ty with
  | NfBool ->
    let* b = M.get_split ne in
    M.ret (NfNe { ty ; ne = ne_from_bool b })
  | ty -> M.ret (NfNe { ty ; ne })

let rec do_app fn arg : t M.t =
  match fn with
  | NfLam c -> do_clos c arg
  | NfNe { ty ; ne } ->
    begin match ty with
      | NfPi { dom ; cod} ->
        let ne = NeApp { fn = ne ; arg = Normal { ty = dom ; tm = arg } } in
        let* r = do_clos cod arg in
        split_bool r ne
      | _ -> raise (FailedNbe "In do_app, not a Pi")
    end
  | _ -> raise (FailedNbe "In do_app, not a function")

and do_clos (Clos { env ; body }) arg : t M.t = eval body (arg :: env)

and do_case b on_true on_false =
  match b with
  | NeTrue -> M.ret on_true
  | NeFalse -> M.ret on_false
  | ne ->
    let* b = M.get_split ne in
    M.ret (if b then on_true else on_false)

and eval tm env : t M.t =
  match tm with
  | Tm.Var i -> M.ret (List.nth env i)
  | Tm.U -> M.ret NfU
  | Tm.Pi { dom ; cod } ->
    let* dom = eval dom env in
    let cod = Clos { env ; body = cod } in
    M.ret (NfPi { dom ; cod })
  | Tm.Lam { ty = _ ; body } ->
    M.ret (NfLam (Clos { env ; body }))
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
      let* on_true = eval brT env in
      let* on_false = eval brF env in
      do_case ne on_true on_false
    | _ -> raise (FailedNbe "Boolean not evaluating to a neutral")
    end

let mk_var ty i = NfNe { ty ; ne = NeVar i }


let rec contains_ne_var i ne =
  match ne with
  | NeVar k -> i = k
  | NeApp { fn ; arg } -> contains_ne_var i fn || contains_nf_var i arg
  | NeTrue | NeFalse -> false
and contains_nf_var i (Normal r) = contains_t_var i r.tm
and contains_t_var i (nf : t) =
  match nf with
  | NfPi { dom ; cod } -> contains_t_var i dom || contains_clos_var i cod
  | NfLam c -> contains_clos_var i c
  | NfNe { ty = _ ; ne } -> (* contains_nf_var i ty ||*) contains_ne_var i ne
  | NfBool | NfU -> false

and contains_clos_var i (Clos { env ; body }) =
  List.exists (contains_t_var i) env ||
  Tm.contains_var (i+1) body


let rec read_back size (Normal { ty ; tm } : nf) : Tm.tm M.t =
  match ty, tm with
  | NfPi { dom ; cod }, _ ->
    let* ty = read_back size (Normal { ty = NfU ; tm = dom}) in
    let arg = mk_var dom size in
    let body =
      let* ty = do_clos cod arg in
      let* tm = do_app tm arg in
      read_back (size+1) (Normal { ty ; tm})
    in
    let* case_tree = M.filter (contains_ne_var 0) body in
    M.ret (Tm.Lam { ty ; body = from_case_tree case_tree })
  | _ -> failwith "todo"

and from_case_tree size m =
  match m with
  | Leaf t -> t
  | Split { discr ; on_true ; on_false } ->
    Tm.Ifte {
      discr = read_back_ne size discr ;
      on_true = from_case_tree m ;
      on_false = from_case_tree m
    }


end

