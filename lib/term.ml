type tm =
 | Var of int (* deBruijn indices *)
 | Pi of { dom : tm ; cod : tm }
 | Lam of { ty : tm ; body : tm }
 | App of { fn : tm ; arg : tm }
 | Bool
 | True
 | False
 | Ifte of { discr : tm ; brT : tm ; brF : tm }
 | U [@@ deriving ord]

 let rec pp_tm ?(names=[]) fmt = function 
  | Var i -> 
    begin match List.nth_opt names i with
    | None | Some None -> Format.fprintf fmt "v%n" i
    | Some (Some s) -> Format.fprintf fmt "%s" s
    end
  | Pi {dom ; cod} -> 
      Format.fprintf fmt "Π(%a). %a"
        (pp_tm ~names) dom
        (pp_tm ~names:(None :: names)) cod
  | Lam { ty ; body } -> 
      Format.fprintf fmt "λ( :%a). %a"
        (pp_tm ~names) ty
        (pp_tm ~names:(None :: names)) body
  | App {fn ; arg} -> 
    Format.fprintf fmt "(%a) %a"
        (pp_tm ~names) fn
        (pp_tm ~names) arg
 | Bool -> Format.fprintf fmt "bool"
 | True -> Format.fprintf fmt "true"
 | False -> Format.fprintf fmt "false"
 | Ifte { discr ; brT ; brF } -> 
    Format.fprintf fmt "if %a then %a else %a"
        (pp_tm ~names) discr
        (pp_tm ~names) brT
        (pp_tm ~names) brF
 | U -> Format.fprintf fmt "U"


let rec contains_var i t =
  match t with
  | Var k -> i = k
  | Pi { dom ; cod } -> contains_var i dom || contains_var (i+1) cod
  | Lam { ty ; body } -> contains_var i ty || contains_var (i+1) body
  | App { fn ; arg } -> contains_var i fn || contains_var i arg
  | Ifte { discr ; brT ; brF } ->
    contains_var i discr || contains_var i brT || contains_var i brF
  | Bool | True | False | U -> false

module S = Set.Make(Int)

let rec supp k t : S.t =
  match t with
  | Var i -> if i >= k then S.singleton i else S.empty
  | Pi { dom ; cod } -> S.union (supp k dom) (supp (k+1) cod)
  | Lam { ty ; body } -> S.union (supp k ty) (supp (k+1) body)
  | App { fn ; arg } -> S.union (supp k fn) (supp k arg)
  | Ifte { discr ; brT ; brF } -> 
    S.union (supp k discr) (S.union (supp k brT) (supp k brF))
  | _ -> S.empty

let rec strenghen k l t = 
  match t with
  | Var i -> 
    if i >= k then Var (i - l) else Var i
  | Pi { dom ; cod } -> 
    Pi { dom = strenghen k l dom ; cod = strenghen (k+1) l cod }
  | Lam { ty ; body } ->
    Lam { ty = strenghen k l ty ; body = strenghen (k+1) l body }
  | App { fn ; arg } ->
    App { fn = strenghen k l fn ; arg = strenghen k l arg }
  | Ifte { discr ; brT ; brF } -> 
    Ifte { discr = strenghen k l discr ; brT = strenghen k l brT ; brF = strenghen k l brF }
  | _ -> t

let to_canonical_index t =
  let s = supp 0 t in
  match S.min_elt_opt s with
  | None -> 
    (-1, t) (* That case should never happen for a neutral term t *)
  | Some l -> 
    let t' = strenghen 0 l t in
    (* Format.printf "Before str: %a@\nAfter str: %a@\n@\n"
      (pp_tm ~names:[]) t (pp_tm ~names:[]) t' ; *)
    (l, t')

module NeNf : sig
  type ne = private tm
  type pnf = private tm
  type nf = private tm

  val compare_ne : ne -> ne -> int
  val contains_var : int -> ne -> bool
  val to_canonical_index : ne -> int * ne

  val var : int -> ne
  val app : ne -> pnf -> ne
  val ne_pnf : pnf -> ne -> pnf
  val pi : pnf -> nf -> pnf
  val lam : pnf -> nf -> pnf
  val bool : pnf
  val btrue : pnf
  val bfalse : pnf
  val pnf_nf : pnf -> nf
  val case : ne -> nf -> nf -> nf
  val univ : pnf
end =
struct

  (* Neutral terms *)
  type ne = tm

  (* Pure normal forms *)
  type pnf = tm

  (* Normal forms *)
  type nf = tm

  let compare_ne = compare_tm
  let contains_var = contains_var
  let to_canonical_index = to_canonical_index

  let basetype (ty : pnf) : bool =
    match ty with
    | U -> true
    (* Neutral types *)
    | App _ | Var _ -> true
    | _ -> false

  (* Check that all the leading case split of a normal form depend on the 0th variable to be bound *)
  let rec valid_nf (t : nf) : bool =
    match t with
    | Ifte { discr ; brT ; brF } ->
      contains_var 0 discr && valid_nf brT && valid_nf brF
    | _ -> true

  (* Check that the (neutral, boolean) discriminee d is smaller
     than all the discriminees in the branches of t.
     Since t is assumed to satisfy the same assumption for all the
     discriminees in its leading splits, it is enough to check for
     the toplevel split (if it exists) *)
  let smaller (d : ne) (t : nf) : bool =
    match t with
    | Ifte {discr ; _ } -> compare_tm d discr < 0
    | _ -> true


  let var k = Var k
  let app fn arg = App { fn ; arg }
  (* ty has to be the normal form of the type of t
     it is not recorded in the term and only required for checking
     that neutral are included in pure normal forms at base types *)
  let ne_pnf ty t =
    assert (basetype ty) ;
    t
  let pi dom cod =
    assert (valid_nf cod) ;
    Pi { dom ; cod }

  let lam ty body =
    (* assert (valid_nf body) ; *)
    Lam { ty ; body }
  let bool = Bool
  let btrue = True
  let bfalse = False
  let pnf_nf t = t

  let case discr brT brF =
    assert (compare_tm brT brF <> 0) ;
    assert (smaller discr brT) ;
    assert (smaller discr brF) ;
    Ifte { discr ; brT ; brF }

  let univ = U
end

module NeOrd : Map.OrderedType with type t = NeNf.ne = 
struct 
  type t = NeNf.ne 
  let compare = NeNf.compare_ne 
end

