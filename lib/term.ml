type tm =
 | Var of int (* deBruijn indices *)
 | Pi of { dom : tm ; cod : tm }
 | Lam of tm
 | App of { fn : tm ; arg : tm }
 | Bool
 | True
 | False
 | Ifte of { discr : tm ; brT : tm ; brF : tm }
 | U 
 [@@ deriving ord, show]

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
  | Lam body -> 
      Format.fprintf fmt "λ. %a"
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
  | Lam body -> contains_var (i+1) body
  | App { fn ; arg } -> contains_var i fn || contains_var i arg
  | Ifte { discr ; brT ; brF } ->
    contains_var i discr || contains_var i brT || contains_var i brF
  | Bool | True | False | U -> false


let rec minsupp k t : int =
  match t with
  | Var i -> if i >= k then (i - k) else max_int
  | Pi { dom ; cod } -> Int.min (minsupp k dom) (minsupp (k+1) cod)
  | Lam body -> minsupp (k+1) body
  | App { fn ; arg } -> Int.min (minsupp k fn) (minsupp k arg)
  | Ifte { discr ; brT ; brF } -> 
    Int.min (minsupp k discr) (Int.min (minsupp k brT) (minsupp k brF))
  | Bool | U | True | False -> max_int

let rec strenghen k l t = 
  match t with
  | Var i -> 
    if i >= k then Var (i - l) else Var i
  | Pi { dom ; cod } -> 
    Pi { dom = strenghen k l dom ; cod = strenghen (k+1) l cod }
  | Lam body ->
    Lam (strenghen (k+1) l body)
  | App { fn ; arg } ->
    App { fn = strenghen k l fn ; arg = strenghen k l arg }
  | Ifte { discr ; brT ; brF } -> 
    Ifte { discr = strenghen k l discr ; brT = strenghen k l brT ; brF = strenghen k l brF }
  | (Bool | U | True | False) as t -> t

let to_canonical_index t =
  let l = minsupp 0 t in
  let t' = strenghen 0 l t in
  (* Format.printf "Before str: %a@\nAfter str: %a@\n@\n"
      (pp_tm ~names:[]) t (pp_tm ~names:[]) t' ; *)
  (l, t')

module NeNf : sig
  type ne = private tm [@@deriving show]
  type pnf = private tm [@@deriving show]
  type nf = private tm [@@deriving show]

  val compare_ne : ne -> ne -> int
  val contains_var : int -> ne -> bool
  val to_canonical_index : ne -> int * ne

  val var : int -> ne
  val app : ne -> pnf -> ne
  val ne_pnf : pnf -> ne -> pnf
  val pi : pnf -> nf -> pnf
  val lam : nf -> pnf
  val bool : pnf
  val btrue : pnf
  val bfalse : pnf
  val pnf_nf : pnf -> nf
  val case : ne -> nf -> nf -> nf
  val univ : pnf
end =
struct

  (* Neutral terms *)
  type ne = tm [@@deriving show]

  (* Pure normal forms *)
  type pnf = tm [@@deriving show]

  (* Normal forms *)
  type nf = tm [@@deriving show]

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

  let lam body =
    assert (valid_nf body) ;
    Lam body
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


let rec wk k t n = 
  match t with
  | Var i -> if i < k then Var i else Var (i+n)
  | Pi {dom; cod} -> Pi { dom = wk k dom n ; cod = wk (k+1) cod n }
  | Lam body -> Lam (wk (k+1) body n)
  | App {fn ; arg} -> App {fn = wk k fn n ; arg = wk k arg n}
  | Ifte { discr ; brT ; brF } -> 
    Ifte { discr = wk k discr n ; brT = wk k brT n ; brF = wk k brF n }
  | cst -> cst

let wkn n t = wk 0 t n
let wk1 = wkn 1

let rec subst k t u = 
  match t with
  | Var i -> if i = k then u else Var i
  | Pi {dom; cod} -> Pi { dom = subst k dom u ; cod = subst (k+1) cod (wk1 u) }
  | Lam body -> Lam (subst (k+1) body (wk1 u))
  | App {fn ; arg} -> App {fn = subst k fn u ; arg = subst k arg u}
  | Ifte { discr ; brT ; brF } -> 
    Ifte { discr = subst k discr u ; brT = subst k brT u ; brF = subst k brF u }
  | cst -> cst

let subst0 t u = subst 0 t u
