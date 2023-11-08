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
      Format.fprintf fmt "Π %a. %a"
        (pp_tm ~names) dom
        (pp_tm ~names:(None :: names)) cod
  | Lam { ty ; body } -> 
      Format.fprintf fmt "λ :%a. %a"
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

module NeNf : sig
  type ne = private tm
  type pnf = private tm
  type nf = private tm

  val compare_ne : ne -> ne -> int
  val contains_var : int -> ne -> bool

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
    assert (valid_nf body) ;
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

