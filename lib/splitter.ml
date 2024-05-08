
module CT = struct

  type ('a, 'b) case_tree =
    | Split of { lbl : 'a ; onl : ('a,'b) case_tree ; onr : ('a,'b) case_tree }
    | Leaf of 'b

  let ret x = Leaf x
  let rec map flbl fleaf t = 
    match t with
    | Split r -> 
      Split { 
        lbl = flbl r.lbl ; 
        onl = map flbl fleaf r.onl  ;
        onr = map flbl fleaf r.onr }
    | Leaf x -> Leaf (fleaf x)

  let rec bind m f = 
    match m with
    | Leaf x -> f x
    | Split {lbl ; onl; onr} -> Split {lbl ; onl = bind onl f ; onr = bind onr f}

  let (let*) = bind

  let prod m1 m2 = let* x1 = m1 in let* x2 = m2 in ret (x1,x2)
end

open CT
open Either

let rec paths ct =
  match ct with 
  | Leaf x -> [[], x]
  | Split {lbl ; onl ; onr} ->
    let push a (l,x) = (a :: l, x) in
    (List.map (push (Left lbl)) @@ paths onl)
    @ (List.map (push (Right lbl)) @@ paths onr)

let pp_case_tree pp_lbl pp_leaf fmt ct =
  let pp_sep fmt () = Format.fprintf fmt "@\n| " in
  let pp_path fmt (l, x) = 
    let pp_sep fmt () = Format.fprintf fmt ", " in
    let pp_lift_lbl fmt = function
      | Left x -> Format.fprintf fmt "  %a " pp_lbl x
      | Right x -> Format.fprintf fmt "~[%a]" pp_lbl x
    in 
    Format.fprintf fmt "%a -> %a"
      (Format.pp_print_list ~pp_sep pp_lift_lbl) l
      pp_leaf x
  in 
  Format.fprintf fmt "| %a" (Format.pp_print_list ~pp_sep pp_path) (paths ct)



module type Splitter = sig
  type o
  type 'a t
  val ret : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  (* val get_split : o -> bool t *)
  val split : o -> 'a t -> 'a t -> 'a t
  val filter : (o -> bool) -> 'a t -> ((o,'a) case_tree) t

  val run : 'a t -> (o, 'a) case_tree
end

module Notations(M : Splitter) = struct
  let ( let* ) = M.bind
  let ( let+ ) m f = M.map f m
end

type comparison = Lt | Eq | Gt

let sign (n : int) = if n < 0 then Lt else if n = 0 then Eq else Gt

let option_prod o1 o2 = 
  Option.bind o1 (fun x1 -> Option.bind o2 (fun x2 -> Some (x1,x2)))

module TreeSplitter(O : Map.OrderedType) (*: Splitter with type o = O.t *) =
struct
  type o = O.t

  type 'a t = (O.t,'a option) case_tree

  let ret x = Leaf (Some x)
  let fail = Leaf None

  let split lbl onl onr =
    if onl = onr then onl else Split { lbl ; onl ; onr}

  let map f m = CT.map Fun.id (Option.map f) m

  let (let+) m f = map f m

  let rec sink (n : O.t) (b : bool) (m : 'a t) : ('a t) t =
    match m with
    | Leaf x -> ret (Leaf x)
    | Split s ->
      match sign @@ O.compare n s.lbl with
      | Eq -> ret (if b then s.onl else s.onr)
      | Lt -> ret m
      | Gt -> split s.lbl (sink n b s.onl) (sink n b s.onr)

  let rec merge (ml : 'a t) (mr : 'b t) : ('a * 'b) t =
    match ml, mr with
    | Leaf x, m -> CT.map Fun.id (option_prod x) m
    | m, Leaf y -> CT.map Fun.id (fun x -> option_prod x y) m
    | Split sl, Split sr ->
      match sign @@ O.compare sl.lbl sr.lbl with
      | Eq -> split sl.lbl (merge sl.onl sr.onl) (merge sl.onr sr.onr)
      | Lt -> split sl.lbl (merge sl.onl mr) (merge sl.onr mr)
      | Gt -> split sr.lbl (merge ml sr.onl) (merge ml sr.onr)

  let rec bind_aux m f =
    match m with
    | Leaf None -> Leaf None
    | Leaf (Some x) -> f x
    | Split r -> Split {
        r with
        onl = bind_aux r.onl f ;
        onr = bind_aux r.onr f
      }

  let (let*) = bind_aux

  let rec normalize : type a . a t -> a t =
    fun m ->
    match m with
    | Leaf x -> Leaf x
    | Split { lbl ; onl ; onr } ->
       let brT = sink lbl true (normalize onl) in
       let brF = sink lbl false (normalize onr) in
       let* (onl, onr) = (* normalize @@ *) merge brT brF in
       split lbl onl onr


  let bind m f = normalize (bind_aux m f)

  (* let get_split lbl = Split {
      lbl ;
      onl = Leaf true ;
      onr = Leaf false
    } *)


  let rec filter p (m : 'a t) : ((O.t,'a) case_tree) t  =
    match m with
    | Split { lbl ; onl ; onr } ->
      let onl = filter p onl in
      let onr = filter p onr in
      if p lbl
      then
        let+ (onl, onr) = merge onl onr in
        split lbl onl onr
      else split lbl onl onr
    | Leaf (Some x) -> ret (Leaf x)
    | Leaf None -> fail

  (* let rec exists p m =
    match m with
    | Split { lbl ; onl ; onr } ->
      p lbl || exists p onl || exists p onr
    | Leaf _ -> false *)

  let run m = CT.map Fun.id (function | None -> failwith "Run None!" | Some x -> x) m
end
