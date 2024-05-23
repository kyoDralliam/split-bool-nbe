
let curry f (x,y) = f x y

module CT = CaseTree
open CT

module type OrderedPPType =
sig
  include Map.OrderedType  
  val pp : Format.formatter -> t -> unit
end

module type Splitter = sig

  module O : OrderedPPType
  module Map : sig 
    include Map.S with type key = O.t 
    val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
  end

  include Monad.Monad

  (** Actions of the monad *)

  val split : O.t -> 'a t -> 'a t -> 'a t
  val case : O.t -> bool t
  val fail : string -> 'a t

  (** Observations on monadic computations *)

  (* [filter p m] returns the sub-case tree satisfying the predicate [p].
     [p] should be monotone monotone wrt the order on O.t, that is if [O.compare x y = 1]
     and [p x = true] then [p y = true] *)
  val filter : bool Map.t -> (O.t -> bool) -> 'a t -> ((O.t,'a) case_tree) t

  val run : bool Map.t -> (string -> (O.t, 'a) case_tree) -> 'a t -> (O.t, 'a) case_tree

  val forall : bool Map.t -> (bool Map.t * 'a -> bool) -> 'a t -> bool

  val equiv : bool Map.t -> 'a t -> 'a t -> bool

  (* The printer breaks the abstraction in the modules (we can observe non-extensional changes).
    Should that be fixed ?*)
  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

type comparison = Lt | Eq | Gt

let sign (n : int) = if n < 0 then Lt else if n = 0 then Eq else Gt

let option_prod o1 o2 = 
  Option.bind o1 (fun x1 -> Option.bind o2 (fun x2 -> Some (x1,x2)))

let either_prod (comp : 'e -> 'e -> 'e) (e1 : ('a,'e) Either.t) (e2 : ('b,'e) Either.t) : ('a*'b,'e) Either.t =
  match e1, e2 with
  | Left x1, Left x2 -> Left (x1,x2)
  | Right s1, Right s2 -> Right (comp s1 s2)
  | Right s1, Left _ -> Right s1
  | Left _, Right s2 -> Right s2


module TreeSplitter(O : OrderedPPType) : Splitter with module O = O =
struct

  module O = O
  
  (* FIXME: write this as a module once and for all *)
  module Map = struct 
    include Map.Make(O)
    let pp pp_val fmt m = 
      Format.fprintf fmt "{" ;
      iter (fun key vl -> Format.fprintf fmt "| %a ↦ %a " O.pp key pp_val vl) m ;
      Format.fprintf fmt "|}" ;
  end

  module CTE = 
  struct
    type err = string
    type 'a t = (O.t, 'a) case_tree
    let ret = CT.ret
    let bind = CT.bind
  end

  module E = Monad.ExcT(CTE)
  
  (* ** 
    This module maintains the following invariant: 
    any term of type 'a t is normalized, meaning that
    1) the labels at the nodes of the case tree 'a E.t are strictly increasing on each branches
    2) the left and right children of a node are distinct

    ret, fail, case and map trivially preserve the invariant.
    For split, we need to check that the branches are distincts.
    For bind, we re-normalize the result of CaseTree's bind using the function normalize.contents

    An alternative implementation that renormalize only when we observe the type, e.g. on filter, run and equiv is provided below
  *)
  include E


  let pp pp_lbl fmt ct = pp_case_tree O.pp (Format.pp_print_either ~left:pp_lbl ~right:Format.pp_print_string) fmt ct 

  let split lbl onl onr =
    if onl = onr then onl else Split { lbl ; onl ; onr}

  let case lbl = Split { lbl ; onl = ret true ; onr = ret false }

  let map f m = CT.map Fun.id (Either.map_left f) m

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
    | Leaf x, m -> CT.(let+ y = m in either_prod (^) x y)
    | m, Leaf y -> CT.(let+ x = m in either_prod (^) x y)
    | Split sl, Split sr ->
      match sign @@ O.compare sl.lbl sr.lbl with
      | Eq -> split sl.lbl (merge sl.onl sr.onl) (merge sl.onr sr.onr)
      | Lt -> split sl.lbl (merge sl.onl mr) (merge sl.onr mr)
      | Gt -> split sr.lbl (merge ml sr.onl) (merge ml sr.onr)

  (* Beware, not the "real" bind of this module ; do not expose ! *)
  let (let*) = E.bind

  let rec normalize : type a . a t -> a t =
    fun m ->
    match m with
    | Leaf x -> Leaf x
    | Split { lbl ; onl ; onr } ->
       let brT = sink lbl true (normalize onl) in
       let brF = sink lbl false (normalize onr) in
       let* (onl, onr) = (* normalize @@ *) merge brT brF in
       split lbl onl onr

  let bind m f = normalize (E.bind m f)

  let to_case_tree (m : 'a t) : ((O.t,'a) case_tree) t =
    CaseTree.fold 
      (fun lbl brT brF -> let* onl = brT in let* onr = brF in ret (Split {lbl ; onl ; onr}))
      (function Either.Left x -> ret (Leaf x) | Either.Right s -> fail s)
      m

  (* Assuming the predicate p is monotone wrt the order on O *)
  let rec filter' p (m : 'a t) : ((O.t,'a) case_tree) t  =
    match m with
    | Split { lbl ; onl ; onr } ->
      if p lbl then to_case_tree m else Split { lbl ; onl = filter' p onl ; onr = filter' p onr } 
    | Leaf _ -> to_case_tree m

  let filter _env p m = filter' p m

  (* let rec filter p (m : 'a t) : ((O.t,'a) case_tree) t  =
    match m with
    | Split { lbl ; onl ; onr } ->
      let onl = filter p onl in
      let onr = filter p onr in
      if p lbl
      then
        let+ (onl, onr) = merge onl onr in
        split lbl onl onr
      else split lbl onl onr
    | Leaf (Either.Left x) -> ret (Leaf x)
    | Leaf (Either.Right s) -> fail s *)

  let forall _env p m = 
    let open CT in
    let@ (path, x) = m in 
    match x with
    | Either.Right _ -> false
    | Either.Left x ->
      let m : bool Map.t = List.fold_right (curry Map.add) path Map.empty in
      p (m, x)

  let run env fail m = 
    CT.fold (fun ne onl onr -> 
      match Map.find_opt ne env with
      | Some true -> onl
      | Some false -> onr
      | None -> Split { lbl = ne ; onl ; onr })
      (function | Either.Right s -> fail s | Either.Left x -> CT.ret x) m

  let equiv _env m1 m2 = m1 = m2 (* the invariant should ensure that m1 and m2 are always equivalent *)
end

module TreeSplitterLazy(O : OrderedPPType) : Splitter with module O = O =
struct

  module O = O

  module CTE = 
  struct
    type err = string
    type 'a t = (O.t, 'a) case_tree
    let ret = CT.ret
    let bind = CT.bind
  end

  module E = Monad.ExcT(CTE)
  
  (* ** 
    This module maintains the following invariant:
    When a term of type 'a t is observed, it is normalized, meaning that
    1) the labels at the nodes of the case tree 'a E.t are strictly increasing on each branches
    2) the left and right children of a node are distinct

    We renormalize in filter and run before providing external observations.
  *)
  include E



  let split lbl onl onr = Split { lbl ; onl ; onr}

  let case lbl = Split { lbl ; onl = ret true ; onr = ret false }

  module Map = struct 
    include Map.Make(O)
    let pp pp_val fmt m = 
      Format.fprintf fmt "{" ;
      iter (fun key vl -> Format.fprintf fmt "| %a ↦ %a " O.pp key pp_val vl) m ;
      Format.fprintf fmt "|}" ;
  end

  module S = Set.Make(O)

  let rec eval env m = 
    match m with
    | Leaf x -> [x, env], S.empty
    | Split { lbl ; onl ; onr } ->
      match Map.find_opt lbl env with
      | Some true -> eval env onl
      | Some false -> eval env onr
      | None ->
        let l, sl = eval (Map.add lbl true env) onl in
        let r, sr = eval (Map.add lbl false env) onr in
        l @ r, S.add lbl (S.union sl sr)

  let rec split_list lbl l = 
    match l with
    | [] -> [], []
    | x :: ls -> 
      let ls1, ls2 = split_list lbl ls in
      match Map.find_opt lbl (snd x) with
      | None -> x :: ls1, x :: ls2
      | Some true -> (fst x, Map.remove lbl (snd x)) :: ls1, ls2
      | Some false -> ls1, (fst x, Map.remove lbl (snd x)) :: ls2

  let rec rebuild l supp = 
    match S.min_elt_opt supp with
    | None-> 
      begin match l with
      | [x,_env] -> Leaf x (* the leftover env ougth to come from external constraints *)
      | [] -> failwith "No element without support when rebuilding"
      | _ -> failwith "Multiple elements without support when rebuilding"
      end
    | Some lbl -> 
      let ltrue, lfalse = split_list lbl l in
      let supp' = S.remove lbl supp in
      Split { lbl ; onl = rebuild ltrue supp' ; onr = rebuild lfalse supp' }


  let normalize env m = 
    let l, supp = eval env m in
    rebuild l supp


  let to_case_tree fail (m : 'a t) : ((O.t,'a) case_tree) t =
    let (let*) = E.bind in
    CaseTree.fold 
      (fun lbl brT brF -> let* onl = brT in let* onr = brF in ret (Split {lbl ; onl ; onr}))
      (function Either.Left x -> ret (Leaf x) | Either.Right s -> fail s)
      m

  (* Assuming the predicate p is monotone wrt the order on O *)
  let rec filter' p (m : 'a t) : ((O.t,'a) case_tree) t  =
    match m with
    | Split { lbl ; onl ; onr } ->
      if p lbl then to_case_tree fail m else Split { lbl ; onl = filter' p onl ; onr = filter' p onr } 
    | Leaf _ -> to_case_tree fail m

  let filter env p m = filter' p (normalize env m)
  
  let forall' m p = 
    let open CT in
    let@ (path, x) = m in 
    match x with
    | Either.Right _ -> false
    | Either.Left x ->
      let m : bool Map.t = List.fold_right (curry Map.add) path Map.empty in
      p (m, x)

  let forall env p m = forall' (normalize env m) p


  let run env fail m = 
    CaseTree.fold 
      (fun lbl onl onr -> Split {lbl ; onl ; onr})
      (function Either.Left x -> Leaf x | Either.Right s -> fail s)
      (normalize env m)

  let equiv env m1 m2 = (normalize env m1) = (normalize env m2)
  
  let pp pp_lbl fmt ct = pp_case_tree O.pp (Format.pp_print_either ~left:pp_lbl ~right:Format.pp_print_string) fmt ct 
end
