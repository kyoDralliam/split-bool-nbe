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

let (let+) x f = map Fun.id f x

let rec bind m f = 
  match m with
  | Leaf x -> f x
  | Split {lbl ; onl; onr} -> Split {lbl ; onl = bind onl f ; onr = bind onr f}

let (let*) = bind

let prod m1 m2 = let* x1 = m1 in let* x2 = m2 in ret (x1,x2)

let rec fold (flbl : 'a -> 'c -> 'c -> 'c) (fleaf : 'b -> 'c) : ('a,'b) case_tree -> 'c = function
  | Leaf b -> fleaf b
  | Split r -> flbl r.lbl (fold flbl fleaf r.onl) (fold flbl fleaf r.onr)


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
