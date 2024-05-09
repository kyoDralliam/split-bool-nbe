type itm =
 | Var of int (* deBruijn indices *)
 | Pi of { dom : itm ; cod : itm }
 | Lam of { ty : itm ; body : itm }
 | App of { fn : itm ; arg : itm }
 | Bool
 | True
 | False
 | Ifte of { discr : itm ; brT : itm ; brF : itm }
 | U [@@ deriving ord, show]

module Tm = Term

let rec itm_tm = function 
 | Var i -> Tm.Var i
 | Pi x -> Tm.Pi { dom = itm_tm x.dom ; cod = itm_tm x.cod} 
 | Lam x -> Tm.Lam (itm_tm x.body)
 | App x -> Tm.App { fn = itm_tm x.fn ; arg = itm_tm x.arg }
 | Bool -> Tm.Bool
 | True -> Tm.True
 | False -> Tm.False
 | Ifte x -> Tm.Ifte { discr = itm_tm x.discr ; brT = itm_tm x.brT ; brF = itm_tm x.brF }
 | U -> Tm.U

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


let rec wk k t n = 
  match t with
  | Var i -> if i < k then Var i else Var (i+n)
  | Pi {dom; cod} -> Pi { dom = wk k dom n ; cod = wk (k+1) cod n }
  | Lam { ty ; body } -> Lam { ty = wk k ty n ; body = wk (k+1) body n }
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
  | Lam { ty ; body } -> Lam { ty = subst k ty u ; body = subst (k+1) body (wk1 u) }
  | App {fn ; arg} -> App {fn = subst k fn u ; arg = subst k arg u}
  | Ifte { discr ; brT ; brF } -> 
    Ifte { discr = subst k discr u ; brT = subst k brT u ; brF = subst k brF u }
  | cst -> cst

let subst0 t u = subst 0 t u

