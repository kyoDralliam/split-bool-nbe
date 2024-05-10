type itm =
 | Var of int (* deBruijn indices *)
 | App of { fn : itm ; arg : ctm }
 | Ifte of { discr : ctm ; brT : itm ; brF : itm }
 | Ascr of { tm : ctm ; ty : ctm }

and ctm =
 | Pi of { dom : ctm ; cod : ctm }
 | Bool
 | U 
 | IfTy of { discr : ctm ; tyT : ctm ; tyF : ctm }
 | True
 | False
 | Lam of ctm
 | Inj of itm 
 [@@ deriving show]


module Tm = Term
 
let rec itm_tm = function
  | Var i -> Tm.Var i
  | App { fn ; arg } -> Tm.App { fn = itm_tm fn ; arg = ctm_tm arg }
  | Ifte { discr ; brT ; brF } -> Tm.Ifte { discr = ctm_tm discr ; brT = itm_tm brT ; brF = itm_tm brF }
  | Ascr { tm ; _ } -> ctm_tm tm
and ctm_tm = function
  | Pi { dom ; cod } -> Tm.Pi { dom = ctm_tm dom ; cod = ctm_tm cod }
  | Bool -> Tm.Bool
  | U -> Tm.U
  | IfTy {discr; tyT ; tyF} -> Tm.Ifte { discr = ctm_tm discr ; brT = ctm_tm tyT ; brF = ctm_tm tyF }
  | True -> Tm.True
  | False -> Tm.False
  | Lam t -> Tm.Lam (ctm_tm t)
  | Inj t -> itm_tm t


let rec iwk k t n = 
  match t with
  | Var i -> if i < k then Var i else Var (i+n)
  | App {fn ; arg} -> App {fn = iwk k fn n ; arg = cwk k arg n}
  | Ifte { discr ; brT ; brF } -> 
    Ifte { discr = cwk k discr n ; brT = iwk k brT n ; brF = iwk k brF n }
  | Ascr { tm; ty} -> Ascr { tm = cwk k tm n ; ty = cwk k ty n }
and cwk k t n = 
  match t with
  | Pi {dom; cod} -> Pi { dom = cwk k dom n ; cod = cwk (k+1) cod n }
  | Lam body -> Lam (cwk (k+1) body n)
  | IfTy { discr ; tyT ; tyF } -> 
    IfTy { discr = cwk k discr n ; tyT = cwk k tyT n ; tyF = cwk k tyF n }
  | Inj t -> Inj (iwk k t n)
  | (Bool | U | True | False) as cst -> cst

let cwkn n t = cwk 0 t n
let iwkn n t = iwk 0 t n
let iwk1 = iwkn 1
let cwk1 = cwkn 1
