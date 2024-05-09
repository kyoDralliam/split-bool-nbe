type itm =
 | Var of int (* deBruijn indices *)
 | App of { fn : itm ; arg : ctm }
 | Ifte of { discr : ctm ; brT : itm ; brF : itm }
 | Ascr of { tm : ctm ; ty : ctm }

and ctm =
 | Pi of { dom : ctm ; cod : ctm }
 | Bool
 | True
 | False
 | U 
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
  | True -> Tm.True
  | False -> Tm.False
  | U -> Tm.U
  | Lam t -> Tm.Lam (ctm_tm t)
  | Inj t -> itm_tm t