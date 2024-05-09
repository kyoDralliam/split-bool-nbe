
type nf = Normal of { ty : t ; tm : t }

and t =
  | NfPi of { dom : t ; cod : clos }
  | NfLam of clos
  | NfBool
  | NfU
  | NfNe of { ty : t ; ne : ne }
  | NfTrue
  | NfFalse

and ne =
  | NeVar of int
  | NeApp of { fn : ne ; arg : nf }

and env = t list

and clos = Clos of { env : env ; body : Term.tm }
[@@deriving show]


