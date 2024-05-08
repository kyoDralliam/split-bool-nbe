
type nf = Normal of { ty : t ; tm : t }
[@@deriving show]

and t =
  | NfPi of { dom : t ; cod : clos }
  | NfLam of clos
  | NfBool
  | NfU
  | NfNe of { ty : t ; ne : ne }
  | NfTrue
  | NfFalse
[@@deriving show]

and ne =
  | NeVar of int
  | NeApp of { fn : ne ; arg : nf }
[@@deriving show]

and env = t list
[@@deriving show]

and clos = Clos of { env : env ; body : Term.tm }
[@@deriving show]


