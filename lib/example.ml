
open Term
open Nbe

let ( @* ) fn arg = App {fn ; arg}
let pi dom cod = Pi {dom ; cod}
let lam ty body = Lam { ty ; body}
let ifte discr brT brF = Ifte { discr ; brT ; brF }

let print_res names (ct : (int*NeNf.ne,NeNf.pnf) Splitter.case_tree) = 
  let names = List.map (fun x -> Some x) names in
  let pp_pnf fmt (t : NeNf.pnf) = pp_tm ~names fmt (t :> tm) in
  let pp_lvl_ne fmt ((i,ne) : int * NeNf.ne) = Format.fprintf fmt "%d:%a" i (pp_tm ~names) (ne :> tm) in
  Format.printf "%a" (Splitter.pp_case_tree pp_lvl_ne pp_pnf) ct

module Ex1 = struct
  let ctx = [Bool]
  let ty = Bool
  let tm = Var 0

  let res = M.run @@ norm ctx ty tm
  
end

module Ex2 = struct
  let ctx = [Bool ; pi Bool Bool ]
  let ty = Bool
  let tm = App { fn = Var 1 ; arg = Var 0 }

  let res = M.run @@ norm ctx ty tm
  
end

module Ex3 = struct
  let ctx = [Bool ; pi Bool Bool ]
  let f = Var 1
  let x = Var 0
  let ty = Bool
  let tm = f @* (f @* (f @* x))

  let res = M.run @@ norm ctx ty tm
  
end

module Ex4 = struct
  let ctx = [pi Bool Bool ]
  let ty = pi Bool Bool
  let tm = 
    let f = Var 1 in
    let x = Var 0 in
    lam Bool (f @* (f @* (f @* x)))

  let res () = M.run @@ norm ctx ty tm
  
end

module Ex5 = struct
  let ctx = [pi Bool Bool ]
  let ty = pi Bool Bool
  let tm = Var 0 

  let res () = M.run @@ norm ctx ty tm
  
end


module Id = struct
  let ctx = []
  let ty = pi Bool Bool

  let tm = lam Bool (Var 0)

  let res () = M.run @@ norm ctx ty tm
end
