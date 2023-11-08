
open Term
open Nbe

let ( @* ) fn arg = App {fn ; arg}
let pi dom cod = Pi {dom ; cod}
let lam ty body = Lam { ty ; body}

let print_res names (ct : (NeNf.ne,NeNf.pnf) Splitter.case_tree) = 
  let pp_tm = pp_tm ~names:(List.map (fun x -> Some x) names) in
  Format.printf "%a" (Splitter.pp_case_tree pp_tm pp_tm) (ct :> (tm, tm) Splitter.case_tree)

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

  let res = M.run @@ norm ctx ty tm
  
end

module Ex5 = struct
  let ctx = [pi Bool Bool ]
  let ty = pi Bool Bool
  let tm = Var 0 

  let res = M.run @@ norm ctx ty tm
  
end
