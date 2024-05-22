
module type Monad = sig
  type 'a t
  val ret : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
end

module Notations(M : Monad) = struct
  let (let+) x f = M.map f x 
  let (let*) m f = M.bind m f
end

module type ExcTParam =
sig
 type err 
 type 'a t 
 val ret : 'a -> 'a t
 val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module ExcT(M : ExcTParam) = 
struct
  type 'a t = (('a, M.err) Either.t) M.t
  let ret x = M.ret (Either.Left x)
  let bind m f = M.bind m (function | Either.Left x -> f x | Right e -> M.ret (Either.Right e))

  let map f m = bind m (fun x -> ret (f x))

  let fail e = M.ret (Either.Right e)
end
