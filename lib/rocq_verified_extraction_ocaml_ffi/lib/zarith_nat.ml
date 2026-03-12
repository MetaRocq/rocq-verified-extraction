(** Bindings to zarith GMP integers *)
type t = Z.t

let case discr zerob succb =
  if Z.equal Z.zero discr then zerob () else succb (Z.pred discr)

let pow x exp =
  let exp = try Z.to_int exp with Z.Overflow -> raise (Invalid_argument "zarith's Z.pow is called with too large an exponent") in
  Z.pow x exp
