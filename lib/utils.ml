
let (%) dividend divisor =
  let result = dividend mod divisor in
  if result < 0 then result + divisor else result;;

(* Initialize rng *)
Random.self_init ();;

(* TODO Put all configuration in one place *)
let field_size : int = 1337;;

(* A free variable exists with given name *)
exception FreeVariableError of string
(* No free variable exists when one is required *)
exception NoFreeVariableError
