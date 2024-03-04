open Utils
open Formula

module Prover = struct
  (* Step 1 - Calculate the total sum of g evaluated at all Boolean inputs *)
  let eval_sharp_sat (formula: aform) : int =
    eval_sharp_sat formula
  
  (* Step 2 - Compute partial sum of g, leaving first variable free *)
  let get_partial_sum (formula : aform) : aform =
    match get_first_free_variable formula with
    | None -> raise NoFreeVariableError
    | Some v ->
      let f_at_0 = eval_sharp_sat (constrain formula v 0) in
      let f_at_1 = eval_sharp_sat (constrain formula v 1) in
      let coefficient = Const ((f_at_1 - f_at_0) % field_size) in
      let constant = Const (f_at_0) in
      Add (Mul (coefficient, Variable v), constant);;
    
  (* Step 5 - Constrain first free variable with given value, TODO compute partial sum *)
  let constrain_first_free_var (formula: aform) (value: int) : aform =
    match get_first_free_variable formula with
    | None -> raise NoFreeVariableError
    | Some v -> constrain formula v value
end