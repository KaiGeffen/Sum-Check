(*
  Run with
  ocamlc -o main.byte main.ml; ./main.byte   
*)

(* Propositional formulas *)
type pform = 
| Const of bool
| Variable of string
| Not of pform
| And of pform * pform
| Or of pform * pform

let rec show_pform formula =
  match formula with
  | Const false -> "False"
  | Const true -> "True"
  (* TODO Reserve "True" and "False" keywords *)
  | Variable v -> v
  | Not f -> "¬" ^ show_pform f
  | And (f1, f2) -> "(" ^ show_pform f1 ^ " ^ " ^ show_pform f2 ^ ")"
  | Or (f1, f2) -> "(" ^ show_pform f1 ^ " ∨ " ^ show_pform f2 ^ ")"

(* Arithmetic formulas *)
type aform =
| Const of int
| Variable of string
| Add of aform * aform
| Sub of aform * aform
| Mul of aform * aform

let rec show_aform formula =
  match formula with
  | Const c -> string_of_int c
  (* Reserve numbers *)
  | Variable s -> s
  | Add (f1, f2) -> "(" ^ show_aform f1 ^ " + " ^ show_aform f2 ^ ")"
  | Sub (f1, f2) -> "(" ^ show_aform f1 ^ " - " ^ show_aform f2 ^ ")"
  | Mul (f1, f2) -> show_aform f1 ^ " * " ^ show_aform f2

let rec arithmetize (formula : pform) : aform =
  match formula with
  | Const c -> if c then Const 1 else Const 0
  | Variable s -> Variable s
  (* NOT A -> (1 - A) *)
  | Not f -> Sub (Const 1, arithmetize f)
  (* A AND B -> A * B *)
  | And (f1, f2) -> Mul (arithmetize f1, arithmetize f2)
  (* A OR B -> (A + B) - (A * B) *)
  | Or (f1, f2) -> Sub (
    Add (arithmetize f1, arithmetize f2),
    Mul (arithmetize f1, arithmetize f2)
    );;

(* Verifier decides this and tells Prover *)

(* Initialize rng *)
Random.self_init ();;
(* TODO Put all configuration in one place *)
let field_size : int = 19;;

(* A free variable exists with given name *)
exception FreeVariableError of string
(* No free variable exists when one is required *)
exception NoFreeVariableError

(* Constrain the given variable to value in the aformula *)
let rec constrain (formula : aform) (variable : string) (value : int) =
  match formula with
  | Const c -> Const c
  | Variable v ->
    if v = variable then
      Const value
    else
      Variable v
  | Add (f1, f2) -> Add (constrain f1 variable value, constrain f2 variable value)
  | Sub (f1, f2) -> Sub (constrain f1 variable value, constrain f2 variable value)
  | Mul (f1, f2) -> Mul (constrain f1 variable value, constrain f2 variable value)


(*
  If there is a free variable, there must be an argument given
*)
let rec eval formula : int =
  match formula with
  | Const c -> c
  | Variable v -> raise (FreeVariableError v)
  | Add (f1, f2) -> eval f1 + eval f2
  | Sub (f1, f2) -> eval f1 - eval f2
  | Mul (f1, f2) -> eval f1 * eval f2

let rec get_first_free_variable formula : string option =
  match formula with
  | Const c -> None
  | Variable v -> Some v
  | Add (f1, f2)
  | Sub (f1, f2)
  | Mul (f1, f2) -> match get_first_free_variable f1 with
    | Some v -> Some v
    | None -> get_first_free_variable f2

let rec eval_monomial formula value : int =
  (* TODO Make dry with evaluate (dict) when it comes *)
  match get_first_free_variable formula with
  | None -> raise NoFreeVariableError
  | Some var -> eval (constrain formula var value)

let rec get_sharp_sat (formula : aform) : int =
  match get_first_free_variable formula with
  | None -> eval formula
  | Some v ->
    get_sharp_sat (constrain formula v 0) +
    get_sharp_sat (constrain formula v 1);;

module Prover = struct
  (* Step 1 - Calculate the total sum of g evaluated at all Boolean inputs *)
  let evaluate_sharp_sat (formula: aform) : int =
    get_sharp_sat formula
  
  (* Step 2 - Compute partial sum of g, leaving first variable free *)
  let rec get_partial_sum (formula : aform) : aform =
    match get_first_free_variable formula with
    | None -> raise NoFreeVariableError
    | Some v ->
      let f_at_0 = get_sharp_sat (constrain formula v 0) in
      let f_at_1 = get_sharp_sat (constrain formula v 1) in
      let coefficient = Const (f_at_1 - f_at_0) in
      let constant = Const f_at_0 in
      Add (Mul (coefficient, Variable v), constant);;
    
  (* Step 5 - Constrain first free variable with given value, TODO compute partial sum *)
  let constrain_first_free_var (formula: aform) (value: int) : aform =
    match get_first_free_variable formula with
    | None -> raise NoFreeVariableError
    | Some v -> constrain formula v value
end

module Verifier = struct
  (* Step 3 - Check that partial sum and total sum agree *)
  let check_partial_sum total_sum partial_formula =
    total_sum == eval_monomial partial_formula 0 + eval_monomial partial_formula 1
  
  (* Step 4 - Pick a random number *)
  let get_random =
    Random.int field_size

  (* Step 7 - Evaluate g at one input using oracle *)
  let evaluate (formula : aform) (inputs : int list) : int =
    failwith "todo"
end

(* (X1 ∧ ¬X2) ∨ (X3 ∨ (X4 ∧ ¬X5)) *)
(* Has 23 satisfying assignments *)
let example_pform =
  Or(
    And(Variable "X1", Not(Variable "X2")),
    Or(Variable "X3", And(
      Variable "X4", Not(Variable "X5"))
    )
  );;

(* Step 1 *)
Printf.printf "Propositional formula:\n%s\n\n" (show_pform example_pform);;
let example_aform : aform = arithmetize example_pform;;
Printf.printf "Arithmetic representation:\n%s\n\n"  (show_aform example_aform);;
let g0 : int = Prover.evaluate_sharp_sat example_aform;;
Printf.printf "#SAT amount = %n\n" g0;;

(* Step 2 *)
(* 
  Given a formula with at least one free variable
  form the partial equation that leaves the first variable free
  and sums over the superset of all other variables   
*)
let part_g1 : aform = Prover.get_partial_sum example_aform;;
Printf.printf "partial_sum = %s\n" (show_aform part_g1);;

(* Step 3 *)
let result = Verifier.check_partial_sum g0 part_g1;;
Printf.printf "g0 == g1(0) + g1(1) is %b\n" result;;

(* Step 4 *)
let r1 = Verifier.get_random;;
Printf.printf "Verifier chose the number %d\n" r1;;

(* Step 5 *)
(*
  TODO Some version of the protocol cache as it constrains from the end of the list of variables
  This is in the worse case n times worse than that, which could be optimized out
*)

let g1 : aform = Prover.constrain_first_free_var example_aform r1;;
Printf.printf "With the first variable constrained, the formula is now: %s\n" (show_aform g1);;



