(* Run with
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
    )

(* Verifier decides this and tells Prover *)
(* TODO Put all configuration in a single place *)
let field_size = 19;;

(* Partial Sum: A monomial linear equation *)
class partial_sum coefficient constant =
  object
    val coefficient = coefficient mod field_size
    val constant = constant mod field_size
    method show : string =
      Printf.sprintf "%d * X + %d" coefficient constant
    method eval x : int =
      x * coefficient + constant
  end

(* A free variable exists with given name *)
exception FreeVariableError of string
(* No free variable exists when one is required *)
exception NoFreeVariableError

(* Constrain the given variable to value in the aformula *)
let rec constrain formula variable value =
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


let rec evaluate formula : int =
  match formula with
  | Const c -> c
  | Variable v -> raise (FreeVariableError v)
  | Add (f1, f2) -> evaluate f1 + evaluate f2
  | Sub (f1, f2) -> evaluate f1 - evaluate f2
  | Mul (f1, f2) -> evaluate f1 * evaluate f2

let rec get_first_free_variable formula : string option =
  match formula with
  | Const c -> None
  | Variable v -> Some v
  | Add (f1, f2)
  | Sub (f1, f2)
  | Mul (f1, f2) -> match get_first_free_variable f1  with
    | Some v -> Some v
    | None -> get_first_free_variable f2

let rec get_sharp_sat (formula : aform) : int =
  match get_first_free_variable formula with
  | None -> evaluate formula
  | Some v ->
    get_sharp_sat (constrain formula v 0) +
    get_sharp_sat (constrain formula v 1);;

(* (X1 ∧ ¬X2) ∨ (X3 ∨ (X4 ∧ ¬X5)) *)
(* Has 23 satisfying assignments *)
let example_pform =
  Or(
    And(Variable "X1", Not(Variable "X2")),
    Or(Variable "X3", And(
      Variable "X4", Not(Variable "X5"))
    )
  );;
let example_aform = arithmetize example_pform;;

Printf.printf "Propositional formula:\n%s\nArithmetic representation:\n%s\n" (show_pform example_pform) (show_aform example_aform);;

Printf.printf "#SAT amount = %n\n" (get_sharp_sat example_aform);;
(*
(* Step 2 *)
(* 
  Given a formula with at least one free variable
  form the partial equation that leaves the first variable free
  and sums over the superset of all other variables   
*)
let rec get_partial_sum formula : partial_sum =
  match get_first_free_variable formula with
  | None -> raise NoFreeVariableError
  | Some v ->
    let f_at_0 = get_sharp_sat (constrain formula v false) in
    let f_at_1 = get_sharp_sat (constrain formula v true) in
    new partial_sum (f_at_1 - f_at_0) f_at_0;;

Printf.printf "partial_sum(%s) = %s\n" (show_form example_form) (get_partial_sum example_form)#show;;

(* Step 3 *)
let g0 = get_sharp_sat example_form;;
let g1_partial = get_partial_sum example_form;;
Printf.printf "g0 == g1(0) + g1(1) is %b\n" (g0 == g1_partial#eval 0 + g1_partial#eval 1);;

(* Step 4 *)
Random.self_init ()
let get_random = Random.int field_size;;
let r1 = get_random;;
Printf.printf "Verifier chose the number %d\n" r1;;

(* Step 5 *)
(*
  TODO Some version of the protocol cache as it constrains from the end of the list of variables
  This is in the worse case n times worse than that, which could be optimized out
*)
let g1 = constrain g0
Printf.printf "With the first variable constrained, the formula is not: %s\n" ;; *)
