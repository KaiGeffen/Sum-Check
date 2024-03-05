open Utils

(* Propositional formulas *)
type pform = 
| Const of bool
| Variable of string
| Not of pform
| And of pform * pform
| Or of pform * pform

(* Arithmetic formulas *)
type aform =
| Const of int
| Variable of string
| Add of aform * aform
| Sub of aform * aform
| Mul of aform * aform

let rec show_pform (formula : pform) =
  match formula with
  | Const false -> "False"
  | Const true -> "True"
  (* TODO Reserve "True" and "False" keywords *)
  | Variable v -> v
  | Not f -> "¬" ^ show_pform f
  | And (f1, f2) -> "(" ^ show_pform f1 ^ " ^ " ^ show_pform f2 ^ ")"
  | Or (f1, f2) -> "(" ^ show_pform f1 ^ " ∨ " ^ show_pform f2 ^ ")"

let rec show_aform (formula : aform) =
  match formula with
  | Const c -> string_of_int c
  (* TODO Reserve numbers *)
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

let rec eval formula : int =
  match formula with
  (* NOTE Constants outside of field_size are allowed, since that is decided by Verifier *)
  | Const c -> c % field_size
  | Variable v -> raise (FreeVariableError v)
  | Add (f1, f2) -> ((eval f1) + (eval f2)) % field_size
  | Sub (f1, f2) -> ((eval f1) - (eval f2)) % field_size
  | Mul (f1, f2) -> ((eval f1) * (eval f2)) % field_size

let rec get_first_free_variable formula : string option =
  match formula with
  | Const _ -> None
  | Variable v -> Some v
  | Add (f1, f2)
  | Sub (f1, f2)
  | Mul (f1, f2) -> match get_first_free_variable f1 with
    | Some v -> Some v
    | None -> get_first_free_variable f2
  
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

(* TODO I could use a monad instead of throwing *)
let constrain_first (formula : aform) (value : int) : aform  =
  match get_first_free_variable formula with
  | None -> raise NoFreeVariableError
  | Some v -> constrain formula v value;;

let eval_monomial formula value : int =
  eval (constrain_first formula value)

let rec eval_sharp_sat (formula : aform) : int =
  match get_first_free_variable formula with
  | None -> eval formula
  | Some v ->
    (
      eval_sharp_sat (constrain formula v 0) +
      eval_sharp_sat (constrain formula v 1)
    ) % field_size
