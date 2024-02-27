(* Run with
  ocamlc -o main.byte main.ml; ./main.byte   
*)

(* Propositional formulas *)
type form = 
| Const of bool
| Variable of string
| Not of form
| And of form * form
| Or of form * form

let rec show_form formula =
  match formula with
  | Const false -> "False"
  | Const true -> "True"
  (* TODO Reserve "True" and "False" keywords *)
  | Variable v -> v
  | Not f -> "¬" ^ show_form f
  | And (f1, f2) -> "(" ^ show_form f1 ^ " ^ " ^ show_form f2 ^ ")"
  | Or (f1, f2) -> "(" ^ show_form f1 ^ " ∨ " ^ show_form f2 ^ ")"

(* A free variable exists with given name *)
exception FreeVariableError of string

(* Constrain the given variable to value in the formula *)
let rec constrain formula variable value =
  match formula with
  | Const c -> Const c
  | Variable v ->
    if v = variable then
      Const value
    else
      Variable v
  | Not f -> Not (constrain f variable value)
  | And (f1, f2) -> And (constrain f1 variable value, constrain f2 variable value)
  | Or (f1, f2) -> Or (constrain f1 variable value, constrain f2 variable value)

let rec evaluate formula : bool =
  match formula with
  | Const c -> c
  | Variable v -> raise (FreeVariableError v)
  | Not f -> not (evaluate f)
  | And (f1, f2) -> evaluate f1 && evaluate f2
  | Or (f1, f2) -> evaluate f1 || evaluate f2

let rec get_first_free_variable formula : string option =
  match formula with
  | Const c -> None
  | Variable v -> Some v
  | Not f -> get_first_free_variable f
  | And (f1, f2)
  | Or (f1, f2) -> match get_first_free_variable f1 with
    | Some v -> Some v  
    | None -> get_first_free_variable f2

let rec get_sharp_sat (formula : form) : int =
  match get_first_free_variable formula with
  | None -> if evaluate formula then 1 else 0
  | Some v ->
    get_sharp_sat (constrain formula v false) +
    get_sharp_sat (constrain formula v true);;

(* (X1 ∧ ¬X2) ∨ (X3 ∨ (X4 ∧ ¬X5)) *)
let example_form =
  Or(
    And(Variable "1", Not(Variable "2")),
    Or(Variable "3", And(
      Variable "4", Not(Variable "5"))
    )
  ) in

Printf.printf "sharp_sat(%s) = %n\n" (show_form example_form) (get_sharp_sat example_form)
