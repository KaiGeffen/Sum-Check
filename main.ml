(*
  Run with
  ocamlc -o main.byte main.ml; ./main.byte   
*)
let (%) dividend divisor =
  let result = dividend mod divisor in
  if result < 0 then result + divisor else result

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

(* Initialize rng *)
Random.self_init ();;
(* TODO Put all configuration in one place *)
let field_size : int = 19;;

(* A free variable exists with given name *)
exception FreeVariableError of string
(* No free variable exists when one is required *)
exception NoFreeVariableError

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
  | Const c -> None
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
  | Some v -> constrain formula v value

let rec eval_monomial formula value : int =
  eval (constrain_first formula value)

let rec get_sharp_sat (formula : aform) : int =
  match get_first_free_variable formula with
  | None -> eval formula
  | Some v ->
    (
      get_sharp_sat (constrain formula v 0) +
      get_sharp_sat (constrain formula v 1)
    ) % field_size

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
      let coefficient = Const ((f_at_1 - f_at_0) % field_size) in
      let constant = Const (f_at_0) in
      Add (Mul (coefficient, Variable v), constant);;
    
  (* Step 5 - Constrain first free variable with given value, TODO compute partial sum *)
  let constrain_first_free_var (formula: aform) (value: int) : aform =
    match get_first_free_variable formula with
    | None -> raise NoFreeVariableError
    | Some v -> constrain formula v value
end

module Verifier = struct
  (* Step 3 - Check that partial sum and total sum agree *)
  let check_partial_sum (g : aform) (g' : aform) =
    (* Here, g is gn and g' is gn+1 *)
    Printf.printf "g(0) = %i\n" (eval_monomial g' 0);
    Printf.printf "g(1) = %i\n" (eval_monomial g' 1);
    get_sharp_sat g == (eval_monomial g' 0 + eval_monomial g' 1) % field_size
  
  (* Step 4 - Pick a random number *)
  let get_random () =
    Random.int field_size
  
  (* Step 7 - Evaluate g at one input using an oracle *)
  (* Constrain each var in g, with the last el of rs being the first constraint *)
  let rec constrain_fully (g : aform) (rs : int list) =
    match rs with
    | [] -> failwith "Oracle wasn't provided any random values."
    | [r] ->
      Printf.printf "Oracle constraining with value %i\n" r;
      constrain_first g r
    | r :: tl ->
      Printf.printf "Oracle constraining with value %i\n" r;
      constrain_first (constrain_fully g tl) r
  
  let oracle_check (g0 : aform) (gv: aform) (rs : int list) : bool =
    match rs with
    | [] -> failwith "Oracle wasn't provided any random values."
    | [rv]
    | rv :: _ -> 
      let oracle_evaluation = eval (constrain_fully g0 rs) in
      Printf.printf "Oracle sez: %i\n" oracle_evaluation;
      (eval_monomial gv rv) == oracle_evaluation
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
let g0 : aform = arithmetize example_pform;;
Printf.printf "Arithmetic representation:\n%s\n\n" (show_aform g0);;

(* Step 2 *)
(* 
  Given a formula with at least one free variable
  form the partial equation that leaves the first variable free
  and sums over the superset of all other variables   
*)
(* let g1_part : aform = Prover.get_partial_sum g0;;
Printf.printf "partial_sum = %s\n" (show_aform g1_part);; *)

(* A round is steps 2-5 *)
(* TODO do_round is confusing since it does rounds until evaluation is complete *)
let rec do_round (g0: aform) (g : aform) (i : int) (rs : int list) =
  (* Step 1 *)
  Printf.printf "#SAT of g%i = %i\n" i (Prover.evaluate_sharp_sat g);

  (* Step 2 - TODO Explain including this here where in papers it isn't in the round *)
  let g_partial : aform =  Prover.get_partial_sum g in
  let () = Printf.printf "partial_sum = %s\n" (show_aform g_partial) in

  (* Step 3 *)
  (* TODO Print out the details *)
  let result = Verifier.check_partial_sum g g_partial in
  Printf.printf "g%i == g%i(0) + g%i(1) is %b\n" i (i + 1) (i + 1) result;
  if not result then raise NoFreeVariableError;

  (* Step 4 *)
  let r = Verifier.get_random () in
  Printf.printf "Verifier chose the number %d\n\n" r;

  (* Step 5 *)
  (*
    TODO Some version of the protocol cache as it constrains from the end of the list of variables
    This is in the worse case n times worse than that, which could be optimized out
  *)
  let g' : aform = (constrain_first g r) in
  match get_first_free_variable g' with
  | None -> 
    (* Step 7 *)
    Verifier.oracle_check g0 g (r::rs)
  | Some _ -> do_round g0 g' (i + 1) (r::rs);;

(* Perform repeatedly do the steps of checking / constraining with V's rng *)
let result = do_round g0 g0 0 [] in
Printf.printf "Verifier completed step 7 and believes the Prover: %b\n" result
 