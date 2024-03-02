(* main.ml *)

open Sum_Check
open Utils
open Formula
open Prover
open Verifier

(* (X1 ∧ ¬X2) ∨ (X3 ∨ (X4 ∧ ¬X5)) *)
(* Has 23 satisfying assignments *)
let example_pform =
  Formula.Or(
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
 