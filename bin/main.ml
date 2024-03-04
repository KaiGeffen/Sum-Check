open Sum_Check
open Formula
open Prover
open Verifier

(* Step 0 - Get and print the formula *)
(* (X1 ∧ ¬X2) ∨ (X3 ∨ (X4 ∧ ¬X5)) *)
(* Has 23 satisfying assignments *)
let example_pform =
  Formula.Or(
    And(Variable "X1", Not(Variable "X2")),
    Or(Variable "X3", And(
      Variable "X4", Not(Variable "X5"))
    )
  );;
Printf.printf "Propositional formula:\n%s\n\n" (show_pform example_pform);;
let g0 : aform = arithmetize example_pform;;
Printf.printf "Arithmetic representation:\n%s\n\n" (show_aform g0);;

(* Perform the full sumcheck protocol
  g0: The starting (arithmetic) function
  g: The current function (constrained by the random numbers)
  round: The round number
  randoms: The current list of random numbers [r1,r2,...,ri]
*)
let rec do_sumcheck ~g0 ~g ~round ~randoms =
  (* Step 1 *)
  Printf.printf "#SAT of g%i = %i\n" (round - 1) (Prover.eval_sharp_sat g);

  (* Step 2 - TODO Explain including this here where in papers it isn't in the round *)
  let g_partial : aform =  Prover.get_partial_sum g in
  let () = Printf.printf "g%i = %s\n" (round - 1) (show_aform g_partial) in

  (* Step 3 *)
  (* TODO Print out the details *)
  let result = Verifier.check_partial_sum g g_partial in
  Printf.printf "g%i == g%i(0) + g%i(1) is %b\n" (round - 1) round round result;

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
    Verifier.oracle_check g0 g (r::randoms)
  | Some _ -> do_sumcheck ~g0 ~g:g' ~round ~randoms:(r::randoms)

(* Perform repeatedly do the steps of checking / constraining with V's rng *)
let result = do_sumcheck ~g0:g0 ~g:g0 ~round:1 ~randoms:[];;
Printf.printf "Verifier completed step 7 and believes the Prover: %b\n" result
 