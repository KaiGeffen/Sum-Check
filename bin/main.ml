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
Printf.printf "Arithmetic representation (g):\n%s\n\n" (show_aform g0);;

(* Perform the full sumcheck protocol
  g0: The starting (arithmetic) function
  g: The current function (constrained by the random numbers)
  round: The round number
  randoms: The current list of random numbers [r1,r2,...,ri]
*)
let rec do_sumcheck ~g0 ~g ~round ~randoms =
  Printf.printf "Round %i\n" round;

  let total_sum : int = Prover.eval_sharp_sat g in
  let partial_sum : aform = Prover.get_partial_sum g in

  (* Verifier checks that the total sum and partial sum are equal *)
  let result = Verifier.check_partial_sum ~total_sum ~partial_sum ~round in
  if (not result) then
    failwith (Printf.sprintf "Failed in round %i" round);

  (* Verifier picks a new random number and constrains based on it *)
  let r = Verifier.get_random () in
  let g' : aform = Prover.constrain_first ~formula:g ~value:r in
  Printf.printf "Verifier chose the number %d\n\n" r;

  (*
    TODO Some versions of the protocol cache as they constrain from the end of the list of variables
    This is in the worse case n times worse than that, which could be optimized out
  *)
  match get_first_free_variable g' with
  | None -> 
    (* No more rounds of the protocol, accept/reject based on oracle check *)
    Verifier.oracle_check ~g0 ~gv:g ~rs:(r::randoms)
  | Some _ -> do_sumcheck ~g0 ~g:g' ~round:(round + 1) ~randoms:(r::randoms);;

(* Verifier calculates g and makes a claim about it *)
Printf.printf "Verifier computes and claims that #SAT of g is %i\n\n" (Prover.eval_sharp_sat g0);;
let result = do_sumcheck ~g0:g0 ~g:g0 ~round:1 ~randoms:[];;
Printf.printf "The sumcheck protocol has completed, and the Prover trust Verifier: %b\n" result
