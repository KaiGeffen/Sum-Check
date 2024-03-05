open Utils
open Formula

module Verifier = struct
  (* Step 3 - Check that partial sum and total sum agree *)
  let check_partial_sum ~total_sum ~partial_sum ~round =
    (* Here, g is gn and g' is gn+1 *)
    let g_at_0 = eval_monomial partial_sum 0 in
    let g_at_1 = eval_monomial partial_sum 1 in

    Printf.printf "Total sum: g%i = %i\n" (round - 1) total_sum;
    Printf.printf "Partial sum: g%i = %s\n" round (show_aform partial_sum);
    Printf.printf "g%i(0) = %i\n" round g_at_0;
    Printf.printf "g%i(1) = %i\n" round (eval_monomial partial_sum 1);
    Printf.printf "g%i = %i = (%i + %i) mod %i = g%i(0) + g%i(1)\n"
      (round - 1) total_sum g_at_0 g_at_1 field_size round round;
    total_sum == (g_at_0 + g_at_1) % field_size
  
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