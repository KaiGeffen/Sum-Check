open Utils
open Formula

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