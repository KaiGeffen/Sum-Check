open Utils
open Formula

module Verifier = struct
  (* Check that partial sum and total sum agree *)
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
  
  (* Pick a random number in the field *)
  let get_random () =
    Random.int field_size
  
  (* Evaluate g at one input using an oracle
    g0: The starting (Fully unconstrained) function
    gv: Final univariate poly that P claims equals g0(r1,...,rv-1,Xv)
    rs: List of random numbers that V has chosen
  *)
  let oracle_check ~g0 ~gv ~(rs : int list) : bool =
    (* Constrain each var in g, with the last element of rs being the first constraint *)
    let rec constrain_fully (g : aform) (rs : int list) =
      match rs with
      (* TODO Using gadts to ensure the list is size 1+, I can remove this *)
      | [] -> failwith "Oracle wasn't provided any random values."
      | [r] -> constrain_first g r
      | r :: tl -> constrain_first (constrain_fully g tl) r
    in
    
    match rs with
    (* TODO Using gadts to ensure the list is size 1+, I can remove this *)
    | [] -> failwith "Oracle wasn't provided any random values."
    | [rv]
    | rv :: _ -> 
      let oracle_evaluation = eval (constrain_fully g0 rs) in
      Printf.printf "Oracle evaluation of g(r1,r2,...,rv) = %i\n" oracle_evaluation;
      let final_sum = eval_monomial gv rv in
      Printf.printf "gv(rv) = %i\n" final_sum;
      oracle_evaluation == final_sum
end