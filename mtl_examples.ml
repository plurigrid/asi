(* OCaml MTL: Algebraic types with exhaustive pattern matching *)
(* GF(3) trit: -1 (MINUS validator) *)

type interval = { lower: int; upper: int }

type timed_event = {
  timestamp: int;
  predicate: string;
  value: bool;
}

type mtl_formula =
  | Predicate of string
  | Eventually of interval * mtl_formula
  | Always of interval * mtl_formula
  | Until of interval * mtl_formula * mtl_formula
  | And of mtl_formula * mtl_formula
  | Or of mtl_formula * mtl_formula
  | Not of mtl_formula

(* CRDT convergence: ◇[0,τ_mix](replicas_converged) *)
let convergence tau_mix =
  Eventually (
    { lower = 0; upper = tau_mix },
    Predicate "replicas_converged"
  )

(* Merge commutativity: □[0,∞](merge_commutative) *)
let commutativity () =
  Always (
    { lower = 0; upper = max_int },
    Predicate "merge_commutative"
  )

(* Exhaustive pattern matching ensures correctness *)
let rec evaluate formula trace current_time =
  match formula with
  | Predicate p ->
      List.exists (fun e -> e.predicate = p && e.value) trace
  
  | Eventually (interval, f) ->
      List.exists
        (fun event ->
          event.timestamp >= current_time + interval.lower &&
          event.timestamp <= current_time + interval.upper &&
          evaluate f trace event.timestamp)
        trace
  
  | Always (interval, f) ->
      List.for_all
        (fun event ->
          event.timestamp < current_time + interval.lower ||
          event.timestamp > current_time + interval.upper ||
          evaluate f trace event.timestamp)
        trace
  
  | And (f1, f2) ->
      evaluate f1 trace current_time && evaluate f2 trace current_time
  
  | Or (f1, f2) ->
      evaluate f1 trace current_time || evaluate f2 trace current_time
  
  | Not f ->
      not (evaluate f trace current_time)
  
  | Until _ -> failwith "Until not implemented"
