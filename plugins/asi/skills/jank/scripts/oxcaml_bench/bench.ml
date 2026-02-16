(* bench.ml — OxCaml 5.2.0+ox benchmark: OhMyThreads.jl-like parallel primitives
 *
 * Three triads from neanderthal.jank:
 *   1. REGISTER  — tight numeric loops, zero-alloc, unboxed vec2/mat2
 *   2. KERNEL    — parallel dispatch via pre-spawned Domain pool
 *   3. STRUCTURE — append-only log, persistent trajectory
 *
 * OhMyThreads.jl API: tforeach, tmap, treduce, tmapreduce
 *
 * Build: dune build
 * Run:   dune exec ./bench.exe
 *)

(* === Timing === *)
let bench ~iters f =
  for _ = 1 to iters / 10 do ignore (f ()) done;
  let t0 = Sys.time () in
  let v = ref 0.0 in
  for _ = 1 to iters do v := f () done;
  let t1 = Sys.time () in
  (!v, (t1 -. t0) *. 1e9 /. Float.of_int iters)

let time_ns f =
  let t0 = Sys.time () in
  let v = f () in
  let t1 = Sys.time () in
  (v, (t1 -. t0) *. 1e9)

(* === SplitMix64 (matches splitmix64.jank / babashka exactly) === *)
let splitmix64_next state =
  let state' = Int64.add state 0x9E3779B97F4A7C15L in
  let z = Int64.mul (Int64.logxor state' (Int64.shift_right_logical state' 30))
                    0xBF58476D1CE4E5B9L in
  let z = Int64.mul (Int64.logxor z (Int64.shift_right_logical z 27))
                    0x94D049BB133111EBL in
  let z = Int64.logxor z (Int64.shift_right_logical z 31) in
  (state', z)

let hue_from_hash h =
  let masked = Int64.to_float (Int64.logand h 0xFFFFL) in
  Float.rem (masked *. 360.0 /. 65536.0) 360.0

type polarity = Positive | Neutral | Negative

let girard_polarity hue =
  if hue < 120.0 then Positive
  else if hue < 240.0 then Neutral
  else Negative

let polarity_name = function
  | Positive -> "positive" | Neutral -> "neutral" | Negative -> "negative"

let tap_control = function
  | Positive -> 1 | Neutral -> 0 | Negative -> -1

(* === BLAS primitives (2D fixed-size, REGISTER path) === *)
type vec2 = { x: float; y: float }
type mat2 = { a00: float; a01: float; a10: float; a11: float }

let vec2_dot v1 v2 = v1.x *. v2.x +. v1.y *. v2.y
let vec2_norm v = Float.sqrt (v.x *. v.x +. v.y *. v.y)
let vec2_add v1 v2 = { x = v1.x +. v2.x; y = v1.y +. v2.y }
let vec2_scale a v = { x = a *. v.x; y = a *. v.y }

let mat2_mul_vec m v =
  { x = m.a00 *. v.x +. m.a01 *. v.y;
    y = m.a10 *. v.x +. m.a11 *. v.y }

(* === MPC step (REGISTER path) === *)
type mpc2_state = { mx: vec2; cost: float; norm: float }

let mpc2_step a bu q x =
  let x_next = vec2_add (mat2_mul_vec a x) bu in
  let qx = mat2_mul_vec q x in
  let cost = vec2_dot x qx in
  { mx = x_next; cost; norm = vec2_norm x_next }

(* === Append-only log (STRUCTURE path) === *)
type log_entry = { step: int; le_cost: float; le_norm: float }

let mpc_horizon_logged a bu q x0 n =
  let log = Array.make n { step = 0; le_cost = 0.0; le_norm = 0.0 } in
  let x = ref x0 in
  for i = 0 to n - 1 do
    let s = mpc2_step a bu q !x in
    log.(i) <- { step = i; le_cost = s.cost; le_norm = s.norm };
    x := s.mx
  done;
  log

(* === Domain pool — spawn once, reuse forever ===
 * OhMyThreads.jl's DynamicScheduler pre-creates Julia tasks;
 * we pre-create OCaml domains and signal them via Atomic flags.
 * This amortizes the ~100μs domain spawn cost. *)

type work_item =
  | Idle
  | Work of (unit -> unit)
  | Shutdown

type worker = {
  work_slot: work_item Atomic.t;
  done_flag: bool Atomic.t;
}

let make_pool nworkers =
  let workers = Array.init nworkers (fun _ ->
    { work_slot = Atomic.make Idle;
      done_flag = Atomic.make true })
  in
  let _domains = Array.init nworkers (fun i ->
    Domain.spawn (fun () ->
      let w = workers.(i) in
      let running = ref true in
      while !running do
        match Atomic.get w.work_slot with
        | Idle ->
          Domain.cpu_relax ()
        | Work f ->
          Atomic.set w.done_flag false;
          f ();
          Atomic.set w.work_slot Idle;
          Atomic.set w.done_flag true
        | Shutdown ->
          running := false
      done))
  in
  (workers, _domains)

let pool_dispatch workers f_for_worker =
  let n = Array.length workers in
  (* assign work *)
  for i = 0 to n - 1 do
    let w = workers.(i) in
    Atomic.set w.done_flag false;
    Atomic.set w.work_slot (Work (fun () -> f_for_worker (i + 1)))
  done;
  (* main thread does chunk 0 *)
  f_for_worker 0;
  (* wait for all workers *)
  for i = 0 to n - 1 do
    while not (Atomic.get workers.(i).done_flag) do
      Domain.cpu_relax ()
    done
  done

let pool_shutdown (workers, domains) =
  Array.iter (fun w -> Atomic.set w.work_slot Shutdown) workers;
  Array.iter Domain.join domains

(* === OhMyThreads.jl API on domain pool === *)

let pool_tforeach workers f n =
  let ntasks = Array.length workers + 1 in
  let chunk_size = (n + ntasks - 1) / ntasks in
  pool_dispatch workers (fun tid ->
    let start = tid * chunk_size in
    let stop = min n (start + chunk_size) in
    for i = start to stop - 1 do f i done)

let pool_tmapreduce workers f op init n =
  let ntasks = Array.length workers + 1 in
  let chunk_size = (n + ntasks - 1) / ntasks in
  let partials = Array.make ntasks init in
  pool_dispatch workers (fun tid ->
    let start = tid * chunk_size in
    let stop = min n (start + chunk_size) in
    let acc = ref init in
    for i = start to stop - 1 do acc := op !acc (f i) done;
    partials.(tid) <- !acc);
  Array.fold_left op init partials

let pool_tmap workers f n =
  let out = Array.make n 0.0 in
  pool_tforeach workers (fun i -> out.(i) <- f i) n;
  out

(* === Main === *)
let () =
  let ndomain = Domain.recommended_domain_count () in
  Printf.printf "=== OxCaml 5.2.0+ox Benchmark ===\n";
  Printf.printf "Domains available: %d\n\n" ndomain;

  (* --- SplitMix64 correctness --- *)
  Printf.printf "=== SplitMix64 Correctness ===\n";
  let _, hash0 = splitmix64_next 0L in
  Printf.printf "  seed=0 step=0: %016Lx " hash0;
  if hash0 = 0xe220a8397b1dcdafL then
    Printf.printf "PASS\n"
  else
    Printf.printf "FAIL (expected e220a8397b1dcdaf)\n";

  Printf.printf "\n=== SplitMix64 Output (seed=42, 10 steps) ===\n";
  let state = ref 42L in
  for i = 0 to 9 do
    let state', hash = splitmix64_next !state in
    let hue = hue_from_hash hash in
    let pol = girard_polarity hue in
    Printf.printf "  %d %016Lx hue=%.1f %s TAP=%d\n"
      i hash hue (polarity_name pol) (tap_control pol);
    state := state'
  done;

  (* --- SplitMix64 throughput --- *)
  Printf.printf "\n=== SplitMix64 Throughput ===\n";
  let n_sm = 10_000_000 in
  let _, ns_sm = bench ~iters:1 (fun () ->
    let s = ref 0L in
    for _ = 1 to n_sm do
      let s', _ = splitmix64_next !s in
      s := s'
    done;
    Int64.to_float !s)
  in
  Printf.printf "  %d iterations: %.1f ms (%.1f ns/op, %.2f M ops/sec)\n"
    n_sm (ns_sm /. 1e6) (ns_sm /. Float.of_int n_sm)
    (Float.of_int n_sm *. 1e3 /. ns_sm);

  (* --- BLAS L1 --- *)
  Printf.printf "\n=== BLAS Level 1 ===\n";
  let x = { x = 1.0; y = 0.0 } in
  let y = { x = 0.0; y = 1.0 } in
  Printf.printf "  dot([1,0],[0,1]) = %.1f %s\n" (vec2_dot x y)
    (if vec2_dot x y = 0.0 then "PASS" else "FAIL");
  Printf.printf "  nrm2([1,0]) = %.1f %s\n" (vec2_norm x)
    (if vec2_norm x = 1.0 then "PASS" else "FAIL");
  let axpy = vec2_add (vec2_scale 2.5 x) y in
  Printf.printf "  axpy(2.5,[1,0],[0,1]) = [%.1f,%.1f] %s\n"
    axpy.x axpy.y (if axpy.x = 2.5 && axpy.y = 1.0 then "PASS" else "FAIL");

  (* --- MPC trajectory --- *)
  Printf.printf "\n=== MPC Trajectory (20-step) ===\n";
  Printf.printf "  step | cost      | ||x||\n";
  Printf.printf "  -----|-----------|-------\n";
  let a = { a00 = 0.9; a01 = -0.1; a10 = 0.1; a11 = 0.95 } in
  let bu = { x = 0.5 *. (-0.2); y = 0.3 *. (-0.2) } in
  let q = { a00 = 1.0; a01 = 0.0; a10 = 0.0; a11 = 1.0 } in
  let x0 = { x = 5.0; y = 3.0 } in
  let log = mpc_horizon_logged a bu q x0 20 in
  Array.iter (fun e ->
    Printf.printf "  %4d | %9.4f | %.4f\n" e.step e.le_cost e.le_norm
  ) log;

  (* --- REGISTER benchmark --- *)
  Printf.printf "\n=== Benchmark: REGISTER (vec2/mat2, unboxed) ===\n";
  let horizon = 20 in
  let iters_r = 1_000_000 in
  let _, ns_r = bench ~iters:iters_r (fun () ->
    let xi = ref x0 in
    for _ = 0 to horizon - 1 do
      let s = mpc2_step a bu q !xi in
      xi := s.mx
    done;
    let s = mpc2_step a bu q !xi in
    s.cost)
  in
  Printf.printf "  %d-step horizon: %.1f ns/horizon, %.1f ns/step\n"
    horizon ns_r (ns_r /. Float.of_int horizon);
  Printf.printf "  %.2f M horizons/sec\n" (1e3 /. ns_r);

  (* --- STRUCTURE benchmark --- *)
  Printf.printf "\n=== Benchmark: STRUCTURE (REGISTER + append-only log) ===\n";
  let iters_s = 500_000 in
  let _, ns_s = bench ~iters:iters_s (fun () ->
    let log = mpc_horizon_logged a bu q x0 horizon in
    log.(horizon - 1).le_cost)
  in
  Printf.printf "  %d-step horizon + log: %.1f ns/horizon, %.1f ns/step\n"
    horizon ns_s (ns_s /. Float.of_int horizon);
  Printf.printf "  %.2f M horizons/sec\n" (1e3 /. ns_s);
  Printf.printf "  Log overhead vs REGISTER: %.1fx\n" (ns_s /. ns_r);

  (* --- Spawn domain pool ONCE --- *)
  let nworkers = ndomain - 1 in (* main thread is domain 0 *)
  Printf.printf "\n=== Spawning domain pool: %d workers + 1 main ===\n" nworkers;
  let pool = make_pool nworkers in
  let workers = fst pool in

  (* --- KERNEL: parallel Monte Carlo Pi --- *)
  Printf.printf "\n=== Benchmark: KERNEL (parallel Monte Carlo Pi, 100M) ===\n";
  let n_pi = 100_000_000 in

  let pi_serial, ns_serial = time_ns (fun () ->
    let inside = ref 0 in
    let s = ref 42L in
    for _ = 1 to n_pi do
      let s', z1 = splitmix64_next !s in
      let s'', z2 = splitmix64_next s' in
      s := s'';
      let xf = Int64.to_float (Int64.shift_right_logical z1 33)
               /. Float.of_int (1 lsl 31) -. 1.0 in
      let yf = Int64.to_float (Int64.shift_right_logical z2 33)
               /. Float.of_int (1 lsl 31) -. 1.0 in
      if xf *. xf +. yf *. yf < 1.0 then incr inside
    done;
    4.0 *. Float.of_int !inside /. Float.of_int n_pi)
  in
  Printf.printf "  serial:   pi ~ %.6f | %.1f ms\n" pi_serial (ns_serial /. 1e6);

  let pi_par, ns_par = time_ns (fun () ->
    let ntasks = nworkers + 1 in
    let chunk = n_pi / ntasks in
    let inside_total = pool_tmapreduce workers
      (fun tid ->
        let count = ref 0 in
        let s = ref (Int64.add 42L (Int64.of_int (tid * 1000003))) in
        for _ = 1 to chunk do
          let s', z1 = splitmix64_next !s in
          let s'', z2 = splitmix64_next s' in
          s := s'';
          let xf = Int64.to_float (Int64.shift_right_logical z1 33)
                   /. Float.of_int (1 lsl 31) -. 1.0 in
          let yf = Int64.to_float (Int64.shift_right_logical z2 33)
                   /. Float.of_int (1 lsl 31) -. 1.0 in
          if xf *. xf +. yf *. yf < 1.0 then incr count
        done;
        Float.of_int !count)
      (+.) 0.0 ntasks
    in
    4.0 *. inside_total /. Float.of_int (chunk * ntasks))
  in
  Printf.printf "  parallel: pi ~ %.6f | %.1f ms | %d domains\n"
    pi_par (ns_par /. 1e6) ndomain;
  Printf.printf "  speedup: %.2fx\n" (ns_serial /. ns_par);

  (* --- tmap benchmark --- *)
  Printf.printf "\n=== Benchmark: tmap(sin, 0..9999999) ===\n";
  let n_map = 10_000_000 in

  let _, ns_map_s = time_ns (fun () ->
    let _a = Array.init n_map (fun i -> Float.sin (Float.of_int i *. 0.001)) in
    1.0)
  in
  Printf.printf "  serial:   %.1f ms\n" (ns_map_s /. 1e6);

  let _, ns_map_p = time_ns (fun () ->
    let _a = pool_tmap workers (fun i -> Float.sin (Float.of_int i *. 0.001)) n_map in
    1.0)
  in
  Printf.printf "  parallel: %.1f ms | %d domains\n" (ns_map_p /. 1e6) ndomain;
  Printf.printf "  speedup: %.2fx\n" (ns_map_s /. ns_map_p);

  (* --- treduce benchmark --- *)
  Printf.printf "\n=== Benchmark: tmapreduce(sin, +, 0..9999999) ===\n";

  let _, ns_red_s = time_ns (fun () ->
    let s = ref 0.0 in
    for i = 0 to n_map - 1 do
      s := !s +. Float.sin (Float.of_int i *. 0.001)
    done;
    !s)
  in
  Printf.printf "  serial:   %.1f ms\n" (ns_red_s /. 1e6);

  let _, ns_red_p = time_ns (fun () ->
    pool_tmapreduce workers
      (fun i -> Float.sin (Float.of_int i *. 0.001))
      (+.) 0.0 n_map)
  in
  Printf.printf "  parallel: %.1f ms | %d domains\n" (ns_red_p /. 1e6) ndomain;
  Printf.printf "  speedup: %.2fx\n" (ns_red_s /. ns_red_p);

  (* --- Shutdown pool --- *)
  pool_shutdown pool;

  (* --- Summary --- *)
  Printf.printf "\n=== Triad Summary ===\n";
  Printf.printf "  REGISTER:  %.1f ns/step  — unboxed vec2/mat2, zero-alloc MPC\n"
    (ns_r /. Float.of_int horizon);
  Printf.printf "  STRUCTURE: %.1f ns/step  — REGISTER + append-only trajectory log\n"
    (ns_s /. Float.of_int horizon);
  Printf.printf "  KERNEL:    %.2fx speedup — Pool-parallel tmapreduce (%d domains)\n"
    (ns_serial /. ns_par) ndomain;
  Printf.printf "\n=== Cross-Language Comparison ===\n";
  Printf.printf "  OxCaml SplitMix64:   %.2f M ops/sec (%.1f ns/op)\n"
    (Float.of_int n_sm *. 1e3 /. ns_sm) (ns_sm /. Float.of_int n_sm);
  Printf.printf "  OxCaml REGISTER MPC: %.1f ns/step (20-step horizon)\n"
    (ns_r /. Float.of_int horizon);
  Printf.printf "  (cf. C++/Eigen:      3.4 ns/step, babashka: 220 ns/op)\n";
  Printf.printf "\n=== API Mapping: OhMyThreads.jl -> OxCaml ===\n";
  Printf.printf "  tforeach(f, 1:N)            -> pool_tforeach workers f n\n";
  Printf.printf "  tmap(f, A)                  -> pool_tmap workers f n\n";
  Printf.printf "  tmapreduce(f, +, A; init=0) -> pool_tmapreduce workers f (+.) 0.0 n\n";
  Printf.printf "  Scheduler=:dynamic          -> Domain pool + Atomic work slots\n";
  Printf.printf "  @local buf = zeros(100)     -> per-domain local ref (no cross-domain escape)\n"
