let time name f =
  let t0 = Sys.time () in
  let r = f () in
  Printf.printf "%-28s %8.3fs\n%!" name (Sys.time () -. t0);
  r

open Shortcutfusion

let () =
  let xs = List.init 100_000 (fun i -> i) and ys = List.init 100_000 (fun i -> i) in
  let n = time "ex1 (length.map.append), 2x10^5" (fun () -> ex1_code (fun x -> x + 1) ys xs) in
  Printf.printf "  length %s\n" (Uint63.to_string n);
  let zs = List.init 2_000 (fun i -> i) in
  let m = time "ex2 (length.reverse), n=2000" (fun () -> ex2_code zs) in
  Printf.printf "  length %s\n" (Uint63.to_string m)
