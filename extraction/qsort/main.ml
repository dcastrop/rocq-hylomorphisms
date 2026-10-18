let time name f =
  let t0 = Sys.time () in
  let r = f () in
  Printf.printf "%-28s %8.3fs\n%!" name (Sys.time () -. t0);
  r

let () =
  Random.init 42;
  let n = 100_000 in
  let xs = List.init n (fun _ -> Uint63.of_int (Random.int 1_000_000)) in
  let ys = time "qsort, n=10^5" (fun () -> Qsort.qsort_code xs) in
  let rec sorted = function
    | a :: (b :: _ as t) -> Uint63.le a b && sorted t
    | _ -> true in
  Printf.printf "  length %d, sorted %b\n" (List.length ys) (sorted ys)

let () =
  let xs = List.init 100_000 (fun i -> Uint63.of_int ((i * 7919) mod 100_003)) in
  let ys = time "qsort_times_two, n=10^5" (fun () -> Qsort.qsort_times_two_code xs) in
  Printf.printf "  length %d\n" (List.length ys)
