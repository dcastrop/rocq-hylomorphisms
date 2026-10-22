let time name f =
  let t0 = Sys.time () in
  let r = f () in
  Printf.printf "%-28s %8.3fs\n%!" name (Sys.time () -. t0);
  r

let () =
  Random.init 42;
  let n = 100_000 in
  let xs = List.init n (fun _ -> Uint63.of_int (Random.int 1_000_000)) in
  let ys = time "msort, n=10^5" (fun () -> Msort.msort xs) in
  let rec sorted = function
    | a :: (b :: _ as t) -> Uint63.le a b && sorted t
    | _ -> true in
  Printf.printf "  length %d, sorted %b\n" (List.length ys) (sorted ys)
