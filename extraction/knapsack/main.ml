let time name f =
  let t0 = Sys.time () in
  let r = f () in
  Printf.printf "%-28s %8.3fs\n%!" name (Sys.time () -. t0);
  r

let () =
  let u = Uint63.of_int in
  let items =
    [ (3, 4); (4, 5); (7, 10); (8, 11); (9, 13); (12, 17); (15, 21) ] in
  let wvs = List.map (fun (w, v) -> (u w, u v)) items in
  List.iter (fun cap ->
    let r = time (Printf.sprintf "knapsack, capacity %d" cap)
      (fun () -> Knapsack.knapsack_arr wvs (u cap)) in
    Printf.printf "  best value %s\n" (Uint63.to_string r))
    [ 100; 1_000; 5_000; 100_000; 1_000_000 ]
