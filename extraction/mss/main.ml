let time name f =
  let t0 = Sys.time () in
  let r = f () in
  Printf.printf "%-28s %8.3fs\n%!" name (Sys.time () -. t0);
  r

let () =
  Random.init 42;
  let n = 100_000 in
  let xs = List.init n (fun _ -> Bigint.of_int (Random.int 201 - 100)) in
  let r = time "mss_linear, n=10^5" (fun () -> Mss.mss_code xs) in
  match r with
  | Some m -> Printf.printf "  mss = %s\n" (Bigint.to_string m)
  | None -> print_endline "  mss = -inf"
