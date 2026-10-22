let time name f =
  let t0 = Sys.time () in
  let r = f () in
  Printf.printf "%-28s %8.3fs\n%!" name (Sys.time () -. t0);
  r

let u = Uint63.of_int

let () =
  let n = 1_000_000 in
  let p = time "fast_power 3 i, i<=10^6" (fun () ->
    let acc = ref (u 0) in
    for i = 1 to n do
      acc := Uint63.add !acc (Digits.fast_power (u 3) (u i))
    done;
    !acc) in
  Printf.printf "  checksum %s\n" (Uint63.to_string p);
  let s1 = time "sumsq_fold i, i<=10^6" (fun () ->
    let acc = ref (u 0) in
    for i = 1 to n do acc := Uint63.add !acc (Digits.sumsq_fold (u i)) done;
    !acc) in
  let s2 = time "sumsq_unfold i, i<=10^6" (fun () ->
    let acc = ref (u 0) in
    for i = 1 to n do acc := Uint63.add !acc (Digits.sumsq_unfold (u i)) done;
    !acc) in
  Printf.printf "  checksums %s %s\n"
    (Uint63.to_string s1) (Uint63.to_string s2)
