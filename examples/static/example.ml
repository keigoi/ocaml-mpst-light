
module StaticExample = struct
  open Mpst_static
  (* let g =
   *   resolve @@
   *   choice_at a (to_b left_or_right)
   *     (a, (a --> b) left @@ (a --> c) msg finish)
   *     (a, (a --> b) right @@ (a --> c) msg finish) *)

  let _ : unit Lwt.t =
    run_ @@ fun () ->
      let%lin #_0, #_1, #_2 = resolve @@ (a --> b) left finish in
      let* () =
        create_thread_lin _0 _0 begin fun () ->
          print_endline "sending";
          let%lin #_0 = send _0 (fun x -> x#role_B#left) () in
          print_endline "sent";
          close _0
        end
      in
      print_endline "receiving";
      let%lin `left({data=()}, #_1) = receive _1 (fun x -> x#role_A) in
      print_endline "received";
      close _1 >>
      close _2

  let _ : unit Lwt.t =
    let open LinocamlStyle in
    run_ @@ fun () ->
      let%lin #_0, #_1, #_2 = resolve @@ (a --> b) left finish in
      let* () =
        _0 <@ create_thread_lin begin fun () ->
          print_endline "sending";
          let%lin #s = send (fun x -> x#role_B#left) () in
          print_endline "sent";
          close
        end
      in
      let* () =
        _1 <@ begin
          print_endline "receiving";
          let%lin `left({data=()}, #s) = receive (fun x -> x#role_A) in
          print_endline "received";
          close
        end
      in
      _2 <@ close
end
