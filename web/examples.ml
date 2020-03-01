(** Basic Usage *)

open Mpst_light

let g = (a --> b) msg @@ (b --> c) msg finish

let sa = get_ch a g and sb = get_ch b g and sc = get_ch c g

let _ = Thread.create (fun () ->
  let* sa = send sa#role_B#msg ["Hello,"; "OCaml"; "World!"] in close sa
) ()

let _ = Thread.create (fun () ->
  let* `msg(strs,sb) = receive sb#role_A in
  let* sb = send sb#role_C#msg (String.concat " " strs) in
  close sb
) ()

let _ =
  let* `msg(str,sc) = receive sc#role_B in
  print_endline str;
  close sc

(** Static Linearity Checking *)

open Mpst_static

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
    let%lin `left(_, #_1) = receive _1 (fun x -> x#role_A) in
    print_endline "received";
    close _1 >>
    close _2
