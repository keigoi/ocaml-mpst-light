open Mpst_light

module OAuthExample = struct
  let c = {role_label=
             {make_obj=(fun v->object method role_C=v end);
              call_obj=(fun obj->obj#role_C)};
           role_index=idx0}

  let s = {role_label=
             {make_obj=(fun v->object method role_S=v end);
              call_obj=(fun obj->obj#role_S)};
           role_index=idx1}

  let a = {role_label=
             {make_obj=(fun v->object method role_A=v end);
              call_obj=(fun obj->obj#role_A)};
           role_index=idx2}

  let login =
    {obj={make_obj=(fun v->object method login=v end);call_obj=(fun obj->obj#login)};
     var=(fun v->`login v)}

  let pwd =
    {obj={make_obj=(fun v->object method pwd=v end);call_obj=(fun obj->obj#pwd)};
     var=(fun v->`pwd v)}

  let auth =
    {obj={make_obj=(fun v->object method auth=v end);call_obj=(fun obj->obj#auth)};
     var=(fun v->`auth v)}


  let oAuth () = (s --> c) login @@ (c --> a) pwd @@ (a --> s) auth @@ finish
end

module Example = struct
  let sample_prot () =
    (a --> c) msg @@
    fix (fun t ->
          (c --> b) msg @@
          choice_at a (to_b left_or_right)
            (a, (a --> b) left @@
                (c --> b) msg @@
                (b --> c) left @@ t)
            (a, (a --> b) right @@
                (c --> b) msg @@
                (b --> c) right @@ finish))
end

module UnfairExample = struct

  let unfair () =
    let g =
      fix (fun t ->
          choice_at a (to_b right_or_left)
            (a, (a --> b) right @@
                  t)
            (a, (a --> b) left @@
                  (a --> c) left @@
                    finish))
    in
    g

  let run () =
    let g = unfair ()
    in
    let ea = get_ch a g in
    print_endline"projected on a";
    let eb = get_ch b g in
    print_endline"projected on b";
    let ec = get_ch c g in
    print_endline"projected on c";
    print_endline"projected on d";
    let ta = Thread.create (fun () ->
                 let* ea = send ea#role_B#right () in
                 let* ea = send ea#role_B#right () in
                 let* ea = send ea#role_B#right () in
                 let* ea = send ea#role_B#right () in
                 let* ea = send ea#role_B#left () in
                 let* ea = send ea#role_C#left () in
                 close ea
               )()
    and tb = Thread.create (fun () ->
                 let rec loop eb =
                   let* var = receive eb#role_A in
                   match var with
                   | `right(_,eb) ->
                      print_endline "B: right";
                      loop eb
                   | `left(_,eb) ->
                      print_endline "B: left";
                      close eb
                 in
                 loop eb) ()
    and tc = Thread.create (fun () ->
                 let* `left(_,ec) = receive ec#role_A in
                 print_endline "C: closing";
                 close ec) ()
    in
    List.iter Thread.join [ta; tb; tc]
end

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
