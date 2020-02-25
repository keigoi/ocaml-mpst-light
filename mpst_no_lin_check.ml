(** ocaml-mpst-light without linearity checking, for better understanding of the implementation code. *)

include Concur_shims
include Base

let (let/) = IO.bind
let ret = IO.return

module Local = struct
  type 's local = 's Mergeable.t
  (** The local type is a "mergeable". See `Mergeable` module. *)

  type ('v,'s) out = ('v Name.name * 's local)
  (**
   * A bare output channel is a pair ('v name * 't Mergeable.t) where
   * 'v is a payload and 't is a continuation.
   * We need the mergeable continuation for recursive merging.
   *)

  type 'var inp = 'var Event.event
  (**
   * A bare input channel where 'var is [`lab1 of 'v * 't | .. | `labn of 'v * 't].
   *)

  (** Output a value on a bare output channel. *)
  let send ((n,t): ('v,'t) out) (v:'v) =
    let/ () = Event.sync (Name.send n v) in
    ret @@ Mergeable.resolve t

  (** Input a value on a bare input channel. *)
  let receive (ch: 'var inp) =
    Event.sync ch

  (** Close a channel *)
  let close (_: unit) = ret ()

  (**
   * Merge (output case) for internal use.
   *  <role_r=<lab=(n1,s1')>> ⊔ <role_r=<lab=(n2,s2')>> = <role_r=<lab=(unify n1 n2, s1 ⊔ s2)>>
   *)
  let merge_out role label s1 s2 =
    let (n1, s1') : ('v,'t) out = label.call_obj @@ role.call_obj s1 in
    let (n2, s2') : ('v,'t) out = label.call_obj @@ role.call_obj s2 in
    role.make_obj @@
      label.make_obj @@
        (Name.unify n1 n2, Mergeable.merge s1' s2')

  (**
   * Merge (input case) for internal use.
   * <role_r=[`lab_i(_ci,si)]i∈I> ⊔ <role_r=[`lab_j(_cj,sj)]j∈J> = <role_r=[`lab_k(_ck,sk)]k∈I∪J>
   *
   * where [`lab_i(_ci,si)]i∈I is a shorthand of
   *   (choose [wrap c1 (λx.(x,s1)); ...; wrap cn (λx.(x,sn))])
   *)
  let merge_inp role s1 s2 =
    let ev1 = role.call_obj s1 in
    let ev2 = role.call_obj s2 in
    role.make_obj @@
      Event.choose [ev1; ev2]

  (**
   * Merge (closing case) for internal use.
   *)
  let merge_close () () = ()

  (**
   * Closing a channel.
   *)
  let closing : unit local =
    Mergeable.make ~value:() ~mergefun:merge_close ()
end

include Local

(**
 * The communication combinator.
 * "(a --> b) lab cont" represents a protocol where "a" send a "lab" to "b",
 * which makes a tuple of channel vectors with:
 * (1) at role a, output of a label lab to b then cont,
 * (2) at role b, input of a label lab from a then cont, and
 * (3) at other roles, same as cont.
 *)
let (-->) ri rj lab g0 =
  let ch = Name.create () in
  (* make the ouput channel vector *)
  let si = ri.role_index.get g0 in
  let si' =
    (* <role_rj = <lab = (ch,si) > > *)
    let out : ('v,'t) out = (ch,si) in
    rj.role_label.make_obj (lab.obj.make_obj out)
  in
  (* wrap it within a mergeable *)
  let si' = Mergeable.make ~value:si' ~cont:si ~mergefun:(merge_out rj.role_label lab.obj) () in
  let g1 = ri.role_index.put g0 si'
  in
  (* make the input channel vector *)
  let sj = rj.role_index.get g1 in
  let sj' =
    (* <role_ri = wrap (receive ch) (λx.`lab(x,sj)) > *)
    ri.role_label.make_obj @@
      (Event.wrap
         (Name.receive ch)
         (fun x -> lab.var (x, Mergeable.resolve sj)))
  in
  let sj' = Mergeable.make ~value:sj' ~cont:si ~mergefun:(merge_inp ri.role_label) () in
  let g2 = rj.role_index.put g1 sj' in
  g2

(*
val ( --> ) : ('g0, 'ti local, 'g1, 'rj local, 'ri, 'var inp) role ->
    ('g1, 'tj local, 'g2, 'ri local, 'rj, 'obj) role ->
    ('obj, ('v, 'ti) out, 'var, 'v * 'tj) label -> 'g0 -> 'g2
 *)
(*
where
  'ri = <role_Ri=<lab=('v,'ti) out>>,
  'rj = <role_Rj=[`lab of 'v * 'tj] inp>,
  'obj = <lab=('v, 'ti) out>,
  'var = [`lab of 'v * 'tj],
  'g0 = 't0 * .. * 'ti * .. * 'tj * .. * 'tn,
  'g1 = 't0 * .. * 'rj * .. * 'tj * .. * 'tn and
  'g2 = 't0 * .. * 'rj * .. * 'rj * .. * 'tn
 *)

let get_ch role g =
  Mergeable.resolve (role.role_index.get g)

(**
 * Three-role global combinators.
 * We have an arbitrary-number-role implementation in ocaml-mpst as well.
 *)
module Role3 = struct
  (** Finished protocol *)
  let finish =
    (closing, closing, closing)

  (** Branching combinator. choice_at a disj (a, cont1) (a, cont2) *)
  let choice_at ra disj (ra',g1) (ra'',g2) =
    let sa1 = ra'.role_index.get g1
    and sa2 = ra''.role_index.get g2 in
    let sa' = Mergeable.make_disj disj sa1 sa2 in
    let g1' = ra'.role_index.put g1 closing
    and g2' = ra''.role_index.put g2 closing in
    let (x1,x2,x3) = g1' in
    let (y1,y2,y3) = g2' in
    let g = (Mergeable.merge x1 y1, Mergeable.merge x2 y2, Mergeable.merge x3 y3) in
    let g' = ra.role_index.put g sa' in
    g'

  (** Recursion combinator. *)
  let fix f =
    (* utility functions *)
    let fst (x,_,_) = x
    and snd (_,y,_) = y
    and thd (_,_,z) = z in
    let fst_lazy t = Mergeable.make_recvar (lazy (fst @@ Lazy.force t))
    and snd_lazy t = Mergeable.make_recvar (lazy (snd @@ Lazy.force t))
    and thd_lazy t = Mergeable.make_recvar (lazy (thd @@ Lazy.force t))
    in
    (* Tying a knot as (let rec x = f x in f). Laziness is for value recursion. *)
    let rec body = lazy (f (fst_lazy body, snd_lazy body, thd_lazy body)) in
    Lazy.force body

  (** Type-level index 0 (for internal use). *)
  let idx0 : ('t0 * 't1 * 't2, 't0, 't0r * 't1 * 't2, 't0r) idx =
    {get = (fun (x,_,_) -> x); put = (fun (_,x1,x2) x0 -> (x0,x1,x2))}

  (** Type-level index 1 (for internal use). *)
  let idx1 : ('t0 * 't1 * 't2, 't1, 't0 * 't1r * 't2, 't1r) idx =
    {get = (fun (_,x,_) -> x); put = (fun (x0,_,x2) x1 -> (x0,x1,x2))}

  (** Type-level index 2 (for internal use). *)
  let idx2 : ('t0 * 't1 * 't2, 't2, 't0 * 't1 * 't2r, 't2r) idx =
    {get = (fun (_,_,x) -> x); put = (fun (x0,x1,_) x2 -> (x0,x1,x2))}

  (** Resolve locals. *)
  let resolve (a,b,c) =
    (Mergeable.resolve a, Mergeable.resolve b, Mergeable.resolve c)
end
include Role3

(*
  val finish : unit local * unit local * unit local

  val choice_at :
    ('a local * 'b local * 'c local, _, 'g3,  'sa local, _, _) role ->
    ('sa, 'sa1, 'sa2) disj ->
    ('g1, 'sa1 local, 'a local * 'b local * 'c local, unit local, _, _) role * 'g1 ->
    ('g2, 'sa2 local, 'a local * 'b local * 'c local, unit local, _, _) role * 'g2 ->
    'g3

  val fix : ('a local * 'b local * 'c local -> 'a local * 'b local * 'c local) ->
    'a local * 'b local * 'c local

  val get_ch : ('g, 's local, _, _, _, _) role -> 'g -> 's

  val idx0 : ('t0 * 't1 * 't2, 't0, 't0r * 't1  * 't2, 't0r) idx
  val idx1 : ('t0 * 't1 * 't2, 't1, 't0  * 't1r * 't2, 't1r) idx
  val idx2 : ('t0 * 't1 * 't2, 't2, 't0  * 't1  * 't2r, 't2r) idx
*)
