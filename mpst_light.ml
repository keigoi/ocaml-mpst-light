(** An even more light-weighted implementation of ocaml-mpst (with dynamic linearity checking). *)

(* Include concurrency adapters and base modules for convenience and shorter module path printing *)
include Concur_shims
include Base
include Base.Lin

let (let*) = IO.bind
let (and*) = IO.both
let ret = IO.return

module Local : sig
  type 's local = (flag -> 's) Mergeable.t
  (** The mergeable endpoint type, with a fresh "linearity flag" for dynamic checking. *)

  val resolve : 'a local -> 'a
  (** Resolve a mergeable (for internal use).  *)

  type ('v, 's) out = ('v Name.name * (flag -> 's) Mergeable.t)
  (** Bare output channel. *)

  type 'var inp = 'var Event.event
  (** Bare input channel. *)

  val send : ('v, 't) out lin -> 'v -> 't IO.io
  (** Output a value on a bare channel. *)

  val receive : 'var inp lin -> 'var IO.io
  (** Input a value on a bare channel. *)

  val close : unit lin -> unit IO.io
  (** Close a channel *)

  val merge_out :
    role:('s, 'lab) method_ ->
    label:('lab, ('g, 'h) out lin) method_ ->
    (flag -> 's) -> (flag -> 's) -> flag -> 's
  (** (Internal) Merge two output endpoints. *)

  val merge_inp :
    role:('s, 'var inp lin) method_ ->
    (flag -> 's) -> (flag -> 's) -> flag -> 's
  (** (Internal) Merge two input endpoints. *)

  val merge_close : 'a -> 'b -> flag -> unit lin
  (** (Internal) Merge two closing endpoints. *)

  val closed : unit lin local
  (** (Internal) Final state of a channel. *)

end = struct
  type 's local = (flag -> 's) Mergeable.t

  let resolve (t : 'a local) = Lin.fresh (Mergeable.resolve t)

  type ('v, 's) out = ('v Name.name * (flag -> 's) Mergeable.t)

  type 'var inp = 'var Event.event

  let send (out: ('v,'t) out lin) (v:'v) =
    let* (n,t) = Lin.use out in
    let* () = Event.sync (Name.send n v) in
    ret @@ resolve t

  let receive (ch: 'var inp lin) =
    let* ch = Lin.use ch in
    Event.sync ch

  let close (ep: unit lin) =
    Lin.use ep

  let merge_out ~role ~label s1 s2 = fun flag ->
    let merge_bare_out (n1,s1') (n2,s2') =
      (Name.unify n1 n2, Mergeable.merge s1' s2')
    in
    let out1 = label.call_obj @@ role.call_obj (s1 flag) in
    let out2 = label.call_obj @@ role.call_obj (s2 flag) in
    role.make_obj @@
      label.make_obj @@
        (Lin.merge merge_bare_out out1 out2)

  let merge_inp ~role s1 s2 = fun flag ->
    let merge_bare_inp ev1 ev2 =
      Event.choose [ev1; ev2]
    in
    let inp1 = role.call_obj (s1 flag) in
    let inp2 = role.call_obj (s2 flag) in
    role.make_obj @@
      (Lin.merge merge_bare_inp inp1 inp2)

  let merge_close _ _ = fun flag -> Lin.create () flag

  let closed : unit lin local =
    Mergeable.make ~value:(Lin.create ()) ~mergefun:merge_close ()
end

include Local

(**
 * Communication combinator
 *)
let (-->) ri rj lab g0 =
  let ch = Name.create () in
  let si' : _ local = ri.role_index.get g0 in
  let si flag =
    (* make the ouput channel vector *)
    rj.role_label.make_obj @@
      lab.obj.make_obj @@
        ((Lin.create (ch,si') flag) : (_,_) out lin)
    (* <role_rj = <lab = (ch,si) > > *)
  in
  let si : _ local =
    (* wrap in a mergeable *)
    Mergeable.make
      ~value:si ~cont:si' ~mergefun:(merge_out ~role:rj.role_label ~label:lab.obj) () in
  let g1 = ri.role_index.put g0 si in
  let sj' : _ local = rj.role_index.get g1 in
  let sj flag =
    (* make the input channel vector *)
    let inp =
      Event.wrap
        (Name.receive ch)
        (fun x -> lab.var (x, Local.resolve sj'))
    in
    ri.role_label.make_obj (Lin.create inp flag)
    (* <role_ri = wrap (receive ch) (λx.`lab(x,sj)) > *)
  in
  let sj : _ local = (* wrap *)
    Mergeable.make
      ~value:sj ~cont:sj' ~mergefun:(merge_inp ~role:ri.role_label) () in
  let g2 = rj.role_index.put g1 sj in
  g2

(*
val ( --> ) : ('g0, 'ti local, 'g1, 'rj local, 'ri, 'var inp lin) role ->
    ('g1, 'tj local, 'g2, 'ri local, 'rj, 'obj) role ->
    ('obj, ('v, 'ti) out, 'var, 'v * 'tj) label -> 'g0 -> 'g2
 *)
(*
where
  'ri = <role_Ri=<lab=('v,'ti) out lin>>,
  'rj = <role_Rj=[`lab of 'v * 'tj] inp lin>,
  'obj = <lab=('v, 'ti) out lin>,
  'var = [`lab of 'v * 'tj],
  'g0 = 't0 * .. * 'ti * .. * 'tj * .. * 'tn,
  'g1 = 't0 * .. * 'rj * .. * 'tj * .. * 'tn and
  'g2 = 't0 * .. * 'rj * .. * 'rj * .. * 'tn
 *)

let get_ch role g =
  Local.resolve (role.role_index.get g)

(**
 * Three-role global combinators.
 * We have an arbitrary-number-role implementation in ocaml-mpst as well.
 *)
module Role3 = struct
  (** Finished protocol. *)
  let finish =
    (closed, closed, closed)

  (** Branching protocol. *)
  let choice_at ra disj (ra',g1) (ra'',g2) =
    let sa1 = ra'.role_index.get g1
    and sa2 = ra''.role_index.get g2 in
    let disj = Lin.lift_disj disj in (* lift *)
    let sa' = Mergeable.make_disj disj sa1 sa2 in
    let g1' = ra'.role_index.put g1 closed
    and g2' = ra''.role_index.put g2 closed in
    let (x1,x2,x3) = g1' in
    let (y1,y2,y3) = g2' in
    let g = (Mergeable.merge x1 y1, Mergeable.merge x2 y2, Mergeable.merge x3 y3) in
    let g' = ra.role_index.put g sa' in
    g'

  (** Recursive protocol. *)
  let fix f : _ local * _ local * _ local =
    (* utility functions *)
    let fst (x,_,_) = x
    and snd (_,y,_) = y
    and thd (_,_,z) = z in
    let fst_lazy t : _ local = Mergeable.make_recvar (lazy (fst @@ Lazy.force t))
    and snd_lazy t : _ local = Mergeable.make_recvar (lazy (snd @@ Lazy.force t))
    and thd_lazy t : _ local  = Mergeable.make_recvar (lazy (thd @@ Lazy.force t))
    in
    (* Tying a knot as (let rec x = f x in f). Laziness is for value recursion. *)
    let rec body = lazy (f (fst_lazy body, snd_lazy body, thd_lazy body)) in
    Lazy.force body

  let idx0 : ('t0 * 't1 * 't2, 't0, 't0r * 't1 * 't2, 't0r) idx =
    {get = (fun (x,_,_) -> x); put = (fun (_,x1,x2) x0 -> (x0,x1,x2))}
  let idx1 : ('t0 * 't1 * 't2, 't1, 't0 * 't1r * 't2, 't1r) idx =
    {get = (fun (_,x,_) -> x); put = (fun (x0,_,x2) x1 -> (x0,x1,x2))}
  let idx2 : ('t0 * 't1 * 't2, 't2, 't0 * 't1 * 't2r, 't2r) idx =
    {get = (fun (_,_,x) -> x); put = (fun (x0,x1,_) x2 -> (x0,x1,x2))}

  let resolve (a,b,c) =
    (Local.resolve a, Local.resolve b, Local.resolve c)
end
include Role3

(** Utility module for roles and labels *)
module LabelUtil = struct
  let a = {role_label={make_obj=(fun v->object method role_A=v end);
                       call_obj=(fun o->o#role_A)};
           role_index=idx0}
  let b = {role_label={make_obj=(fun v->object method role_B=v end);
                       call_obj=(fun o->o#role_B)};
           role_index=idx1}
  let c = {role_label={make_obj=(fun v->object method role_C=v end);
                       call_obj=(fun o->o#role_C)};
           role_index=idx2}
  let to_ m r1 r2 r3 =
    let (!) x = x.role_label in
    {disj_concat=(fun l r -> !r1.make_obj (m.disj_concat (!r2.call_obj l) (!r3.call_obj r)));
     disj_splitL=(fun lr -> !r2.make_obj (m.disj_splitL @@ !r1.call_obj lr));
     disj_splitR=(fun lr -> !r3.make_obj (m.disj_splitR @@ !r1.call_obj lr));
    }
  let to_a m = to_ m a a a
  let to_b m = to_ m b b b
  let to_c m = to_ m c c c
  let msg =
    {obj={make_obj=(fun f -> object method msg=f end);
          call_obj=(fun o -> o#msg)};
     var=(fun v -> `msg(v))}
  let left =
    {obj={make_obj=(fun f -> object method left=f end);
          call_obj=(fun o -> o#left)};
     var=(fun v -> `left(v))}
  let right =
    {obj={make_obj=(fun f -> object method right=f end);
          call_obj=(fun o -> o#right)};
     var=(fun v -> `right(v))}
  let middle =
    {obj={make_obj=(fun f -> object method middle=f end);
          call_obj=(fun o -> o#middle)};
     var=(fun v -> `middle(v))}

  let left_or_right =
    {disj_concat=(fun l r -> object method left=l#left method right=r#right end);
     disj_splitL=(fun lr -> (lr :> <left : _>));
     disj_splitR=(fun lr -> (lr :> <right : _>));
    }
  let right_or_left =
    {disj_concat=(fun l r -> object method right=l#right method left=r#left end);
     disj_splitL=(fun lr -> (lr :> <right : _>));
     disj_splitR=(fun lr -> (lr :> <left : _>));
    }

  let left_middle_or_right =
    {disj_concat=(fun l r -> object method left=l#left method middle=l#middle method right=r#right end);
     disj_splitL=(fun lr -> (lr :> <left : _; middle: _>));
     disj_splitR=(fun lr -> (lr :> <right : _>));
    }

  let left_or_middle =
    {disj_concat=(fun l r -> object method left=l#left method middle=r#middle end);
     disj_splitL=(fun lr -> (lr :> <left : _>));
     disj_splitR=(fun lr -> (lr :> <middle : _>));
    }

  let left_or_middle_right =
    {disj_concat=(fun l r -> object method left=l#left method middle=r#middle method right=r#right end);
     disj_splitL=(fun lr -> (lr :> <left : _>));
     disj_splitR=(fun lr -> (lr :> <middle: _; right : _>));
    }

  let middle_or_right =
    {disj_concat=(fun l r -> object method middle=l#middle method right=r#right end);
     disj_splitL=(fun lr -> (lr :> <middle : _>));
     disj_splitR=(fun lr -> (lr :> <right : _>));
    }
end
include LabelUtil

(* Re-export for sub-packages *)
module Base = Base

(* No linearity-checking version, for better understanding of the implementation code *)
module Mpst_no_lin_check = Mpst_no_lin_check
