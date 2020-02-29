(** ocaml-mpst-light with static linearity checking via LinOCaml. *)

include Concur_shims
include Mpst_light.Base
include Linocaml

let (let*) = Linocaml.bind
let (>>) = Linocaml.bind_

module Local : sig
  type 's local = 's Mergeable.t
  type ('v,'s) out = ('v Name.name * 's local)
  type 'var inp = 'var Event.event

  val send :
    ('s lin, unit, 'pre, 'post) lens ->
    ((< .. > as 's) -> ('v data, 't lin) out) -> 'v ->
    ('pre, 'post, 't lin) monad

  val deleg_send :
    ('s lin, unit, 'mid, 'post) lens ->
    ((< .. > as 's) -> ('t lin, 'u lin) out) ->
    ('t lin, unit, 'pre, 'mid) lens ->
    ('pre, 'post, 'u lin) monad

  val receive :
    ('s lin, unit, 'pre, 'post) lens ->
    ((< .. > as 's) -> 'var lin inp) ->
    ('pre, 'post, 'var lin) monad

  val close :
    (unit lin, unit, 'pre, 'post) lens ->
    ('pre, 'post, unit data) monad

  val create_thread_lin :
    ('s lin, unit, 'pre, 'post) lens ->
    (unit, 's lin, all_empty, 'pre2) lens ->
    (unit -> ('pre2, all_empty, unit data) monad) ->
    ('pre, 'post, unit data) monad

  val merge_out :
    ('s, 'lab) method_ ->
    ('lab, ('v, 't lin) out) method_ -> 's lin -> 's lin -> 's lin

  val merge_inp :
    ('s, 'var lin inp) method_ -> 's lin -> 's lin -> 's lin

  val closing : unit lin local

  module LinocamlStyle : sig
    val s : ('x, 'y, 'x, 'y) lens

    val send : ((< .. > as 's) -> ('v data, 't lin) out) -> 'v -> ('s lin, unit, 't lin) monad

    val deleg_send : ((< .. > as 's) -> ('t lin, 'u lin) out) -> ('s lin * 't lin, unit, 'u lin) monad

    val receive : ((< .. > as 's) -> 'var lin inp) -> ('s lin, unit, 'var lin) monad

    val close : (unit lin, unit, unit data) monad

    val create_thread_lin :
      (unit -> ('a lin, unit, unit data) monad) -> ('a lin, unit, unit data) monad
  end
end = struct
  let (let*) = IO.bind

  type 's local = 's Mergeable.t

  type ('v,'s) out = ('v Name.name * 's local)

  type 'var inp = 'var Event.event

  module L = Mpst_light.Mpst_no_lin_check.Local

  let mklin x = ({__lin=x})
  let unlin x = (x.__lin)

  let send idx sel v = {__m=(fun lpre ->
      let s = lens_get idx lpre in
      let* t = L.send (sel (unlin s)) {data=v} in
      IO.return (lens_put idx lpre (), t)
    )}

  let deleg_send idx1 sel idx2 = {__m=(fun lpre ->
      let t = lens_get idx2 lpre in
      let lmid = lens_put idx2 lpre () in
      let s = lens_get idx1 lmid in
      let* u = L.send (sel (unlin s)) t in
      IO.return (lens_put idx1 lmid (), u)
    )}

  let receive idx sel = {__m=(fun lpre ->
      let s = lens_get idx lpre in
      let* var = L.receive (sel (unlin s)) in
      IO.return (lens_put idx lpre (), var)
    )}

  let close idx = {__m=(fun lpre ->
      IO.return (lens_put idx lpre (), {data=()})
    )}

  let create_thread_lin idx idx' m =
    {__m=(fun lpre ->
         let s = lens_get idx lpre in
         let lpost = lens_put idx lpre () in
         let rec all_empty = `cons((), all_empty) in
         let (_ : Thread.t) =
           Thread.create
             (fun s -> Syntax.Internal._run (m ()) (lens_put idx' all_empty s))
             s
         in
         IO.return (lpost, {data=()})
       )}

  module LinocamlStyle = struct
    (* "root" index *)
    let s = Other ((fun x -> x), (fun _ x -> x))

    let send sel v = {__m=(fun lpre ->
        let* s = L.send (sel (unlin lpre)) {data=v} in
        IO.return ((), s)
      )}

    let deleg_send sel = {__m=(fun lpre ->
        let subj, obj = lpre in
        let* ep = L.send (sel (unlin subj)) obj in
        IO.return ((), ep)
      )}

    let receive sel = {__m=(fun lpre ->
        let* var = L.receive (sel (unlin lpre)) in
        IO.return ((), var)
      )}

    let close = {__m=(fun lpre ->
        let* () = L.close (unlin lpre) in
        IO.return ((), {data=()})
      )}

    let create_thread_lin (m: unit -> ('a lin, unit, unit data) monad) =
      {__m=(fun lpre ->
           let (_ : Thread.t) =
             Thread.create
               (fun x -> Syntax.Internal._run (m ()) x)
               lpre
           in
           IO.return ((), {data=()})
         )}
  end

  let merge_out role lab s1 s2 =
    mklin @@ L.merge_out role lab (unlin s1) (unlin s2)

  let merge_inp role s1 s2 =
    mklin @@ L.merge_inp role (unlin s1) (unlin s2)

  let merge_close s1 s2 =
    mklin @@ L.merge_close (unlin s1) (unlin s2)

  let closing =
    Mergeable.make ~value:(mklin ()) ~mergefun:merge_close ()
end

include Local

let (-->) ri rj lab g0 =
  let mklin x = ({__lin=x}) in
  let ch = Name.create () in
  let si = ri.role_index.get g0 in
  let si' =
    let out : ('v,'t) out = (ch, si) in
    rj.role_label.make_obj (lab.obj.make_obj out)
  in
  let si' = Mergeable.make ~value:(mklin si') ~cont:si ~mergefun:(Local.merge_out rj.role_label lab.obj) () in
  let g1 = ri.role_index.put g0 si'
  in
  let sj = rj.role_index.get g1 in
  let sj' =
    ri.role_label.make_obj @@
      (Event.wrap
         (Name.receive ch)
         (fun x -> mklin @@ lab.var (x, Mergeable.resolve sj)))
  in
  let sj' = Mergeable.make ~value:(mklin sj') ~cont:si ~mergefun:(Local.merge_inp ri.role_label) () in
  let g2 = rj.role_index.put g1 sj' in
  g2


module Role3 = struct
  let finish = (Local.closing, Local.closing, Local.closing)

  let choice_at ra disj (ra',g1) (ra'',g2) =
    let sa1 = ra'.role_index.get g1
    and sa2 = ra''.role_index.get g2 in
    let mklin x = ({__lin=x})
    and unlin x = (x.__lin)
    in
    let disj =
      {disj_concat=(fun l r -> mklin @@ disj.disj_concat (unlin l) (unlin r));
       disj_splitL=(fun lr -> mklin @@ disj.disj_splitL (unlin lr));
       disj_splitR=(fun lr -> mklin @@ disj.disj_splitR (unlin lr));
      }
    in
    let sa' = Mergeable.make_disj disj sa1 sa2 in
    let g1' = ra'.role_index.put g1 Mpst_light.Mpst_no_lin_check.closing
    and g2' = ra''.role_index.put g2 Mpst_light.Mpst_no_lin_check.closing in
    let (x1,x2,x3) = g1' in
    let (y1,y2,y3) = g2' in
    let g = (Mergeable.merge x1 y1, Mergeable.merge x2 y2, Mergeable.merge x3 y3) in
    let g' = ra.role_index.put g sa' in
    g'

  module G = Mpst_light.Mpst_no_lin_check.Role3

  let fix = G.fix
  let idx0 = G.idx0
  let idx1 = G.idx1
  let idx2 = G.idx2

  (** Resolve locals. *)
  let resolve (sa,sb,sc) =
    {__m=(fun pre ->
         IO.return (pre, {__lin=(Mergeable.resolve sa, Mergeable.resolve sb, Mergeable.resolve sc)})
       )}
end
include Role3
include Mpst_light.LabelUtil
