(** Utility types and modules *)

open Concur_shims

(** First-class methods *)
type ('obj,'mt) method_ =
  {make_obj: 'mt -> 'obj; call_obj: 'obj -> 'mt} (* constraint 'obj = < .. > *)

(** Type-level indices represented by polymorphic lenses *)
type ('ts, 't, 'us, 'u) idx =
  {get: 'ts -> 't; put: 'ts -> 'u -> 'us}

(** Message labels for global combinators. See examples. *)
type ('obj,'ot,'var,'vt) label =
  {obj: ('obj, 'ot) method_; var: 'vt -> 'var} (* constraint 'var = [>] *)

(** Role types for global combinators. See examples *)
type ('ts, 't, 'us, 'u, 'robj, 'mt) role =
  {
    role_index: ('ts,'t,'us,'u) idx;
    (** The index of a role. Zero is "('x1*'y*'z, 'x1, 'x2*'y*'z, 'x2) idx" For three-role case. *)
    role_label:('robj,'mt) method_
    (** The label of a role. Normally it looks like (<role_A: 't>, 't) method_  *)
  }

(** Disjoint concatenation/splitting of two objects  *)
type ('lr, 'l, 'r) disj =
  {disj_concat: 'l -> 'r -> 'lr;
   disj_splitL: 'lr -> 'l;
   disj_splitR: 'lr -> 'r;
  }
  (* constraint 'lr = < .. >
   * constraint 'l = < .. >
   * constraint 'r = < .. > *)

(**
 * The module for merging channel vectors.
 * As we can't directly analyse methods and (polymorphic) variant constructors in OCaml,
 * instead we pair structural objects with a ``merging function''.
 *
 * Uninterested readers can skip this module.
 *
 * Furthermore, another trick is instrumented for loops with `unbalanced' choice,
 * where some roles do not participate in a choice.
 * For example, the choice in the following global protocol is unbalanced:
 *
 *   fix t ->
 *     choice_at a {
 *       (a --> b) left;
 *       (b --> c) msg;
 *       finish
 *     } or {
 *       (a --> b) right;
 *       t
 *     }
 *
 * See that `c' does not participate in the second branch.
 * The resulting channel vector involves merging with recursion variables --
 * for example, the above c's channel vector will be μt.(<role_B=[`msg(_n,end)]> ⊔ t)
 * (where [`msg(_n,end)] is a shorthand of (Event.wrap n (λx.(x,end)) for some name n) and
 * we just remove bare occurrence of `t' since ⊔ is monotonic, obtaining <b=[`msg(_n,end)]>.
 *)
module Mergeable
       : sig
  type 'a t
  (** A mergeable *)

  val make :value:'a -> mergefun:('a -> 'a -> 'a) -> ?cont:'x t -> unit -> 'a t
  (** Make a mergeable value, with a merging function and an optional continuation *)

  val merge : 'a t -> 'a t -> 'a t
  (** Merge two mergeables *)

  val make_recvar : 'a t lazy_t -> 'a t
  (** Declare a delayed mergeable, which is used in a recursion variable (fix (fun t -> ...)).  *)

  val make_disj : ('lr,'l,'r) disj -> 'l t -> 'r t -> 'lr t
  (** Concatenate two disjoint mergeables into one using a `disj' *)

  val resolve : 'a t -> 'a
  (** Extract the value from a mergeable *)

end
  = struct
  type hook = unit lazy_t
  type 'a mvalue =
    {value: 'a; mergefun: 'a -> 'a -> 'a; hook: hook}
  type 'a cache = 'a mvalue lazy_t

  type 'a t =
    | Value : 'a mvalue -> 'a t
    (** fully resolved merge *)
    | RecVar : 'a t lazy_t * 'a cache -> 'a t
    (** (A) a recursion variable *)
    | Merge : 'a t * 'a t * 'a cache -> 'a t
    (** (B) delayed merge involving recvars *)
    | Disj   : 'l t * 'r t * ('lr,'l,'r) disj * 'lr cache -> 'lr t
    (** (C) disjoint merge involving recvars  (output) *)

  exception UnguardedLoop

  let seq_hook l r = lazy (Lazy.force l.hook; Lazy.force r.hook)

  let merge_value l r =
    {value=l.mergefun l.value r.value;
     mergefun=l.mergefun;
     hook=seq_hook l r}

  let make_value_disj
      : 'lr 'l 'r. ('lr,'l,'r) disj -> 'l mvalue -> 'r mvalue -> 'lr mvalue =
    fun disj bl br ->
    let mergefun lr1 lr2 =
      disj.disj_concat
        (bl.mergefun (disj.disj_splitL lr1) (disj.disj_splitL lr2))
        (br.mergefun (disj.disj_splitR lr1) (disj.disj_splitR lr2))
    in
    let value = disj.disj_concat bl.value br.value
    in
    {value; mergefun; hook=seq_hook bl br}

  let rec find_phys_eq : 'a. 'a list -> 'a -> bool = fun xs y ->
    match xs with
    | x::xs -> if x==y then true else find_phys_eq xs y
    | [] -> false

  (**
   * Resolve delayed merges.
   * It carries list of recursion variables forced in the first arg, so that
   *
   *)
  let rec real_resolve : type x. x t lazy_t list -> x t -> x mvalue option = fun hist ->
      function
      | Value v ->
         Some v (* already resolved *)
      | RecVar (t, _) ->
         (* (A) a recursion variable -- check occurrence of it *)
         if find_phys_eq hist t then begin
             None (* we found a cycle of form (μt. .. ⊔ t ⊔ ..) -- strip t *)
           end else begin
             (* force and resolve it *)
             real_resolve (t::hist) (Lazy.force t)
           end
      | Merge (s, t, _) ->
         (* (B) merge recursion variables *)
         begin match real_resolve hist s, real_resolve hist t with
         | Some s, Some t ->
            Some (merge_value s t)
         | Some s, None | None, Some s ->
            Some s
         | None, None ->
            None
         end
      | Disj (l,r,mrg,_) ->
         (* (C) disjoint merge involves recursion variables *)
         (* we can safely reset the history; as the two types are
            different from the original one, the same type variable will not occur. *)
         let l = do_real_resolve l in
         let r = do_real_resolve r in
         Some (make_value_disj mrg l r)

  and do_real_resolve : 'a. 'a t -> 'a mvalue = fun t ->
    match real_resolve [] t with
    | Some v -> v
    | None -> raise UnguardedLoop

  let make_recvar t =
    let rec d = RecVar (t, lazy (do_real_resolve d))
    in d

  let make_merge_delayed : 'a. 'a t -> 'a t -> 'a t = fun s t ->
    let rec d = Merge (s, t, lazy (do_real_resolve d))
    in d

  let merge : 'a. 'a t -> 'a t -> 'a t = fun l r ->
    match l, r with
    | Value ll, Value rr ->
       let blr = merge_value ll rr in
       Value blr
    | _ ->
       make_merge_delayed l r

  let make_disj : 'lr 'l 'r. ('lr,'l,'r) disj -> 'l t -> 'r t -> 'lr t = fun mrg l r ->
    match l, r with
    | Value bl, Value br ->
       let blr = make_value_disj mrg bl br in
       Value blr
    | _ ->
       let rec d = Disj (l,r,mrg, lazy (do_real_resolve d))
       (* prerr_endline "WARNING: internal choice involves recursion variable"; *)
       in d

  let resolve : type x. x t -> x = fun t ->
    let b =
      match t with
      | Value b ->
        b
      | RecVar (_,d) ->
        Lazy.force d
      | Disj (_,_,_,d) ->
        Lazy.force d
      | Merge (_,_,d) ->
        Lazy.force d
    in
    Lazy.force b.hook;
    b.value

  let make ~value ~mergefun ?cont () =
    let hook =
      match cont with
      | None -> Lazy.from_val ()
      | Some cont -> lazy (ignore (resolve cont))
    in
    Value {mergefun;value;hook}
end

(**
 * ``Unifiable'' names. Uninterested readers can skip this, as it is just
 * a channel for synchronous communication for the first place.
 *
 * This is required for choices with output from `non-enabled' roles --
 * For example, the following protocol has an output from c, which is not enabled
 * (i.e., c can output without waiting in both branches):
 *
 *   choice_at a {
 *     (a --> b) left; (c --> b) msg; finish
 *   } or {
 *     (a --> b) right; (c --> b) msg; finish
 *   }
 *
 * While there is no need to merge outputs from enabled roles
 * (because they guarded by some input or another output),
 * non-enabled outputs need merging.
 *
 * (Normally, such output can be factored out, but in some `joining' global protocols like
 * Two Producer-Consumer, this seems inevitable.)
 *
 * For example, in the above, we have two channel vectors at `c', with same structure
 * but different names:
 *
 *   <role_B=<msg=(n1,())>> and <role_B=<msg=(n2,())>>
 *
 * for some n1 and n2, but we must deterministically output values on
 * those two alternatives.
 *
 * Because of that, we `unify' these names (n1 and n2) so that
 * (1) outputs become deterministic, and
 * (2) inputs can receive those values.
 *
 * Note that this is not a mere substitution; unification is propagated to input side so that
 * the values in transmission are correctly delivered to the input end.
 *
 * Also note this strategy is not usable in asynchronous cases
 * (which is why we invented Mstream for Lwt).
 *)
module Name
  : sig
  type 'v name
  (** Type of a name communicating value 'v *)

  val create : unit -> 'a name
  (** Create a fresh name *)

  val unify : 'v name -> 'v name -> 'v name
  (** Unify two names into one *)

  val send : 'v name -> 'v -> unit Event.event
  (** Output a value on the name *)

  val receive : 'v name -> 'v Event.event
  (** Input a value on the name *)
end
= struct
  type 'v name = 'v name_ ref
  and 'v name_ =
      Chan of 'v Event.channel
    | Subst of 'v name_ ref

  let create () =
    ref (Chan (Event.new_channel ()))

  (* record a substitution n1 := n2 *)
  let rec unify (n1:'v name) (n2:'v name) : 'v name =
    begin match !n1 with
    | Chan _ ->
       n1 := Subst n2
    | Subst r ->
       ignore (unify r n2)
    end;
    n1

  (* resolve substitution and extract an OCaml channel from a name *)
  let rec resolve (n : 'v name) : 'v Event.channel=
    match !n with
    | Chan ch -> ch
    | Subst r -> resolve r

  let send (n : 'v name) (v : 'v) : unit Event.event =
    Event.send (resolve n) v

  let receive (n : 'v name) : 'v Event.event =
    Event.guard (fun () -> Event.receive (resolve n))
end

(** An abstraction for dynamic linearity checking *)
module Lin : sig
  type +'a lin
  (** Linear type constructor *)

  type flag
  (** Dynamic linearity flag *)

  val use : 'a lin -> 'a IO.io
  (** Extract the value. Raises InvalidEndpoint if the endpoint is already consumed *)

  val create : 'a -> flag -> 'a lin
  (** Declare a linear resource *)

  val fresh : (flag -> 'a) -> 'a
  (** Generate a fresh linear resource  *)

  val merge : ('a -> 'a -> 'a) -> 'a lin -> 'a lin -> 'a lin
  (** Merge two linear values (having the same flag) *)

  val lift_disj : ('lr,'l,'r) disj -> (flag -> 'lr, flag -> 'l, flag -> 'r) disj
  (** Lift given disjoint concatenation *)
end = struct
  exception InvalidEndpoint
  let (let*) = IO.bind

  module Flag = struct
    type t         = Mutex.t
    let create ()  = Mutex.create ()
    let use f      =
      let* b = Mutex.try_lock f in
      if b then
        IO.return ()
      else
        raise InvalidEndpoint
  end

  type +'a lin = {once:Flag.t; value: 'a}
  type flag = Flag.t
  let use t =
    let* () = Flag.use t.once in
    IO.return t.value
  let create v = fun once -> {once; value=v}
  let fresh f = f (Flag.create ())
  let merge f x y = assert (x.once==y.once); {value=f x.value y.value; once=x.once}
  let lift_disj mrg =
    {disj_concat=(fun ls rs once -> mrg.disj_concat (ls once) (rs once));
     disj_splitL=(fun lr once -> mrg.disj_splitL (lr once));
     disj_splitR=(fun lr once -> mrg.disj_splitR (lr once))}
end
type 'a lin = 'a Lin.lin
type flag = Lin.flag
