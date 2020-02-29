module IO = struct
  type +'a io = 'a Lwt.t
  let bind = Lwt.bind
  let both = Lwt.both
  let return = Lwt.return
  let map = Lwt.map
end

module List = struct
  include List
  let iter = Lwt_list.iter_s
end

module Event : sig
  type 'a channel
  val new_channel : unit -> 'a channel
  type +'a event
  val send : 'a channel -> 'a -> unit event
  val receive : 'a channel -> 'a event
  val choose : 'a event list -> 'a event
  val wrap : 'a event -> ('a -> 'b) -> 'b event
  val guard : (unit -> 'a event) -> 'a event
  val sync : 'a event -> 'a IO.io
end
  = struct
  type 'a channel = 'a Lwt_mvar.t Lwt_mvar.t
  let new_channel () = Lwt_mvar.create_empty ()
  type +'a event = unit -> 'a Lwt.t
  let (let/) = Lwt.bind
  let send mvar v () =
    let/ sync = Lwt_mvar.take mvar in
    Lwt_mvar.put sync v
  let receive mvar () =
    let sync = Lwt_mvar.create_empty () in
    let/ () = Lwt_mvar.put mvar sync in
    Lwt_mvar.take sync
  let choose xs () = Lwt.choose (List.map (fun f -> f ()) xs)
  let wrap t f () = Lwt.map f (t ())
  let guard f = f ()
  let sync x = x ()
end

module Thread : sig
  type t
  val create : ('a -> 'b IO.io) -> 'a -> t
  (* val delay: float -> unit *)
  val join : t -> unit IO.io
end = struct
  type t = unit Lwt.t
  let create f x =
    let t,u = Lwt.wait () in
    Lwt.async (fun () ->
        Lwt.map (fun _ -> Lwt.wakeup_later u ()) (f x));
    t
  let join t = Lwt.join [t]
end

module Mutex : sig
  type t
  val create : unit -> t
  val lock : t -> unit IO.io
  val try_lock : t -> bool Lwt.t
  val unlock : t -> unit
end = struct
  type t = Lwt_mutex.t
  let (let/) = Lwt.bind
  let create = Lwt_mutex.create
  let lock = Lwt_mutex.lock
  let try_lock t =
    if Lwt_mutex.is_locked t then
      Lwt.return false
    else
      let/ () = Lwt_mutex.lock t in
      Lwt.return true
  let unlock = Lwt_mutex.unlock
end
