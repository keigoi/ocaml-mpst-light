module IO = struct
  type +'a io = 'a
  let bind m f = f m
  let both a b = (a, b)
  let map f x = f x
  let return x = x
end

module Thread = Thread
module Event = Event
module List = List
module Mutex = Mutex
