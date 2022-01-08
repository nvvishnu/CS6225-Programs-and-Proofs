module Memo

open FStar.All
open FStar.Ref

(* 15 points - Delete the type [False] and write down the correct spec. You may want
to separate out the [cache_miss] function to its own definition for defining its
spec. *)

val cache_miss: r: ref (option (int*int)) ->  f:( int -> int) -> v: int  -> ST int  (requires (fun h_pre -> True)) (ensures (fun h_pre q h_post ->  modifies !{r} h_pre h_post /\ (q== f v)/\ (sel h_post r == Some (v,f v))))


let cache_miss r f v =
    let res = f v in
    r := Some (v, res);
    res

val memo : r: ref (option (int*int)) -> f:(int -> int) -> v:int -> ST int  (requires (fun h_pre ->  sel h_pre r == None \/ (exists v1 c1. (sel h_pre r == Some(v1,c1)) /\ ( (v<>v1) \/ ((v==v1) /\ (c1 == f v))))))
 (ensures (fun h_pre q h_post -> (q == f v /\ (sel h_post r == Some(v,f v))))) 

let memo r f v =
  match !r with  
  | None -> cache_miss r f v
  | Some (v', r') -> 
      if v = v' then r'
  else  cache_miss r f v

(* Your definition should make the following function type check *)
let test () = 
  let foo v = v + 1 in
  let r = alloc None in
  let foo' = memo r foo in

  let r1 = foo 10 in
  let r2 = foo' 10 in
  assert (r1 == r2);

  let r3 = foo 10 in
  let r4 = foo' 10 in
  assert (r3 == r4);
  let r5 = foo 20 in
  let r6 = foo' 20 in
  assert (r5 == r6)
  

