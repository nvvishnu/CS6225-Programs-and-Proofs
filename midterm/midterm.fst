module Midterm

open FStar.List.Tot

(* In this module, we will describe and prove properties about vector clocks.
   For more information about vector clocks, see: https://en.wikipedia.org/wiki/Vector_clock.

	 You solution should not contain any [admit()] or equivalent. *)

(* The type of vector clock indexed by length *)
type t (n:nat) = lst:list nat{n > 0 && length lst = n}

type ordering =
| Happened_before
| Happened_after
| Concurrent
| Equal

val compare : v1:list nat -> v2:list nat{length v1 = length v2} -> ordering
let rec compare v1 v2 =
  match v1, v2 with
  | [], [] -> Equal
  | x::xs, y::ys ->
      if x = y then compare xs ys
      else if x < y then
        match compare xs ys with
        | Equal | Happened_before -> Happened_before
        | _ -> Concurrent
      else match compare xs ys with
           | Equal | Happened_after -> Happened_after
           | _ -> Concurrent

val hb: n:nat -> v1:t n -> v2:t n -> bool
let hb n a b = compare a b = Happened_before

val hbeq: n:nat -> v1:t n -> v2:t n -> bool
let hbeq n a b =
  match compare a b with
  | Happened_before | Equal -> true
  | _ -> false

val util_1: n:nat -> v:t n -> Lemma (ensures (compare v v = Equal)) (decreases (length v))
let rec util_1 n v = match v with
| [] -> ()
| h::[] -> ()
| h::t -> let x = n-1 in assert(compare v v = compare t t); assert(length t =x); util_1 x t
(* 5 points *)

val hbeq_reflexive : n:nat -> v:t n -> Lemma (ensures (hbeq n v v))
let hbeq_reflexive n v = util_1 n v

val util_2_1:  v1:list nat -> v2:list nat{length v2 = length v1 && compare v1 v2 = Equal} -> v3:list nat{length v3 = length v2 && compare v2 v3= Equal} -> Lemma (ensures(compare v1 v3 = Equal))
let rec util_2_1 v1 v2 v3 = match v1,v2,v3 with
| [],[],[] -> ()
| h1::t1,h2::t2,h3::t3 -> util_2_1 t1 t2 t3; ()

val util_2_2:  v1:list nat -> v2:list nat{length v2 = length v1 && compare v1 v2 = Equal} -> v3:list nat{length v3 = length v2 && compare v2 v3= Happened_before} -> Lemma (ensures(compare v1 v3 = Happened_before))
let rec util_2_2 v1 v2 v3 = match v1,v2,v3 with
| [],[],[] -> ()
| h1::t1,h2::t2,h3::t3 ->  match(compare t2 t3) with
  | Equal ->  util_2_1 t1 t2 t3
  | Happened_before -> util_2_2 t1 t2 t3

(*assert(h1=h2);match (h2=h3) with
  | true -> util_2_2 t1 t2 t3
  | false -> assert(h2<h3);match(compare t2 t3) with
  | Equal ->  util_2_1 t1 t2 t3
  | Happened_before -> util_2_2 t1 t2 t3*)

val util_2_3:  v1:list nat -> v2:list nat{length v2 = length v1 && compare v1 v2 = Happened_before} -> v3:list nat{length v3 = length v2 && compare v2 v3= Equal} -> Lemma (ensures(compare v1 v3 = Happened_before))
let rec util_2_3 v1 v2 v3 = match v1,v2,v3 with
| [],[],[] -> ()
| h1::t1,h2::t2,h3::t3 -> match(compare t1 t2) with
  | Equal ->  util_2_1 t1 t2 t3
  | Happened_before -> util_2_3 t1 t2 t3

(*assert(h2=h3);match (h1=h2) with
  | true -> util_2_3 t1 t2 t3
  | false -> assert(h1<h2);match(compare t1 t2) with
  | Equal ->  util_2_1 t1 t2 t3
  | Happened_before -> util_2_3 t1 t2 t3*)

 val util_2_4:  v1:list nat -> v2:list nat{length v2 = length v1 && compare v1 v2 = Happened_before} -> v3:list nat{length v3 = length v2 && compare v2 v3= Happened_before} -> Lemma (ensures(compare v1 v3 = Happened_before))
let rec util_2_4 v1 v2 v3 = match v1,v2,v3 with
| [],[],[] -> ()
| h1::t1,h2::t2,h3::t3 -> match(compare t1 t2), (compare t2 t3) with
  | Equal, Equal -> util_2_1 t1 t2 t3
  | Happened_before, Equal -> util_2_3 t1 t2 t3
  | Equal, Happened_before -> util_2_2 t1 t2 t3
  | Happened_before,Happened_before -> util_2_4 t1 t2 t3



(*match (h1=h2),(h2=h3) with
  | true, true -> util_2_4 t1 t2 t3
  | true, false -> (match(compare t2 t3) with
      | Equal ->  util_2_3 t1 t2 t3
      | Happened_before -> util_2_4 t1 t2 t3 
     )
  | false, true ->(match(compare t1 t2) with
      | Equal ->  util_2_2 t1 t2 t3
      | Happened_before -> util_2_4 t1 t2 t3 
     ) 
  | false, false -> ( match(compare t1 t2), (compare t2 t3) with
  | Equal, Equal -> util_2_1 t1 t2 t3
  | Happened_before, Equal -> util_2_3 t1 t2 t3
  | Equal, Happened_before -> util_2_2 t1 t2 t3
  | Happened_before,Happened_before -> util_2_4 t1 t2 t3
  )
*)




(*10 points *)
val hbeq_transitive : n:nat -> v1:t n -> v2:t n{hbeq n v1 v2} -> v3:t n{hbeq n v2 v3}
                    -> Lemma (ensures (hbeq n v1 v3))
let rec hbeq_transitive n v1 v2 v3 = match (compare v1 v2),(compare v2 v3) with
| Equal, Equal -> util_2_1 v1 v2 v3
| Equal, Happened_before -> util_2_2 v1 v2 v3
| Happened_before, Equal -> util_2_3 v1 v2 v3
| Happened_before, Happened_before -> util_2_4 v1 v2 v3

(*assert(length v1 = length v2); util_2_1 v1 v2 v3; util_2_2 v1 v2 v3; util_2_3 v1 v2 v3; util_2_4 v1 v2 v3*)

val concurrent : n:nat -> v1:t n -> v2:t n -> bool
let concurrent n v1 v2 = compare v1 v2 = Concurrent

(* 15 points *)
val eq_ref: v1:list nat -> v2:list nat{length v1= length v2} -> Lemma
  (requires(compare v1 v2 = Equal))
  (ensures(compare v2 v1 = Equal))
let rec eq_ref v1 v2 = match v1,v2 with
| [],[] -> ()
| h1::t1,h2::t2 -> (*assert(length t1 = length t2);*) eq_ref t1 t2

val util_3_1: v1:list nat -> v2:list nat {length v2 = length v1} -> 
Lemma 
  (requires(compare v1 v2=Happened_after)) 
  (ensures(compare v2 v1=Happened_before))
let rec util_3_1 v1 v2 = match v1,v2 with
 | [],[] -> ()
 | h1::t1,h2::t2 -> match (compare t1 t2) with
 | Equal -> assert(h2<h1); assert(compare t1 t2 = Equal);eq_ref t1 t2; assert(compare t2 t1 = Equal); ()
 | Happened_after-> util_3_1 t1 t2; ()

val util_3_2: v1:list nat -> v2:list nat {length v2 = length v1} -> 
Lemma 
  (requires(compare v1 v2=Happened_before)) 
  (ensures(compare v2 v1=Happened_after))
let rec util_3_2 v1 v2 =  match v1,v2 with
 | [],[] -> ()
 | h1::t1,h2::t2 -> match (compare t1 t2) with
 | Equal -> assert(h1<h2); assert(compare t1 t2 = Equal);eq_ref t1 t2; assert(compare t2 t1 = Equal); ()
 | Happened_before-> util_3_2 t1 t2; ()

val util_3: n:nat -> v1: list nat{length v1=n} -> v2:list nat
{length v2 = n && compare v1 v2 = Concurrent} -> Lemma(ensures(compare v2 v1= Concurrent))
let rec util_3 n v1 v2 = match v1,v2 with
| [], [] -> ()
| h1::t1,h2::t2 -> let x=n-1 in if(h1=h2) then util_3  x t1 t2
else if(h1<h2) then 
(
  match(compare t1 t2) with
  | Concurrent -> util_3 x t1 t2
  | Happened_after -> util_3_1 t1 t2; assert(compare v2 v1=Concurrent)
)
else 
(
match(compare t1 t2) with
  | Concurrent -> util_3 x t1 t2
  | Happened_before -> util_3_2 t1 t2
)

val concurrent_commutative : n:nat -> v1:t n -> v2:t n{concurrent n v1 v2}
                           -> Lemma (ensures (concurrent n v2 v1))
let rec concurrent_commutative n v1 v2 = util_3 n v1 v2
