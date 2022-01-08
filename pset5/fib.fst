module Fib

(** TODO (5 points): Prove that tail recursive fibonacci is equivalent to the
    non-tail recursive one. *)

val fib : nat -> Tot nat
let rec fib n =
  if n < 2 then 1 else fib (n-1) + fib (n-2)

val fib_tail_rec_util: (n:nat) -> (acc1:nat) -> (acc2:nat) -> Tot nat  (*)(decreases %[(n-i)])*)
let rec fib_tail_rec_util  n acc1 acc2 =
    if n=0 then acc1
    else fib_tail_rec_util (n-1) (acc2) (acc1+acc2)
val fib_tail_rec: nat ->Tot nat
let fib_tail_rec n = fib_tail_rec_util n 1 1



val fib_lemma: n:nat{n>=1} -> k:nat  -> Lemma (ensures (fib (k+n)=fib_tail_rec_util n (fib k) (fib (k+1))))
let rec fib_lemma n k = 
if(n=1) then ()
else let x = n-1 in let y = k+1 in assert((k+2)>=2); assert(fib (k+2) = fib k +fib (k+1)); fib_lemma x y

val fib_same : n:nat -> Lemma  (ensures (fib n = fib_tail_rec n))
let rec fib_same n =
  if n=0 then ()
 else fib_lemma n 0
(* Ignore the following:
val fib_same_dum : n:nat -> Lemma (ensures(fib 5=fib_tail_rec 5))
let fib_same_dum n = ()
*)

