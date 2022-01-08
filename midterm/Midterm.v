(** CS6225 Spring 2021: Programs and proofs -- Mid Term *)

(***************************************
 ** Instructions
 ***************************************

   This is a take home exam, with 48 hours for the exam. Strictly no late
   submissions allowed. Submit your solutions through course moodle.

   Completed solutions should not have any [Abort]ed proofs. If there are, they
   will get [0] points. There are a few lemmas and theorems for which the proof
   ends with [Admitted]. For example, see [fib_succ_add] and
   [fib_fib_tail_rec']. Those are the only ones for which you may leave the
   proof as admitted and use it in the subsequent theorems ([fib_ok] for
   example). Your solution will not have any other [Admitted] proofs. Any other
   use of [Admitted] proofs will get [0] points. *)

Require Import Frap MidtermSig.

(***************************************
 ** Swivel
 ***************************************)

Inductive tree :=
  | Leaf
  | Node (v : nat) (lt rt : tree).
  
Fixpoint rightmost (tr: tree) : option nat :=
  match tr with
  | Leaf => None
  | Node v _ rt =>
    match rt with
    | Leaf => Some v
    | _ => rightmost rt
    end
  end.
  
Fixpoint leftmost (tr : tree) : option nat :=  (* Remove [None] and fill in *)
  match tr with
  | Leaf => None
  | Node v lt _ =>
    match lt with
    | Leaf => Some v
    | _ => leftmost lt
    end
end.
(* 3 points *)
  
Fixpoint swivel tr :=
  match tr with
  | Leaf => Leaf
  | Node v lt rt => Node v (swivel rt) (swivel lt)
  end.
  
Theorem swivel_ok : forall tr, 
  leftmost tr = rightmost (swivel tr).
(* 5 points *)
Proof.
  simplify.
  induction tr.
   - simplify. equality.
   - simplify. induction tr1.
      + simplify. equality.
      + simplify. assumption.
Qed.

(***************************************
 ** Fibonacci Sequence
 ***************************************)

Fixpoint fib n :=
  match n with
  | 0 => 1
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n'' + fib n'
            end
  end.

Fixpoint fib_tail_rec' n a b :=
  match n with
  | 0 => a
  | S n' => fib_tail_rec' n' b (a+b)
  end.

Definition fib_tail_rec n := fib_tail_rec' n 1 1.
(* Remove [n + 0] and fill in correct definition *)
(* 2 points *)

Example ex1: fib 10 = 89.
Proof.
  auto.
Qed.

Example ex2: fib_tail_rec 10 = 89.
Proof.
  auto.
Qed.

Lemma fib_succ_add: forall n,
  fib n + fib (n+1) = fib(n+2).
(* 5 points *)
Proof.
  simplify.
  induction n.
  - simplify. equality.
  - replace (S n + 2) with (S(S (S n))) by linear_arithmetic. 
    replace (S n + 1) with (S (S n)) by linear_arithmetic.     
    simpl fib. equality.
Qed.   
    

Lemma fib_fib_tail_rec': forall n k,
  fib_tail_rec' n (fib k) (fib (k+1)) = fib (k+n).
(* 5 points *)
Proof.
  induction n.
  - simplify. f_equal. ring.
  - simplify. 
    replace (k + S n) with ((k+1)+n) by linear_arithmetic.
    rewrite <- (IHn (k+1)). rewrite -> fib_succ_add. f_equal. f_equal. linear_arithmetic.
  (* FILL IN *)
Qed.

Theorem fib_ok : forall n, fib n = fib_tail_rec n.
(* 5 points *)
Proof.
  simplify.
  induction n.
  - simplify. unfold fib_tail_rec. unfold fib_tail_rec'. equality.
  - unfold fib_tail_rec. 
    replace (S n) with (0 + S n) by linear_arithmetic.
    rewrite <- (fib_fib_tail_rec' (S n) 0). simplify. equality.
Qed.


(***************************************
 ** List.rev is involutive
 **************************************)

Require Import List.
Import ListNotations.


Lemma append_right: forall (A:Type) (l:list A), l ++ [] = l.
Proof.
  simplify.
  induction l.
  - simplify. equality.
  - simplify. rewrite IHl. equality.
Qed.

Lemma append_associative: forall (A:Type) (a b c: list A), (a ++ b) ++ c = a ++ (b ++ c).
Proof.
  simplify.
  induction a.
  - simplify. equality.
  - simplify. rewrite IHa. equality.
Qed.

Lemma rev_comm: forall (A:Type) (l1 l2:list A) , rev(l1++l2) = rev(l2) ++ rev(l1).
Proof.
  simplify. 
  induction l1.
  - simplify. rewrite append_right. equality.
  - simplify. rewrite IHl1. apply append_associative.
Qed.

Theorem rev_involutive : forall (A:Type) (l : list A), rev (rev l) = l.
(* 5 points *)
Proof.
   simplify.
   induction l.
    - simplify. equality.
    - simplify. rewrite rev_comm. simplify. rewrite IHl. equality.
Qed.


(***************************************
 ** n^2 insertion sort
 ***************************************
 
 
  We will define an n^2 insertion sort and prove it right. Consider the following idea. Given the input list l = [4;5;1;3], sorting proceeds like this:

  Using an auxilliary list [sorted]:

  l=[4;5;1;3] aux=[]
  l=[5;1;3]   aux=[4]
  l=[1;3]     aux=[4;5]
  l=[3]       aux=[1;4;5]
  l=[]        aux=[1;3;4;5]
  
  Observe that [aux] is always sorted. The idea is that, at each step, we take one element from [l] and insert into [aux] at the right position so that [aux] remains sorted. When [l] is empty, [aux] is the sorted version of the input list [l].
  
  In a typical insertion sort, you can do binary search on [aux] list and insert, leading to O(n log(n)) running time. We will just do a linear search through [aux] to find the correct position.

  We will use the comparison function [compare] that you have seen in assignment 5b. *)

Require Import OrdersFacts.

Check compare.
Print comparison.
Print OrdersFacts.

(* In order to prove facts, you will need the definitions from the following. *)

Include (OrderedTypeFacts MidtermSig).
Include (OrderedTypeTest MidtermSig).

(* Print OrderedTypeFacts. 
 Print OrderedTypeTest. *)

(* FYI, our solution only uses the following three facts, but you may use other 
   facts. *)

Check compare_gt_iff.
Check compare_lt_iff.
Check compare_eq_iff.

(* You will need to define a function [sort] that returns a sorted version of the input list based on the insertion sorting algorithm above: *)
  
Fixpoint sort_util_insert (e:t) (l1: list t) := match l1 with
| [] => [e]
| a::b => match compare e a  with
| Lt =>  [e]++[a]++b
| Eq =>  [e]++[a]++b
| Gt => [a]++sort_util_insert e b
end
end.

Fixpoint sort_util (l aux:list t) : list t:= match l with
| [] => aux
| h::t => sort_util t (sort_util_insert h aux)
end.
Fixpoint sort (l : list t) : list t := match l with
| [] => []
| h::t => sort_util_insert h (sort t)
end.
(* sort_util l []. *)
(* Remove [l] and fill in correct defintion. *)
(* 5 points *)

(* In order to do the proof, we will define an inductive type called [sorted] that captures that 
  (1) An empty list is sorted.
  (2) A singleton list is sorted.
  (3) Given a list [l = x::y::t], in order for [l] to be sorted, it better be the case that [lt x y \/ eq x y] and [sorted (y::t)].
  
Check the definition of [lt] and [eq] below:
*)

Check lt.
Check eq.

 (* FILL IN *)
(*Inductive SortedList : list nat -> Prop :=
| [] => True
| [x] => True
| x::(y::t) => (lt x y \/ eq x y) /\ (sorted (y::t))
*)
Inductive sorted: list t -> Prop :=
| null_sorted : sorted []
| singleton_sorted : forall a, sorted [a]
| sortcons : forall z1 z2, forall l, (lt z1 z2 \/ eq z1 z2) -> sorted (z2 :: l) -> sorted (z1 :: z2 :: l).
(* 5 points *)

(* Prove the following theorem: the result of the [sort] function returns a [sorted] list. *)

Lemma sort_ok_util: forall h l, sorted(l) -> sorted(sort_util_insert h l).
Proof.
intros.
simplify.
(*invert H.
- simplify. apply singleton_sorted.
- simplify. cases(compare h a).
  + apply sortcons. right. apply compare_eq_iff. assumption. apply singleton_sorted.
  + apply sortcons. left. apply compare_lt_iff. assumption. apply singleton_sorted.
  + apply sortcons. left. apply compare_gt_iff. assumption. apply singleton_sorted.*)
induction l.
  - simplify. apply singleton_sorted.
  - simplify. cases(compare h a).
      * apply sortcons. right. apply compare_eq_iff. assumption. assumption.
      * apply sortcons. left. apply compare_lt_iff. assumption. assumption. 
      * cases l.
        -- simplify. apply sortcons. left. apply compare_gt_iff. assumption. apply singleton_sorted.
        -- simplify. cases(compare h t).
              ++ apply sortcons. left. apply compare_gt_iff. assumption. apply sortcons. right. apply compare_eq_iff. assumption. invert H. assumption.
              ++ apply sortcons. left. apply compare_gt_iff. assumption. apply sortcons. left. apply compare_lt_iff. assumption. invert H. assumption.
              ++ apply sortcons. invert H. assumption. apply IHl. invert H. assumption.
Qed.

Theorem sort_ok : forall l, sorted (sort l).
(* 10 points *)
Proof.
  simplify.
  induction l.
  - simplify. propositional. unfold sort. simplify. apply null_sorted.
  - simpl sort. apply (sort_ok_util a (sort l)). assumption.
Qed.

(* Of course, one also needs to prove that the sorted list is a permutation of the original list. Perhaps you can try that in your own time :-) *)