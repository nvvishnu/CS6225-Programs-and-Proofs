(**
* PSet2b: Induction in Coq (240 points)
*)

Require Import List Arith.

(**********************************************************************)

(* Exercise: app_assoc coq [10 points].
   In Coq, the list append operator is written [++]. Complete the following
   proof by induction, which shows that application is associative.
   Hint:  the solution is in the lecture slides. *)

Theorem app_assoc : forall (A:Type) (l1 l2 l3 : list A),
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
  intros A l1 l2 l3.
  induction l1 as [ | h t IH].
  - simpl. trivial.
  - simpl. rewrite -> IH. trivial.
Qed.

(**********************************************************************)

(* Exercise: app_assoc math [20 points].

Prove that the OCaml [@] operator is also associative.  Your answer should
be a mathematical proof, not a Coq proof.  We have supplied part of the
proof for you.

Theorem:  for all lists lst1, lst2, and lst3,
  lst1 @ (lst2 @ lst3) = (lst1 @ lst2) @ lst3.

Proof:  by induction on lst1.
The property being proved is:
P(l) =  lst1 @ (lst2 @ lst3) = (lst1 @ lst2) @ lst3, where lst1 is a list of length l.

Case:  lst1 = [] (Base case - l=0 )
To Show: [] @ (lst2 @ lst3) = ([] @ lst2) @ lst3.
Proof: 
  By the definition of append function, [] @ lst2 = lst2.
  Thus, we need to prove, 
  (lst2 @ lst3) = (lst2) @ (lst3) which is true trivially(They are the same terms).

Case: lst1 = h::t, lst1 is a list of length l.
IH:  t@(lst2 @ lst3) = (t @ lst2) @lst3( t is a list of length l).
To Show:  (h::t)@(lst2 @ lst3) = ((h::t)@ lst2) @lst3
Proof: 
  By the definition of append funciton, (h::t) @lst2 = h::(t @ lst2).
  Thus, we need to prove,
    h::(t @ (lst2 @ lst3)) = (h:: (t @ lst2)) @ lst3
  Applying (h::t) @lst2 = h::(t @ lst2) again to the right hand side(where t is (t @ lst2) in this case),
  we need to prove,
    h::(t @ (lst2 @ lst3)) = h::( (t @ lst2) @ lst3)
  Rewriting the L.H.S using the Induction Hypothesis(IH),we get that it suffices to prove:
    h::((t @ lst2) @ lst3 ) = h::((t @ lst2) @ lst3)
which is true trivially (Same term).

Thus, by the principle of induction, p(l)=lst1 @ (lst2 @ lst3) = (lst1 @ lst2) @ lst3, where lst1 is a list of length l
is true for all l.

Thus, lst1 @ (lst2 @ lst3) = (lst1 @ lst2) @ lst3 is true for all lists lst1,lst2,lst3


QED

*)

(**********************************************************************)

(* Exercise: rev_append math [30 points].

Prove the following theorem, which shows how list reversal distributes
over list append.

Theorem: for all lists lst1 and lst2,
  rev (lst1 @ lst2) = rev lst2 @ rev lst1.

Recall that [rev] is defined as follows:
<<
let rec rev = function
  | [] -> []
  | h::t -> rev t @ [h]
>>

Your answer should be a mathematical proof, not a Coq proof. In the inductive
case, you will need the lemma proved above saying that append is associative. In
the base case, you will need this lemma:

Lemma:  for all lists lst, lst @ [] = lst. [Lemma 1]
Proof:  given in lecture.

Here, again, is the theorem you should prove:

Theorem: for all lists lst1 and lst2,
  rev (lst1 @ lst2) = rev lst2 @ rev lst1.

Proof:  by induction on lst1.
The property being proved is:
P(l) =  rev(lst1 @ lst2) = rev (lst2) @ rev (lst1), where lst1 is a list of length l.

Case:  lst1 = [] (Base case - l=0 )
To Show: rev([] @ lst2) = rev (lst2) @ rev ([])
Proof: 
  By the definition of append function, [] @ lst2= lst2.
  By definition of rev function, rev ([]) = [] 
  Thus, we need to prove, 
    rev(lst2) = rev (lst2) @ []
  Using Lemma 1(for all lists lst, lst @ [] = lst),
  we need to prove
    rev(lst2) = rev(lst2) which is trivally true.

Case: lst1 = h::t, lst1 is a list of length l.
IH:  rev(t @ lst2) = rev (lst2) @ rev (t), t is a list of length l).
To Show:  
  rev( (h::t) @ lst2) = rev (lst2) @ rev (h::t)
  Using the definition of append, (h::t) @ lst2 = h::(t @ lst2). We need to prove,
    rev(h::(t @ lst2)) = rev (lst2) @ rev (h::t)
  Using the definition of rev, rev(h::t) = rev(t) @ [h]. We need to prove,
    rev(t @ lst2) @ [h] = rev (lst2) @ (rev (t) @ [h])
  Using the induction hypothesis(IH), it suffices to prove:
   ( rev(lst2) @ rev (t)) @ [h] = rev (lst2) @ (rev(t) @ [h])
  This is true from the associativity of list append with lst1 = rev(lst2), lst2 = rev(t), lst3 = [h].

Thus, from principal of induction, rev(lst1 @ lst2) = rev (lst2) @ rev (lst1), where lst1 is a list of length l,is true for all l.
Hence, rev(lst1 @ lst2) = rev (lst2) @ rev (lst1) for all lists lst1 and lst2  

*)

(**********************************************************************)

(* Exercise: rev_append coq [30 points].

Now prove the same theorem as the previous exercise, but in Coq.
The Coq list reversal function [rev] is defined in the standard
library for you.  Use the mathematical proof you gave above
as a guide.  For the base case, you will need the lemma [app_nil]
that we proved in lecture; we've inserted the code for it below.
You can use that lemma in your own proof with the [rewrite] tactic.
*)

Lemma app_nil : forall (A:Type) (lst : list A),
  lst ++ nil = lst.
Proof.
  intros A lst.
  induction lst as [ | h t IH].
  - trivial.
  - simpl. rewrite -> IH. trivial.
Qed.

Theorem rev_append : forall (A:Type) (lst1 lst2 : list A),
  rev (lst1 ++ lst2) = rev lst2 ++ rev lst1.
Proof.
  intros a lst1 lst2.
  induction lst1.
  - simpl. rewrite -> app_nil. trivial.
  - simpl. rewrite -> IHlst1. rewrite -> app_assoc. trivial.
Qed.

(**********************************************************************)

(* Exercise: rev involutive [30 points].

Prove that [rev] is _involutive_, meaning that it is its own inverse. That is,
[rev (rev lst) = lst].

Hint:  for the inductive case, there is a lemma that has already been proved in
this lab that you will find very helpful.  Part of this exercise is figuring out
which lemmma that is.
*)

Theorem rev_involutive : forall (A:Type) (lst : list A),
  rev (rev lst) = lst.
Proof.
  intros a lst.
  induction lst.
    - simpl. trivial.
    - simpl. rewrite -> rev_append. simpl. rewrite -> IHlst. trivial.
Qed.

(**********************************************************************)

(* Exercise: app_length [Optional].
Prove the following theorem in Coq.
*)


Theorem app_length : forall (A:Type) (l1 l2 : list A),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros a l1 l2.
  induction l1.
    - simpl. trivial.
    - simpl. rewrite -> IHl1. trivial.  
Qed.


(**********************************************************************)

(* Exercise: rev_length [Optional].
Prove the following theorem in Coq.

Hint: previous exercise(s) as lemma, and the [ring] tactic.
*)


Theorem app_rev : forall (A:Type) (lst : list A),
  length (rev lst) = length lst.
Proof.
  intros a lst.
  induction lst.
    - simpl. trivial.
    - simpl. rewrite -> app_length. rewrite -> IHlst. simpl. ring.
Qed.

(**********************************************************************)

(* INDUCTION ON BINARY TREES *)

(* Here is a Coq type for binary trees: *)
Inductive tree (A : Type) : Type :=
  | Leaf : tree A
  | Node : tree A -> A -> tree A -> tree A.

(* The following commands cause the [A] argument to
   be implicit to the [Leaf] and [Node] constructors. *)
   Arguments Leaf [A].
   Arguments Node [A] _ _ _.

(* The equivalent OCaml type would be:
<<
type 'a tree =
  | Leaf
  | Node of 'a tree * 'a * 'a tree
>>
*)

(* The _reflection_ operation swaps the left and right
   subtrees at every node. *)
Fixpoint reflect {A : Type} (t : tree A) :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (reflect r) v (reflect l)
  end.

(* The equivalent OCaml function would be:
<<
let rec reflect = function
  | Leaf -> Leaf
  | Node (l,v,r) -> Node (reflect r, v, reflect l)
>>
*)

(* A proof by induction on a binary tree has the following structure:

Theorem:  For all binary trees t, P(t).

Proof: by induction on t.

Case: t = Leaf
Show: P(Leaf)

Case: t = Node(l,v,r)
IH1:  P(l)
IH2:  P(r)
Show:  P(Node(l,v,r))

QED

Note that we get _two_ inductive hypotheses in the inductive
case, one for each subtree.
*)

(**********************************************************************)

(* Exercise: tree_ind [20 points].
Explain the output of the following command in your own words, relating it to
the proof structure given above for induction on binary trees.
Hint: read the notes on induction principles.
*)

Check tree_ind.

(*
  Explanation of the output: 
    Consider A is a type and P is a Proposition on a tree of type tree A.
     Given that 
      1. Proposition P is true for a  Leaf (tree which is just a Leaf).
      2. Given that P is true for all trees t (of type tree A) and for all trees t0(of type tree A) 
        implies that, P is true for (Node t a t0) where a is any value of type A.
    implies that
        P is true for all trees of type tree A.

  This is the induction structure for hypothesis on type tree A.
  This can be proved to prove theorems on trees of type tree A.
*)
(**********************************************************************)

(* Exercise: reflect_involutive math [30 points].
Prove the following theorem mathematically (not in Coq).

Theorem:  for all trees t, reflect (reflect t) = t

Proof: by induction on t.
P(t) = reflect (reflect t) = t

Case: t = Leaf
To Show: reflect(reflect Leaf) = Leaf
Proof: 
  By the definition of reflect, we need to prove:
    reflect(leaf) = leaf ( as reflect(Leaf) = Leaf from the definition of reflect)
  This is the true from the definition of reflect

Case: t = Node(l,v,r)
IH1: P(l) = reflect(reflect l) = l
IH2: P(r) = reflect(reflect r) = r
To Show: reflect(reflect(Node(l,v,r))) = Node(l,v,r)
Proof:
  By the definition of reflect, it suffices to prove:
    reflect( Node(reflect r, v, reflect l)) = Node(l,v,r) { Using reflect(Node l v r)= Node (reflect r) v (reflect l) }
  Again using the defintion of reflect, we need to prove:
    Node(reflect(reflect l), v, reflect(reflect(r)) = Node(l,v,r) 
  Now, it suffices to prove,
    Node(l,v,r) = Node(l,v,r) {Using IH1 (reflect(reflect l) = l) and IH2 (reflect(reflect r) = r)).
  This trivially true.

Thus, by the principle of induction(as in tree_ind), reflect(reflect t) = t is true for all trees t.   

QED
*)

(**********************************************************************)

(* Exercise: reflect_involutive coq [30 points].
State and prove a theorem in Coq that shows reflect is involutive.
Use your mathematical proof from the previous exercise as a guide.

Hint: the [induction] tactic expects the arguments for the inductive
case in the following order:  the left subtree, the IH for the left subtree,
the value at the node, the right subtree, and the IH for the right subtree.
*)

Theorem reflect_involutive : forall (A:Type) (t:tree A), reflect(reflect t)=t.
Proof.
  intros a t.
  induction t.
    - simpl. trivial.
    - simpl. rewrite -> IHt1. rewrite -> IHt2. trivial.
Qed.

(**********************************************************************)

(* Exercise: height [40 points].

1. Write a Coq function [height] that computes the height of a binary tree.
Recall that the height of a leaf is 0, and the height of a node is 1 more than
the maximum of the heights of its two subtrees.  The standard library does
contain a [max] function that will be helpful. *)

Fixpoint height {A:Type} (t:tree A) :nat :=   
match t with
| Leaf => 0 
| Node l v r => 1 + max (height l) (height r)
end.


(*
2. Prove that [reflect] preserves the height of a tree.  Hint: [Nat.max_comm].
*)
Theorem ref_height:forall (A:Type) (t:tree A), height(reflect(t)) = height(t).
Proof.
  intros A t.
  induction t.
 - simpl. trivial.
 - simpl. rewrite <- IHt1. rewrite <- IHt2. rewrite -> Nat.max_comm. trivial.
Qed.

(*
3. Write a Coq function [perfect : nat -> tree nat], such that
[perfect h] constructs the perfect binary tree of height [h], and
the value at the root is [1], and if the value at a node is [v],
then the values of its left and right subnodes are [2*v] and [2*v+1].
For example, [perfect 3] is
<<
Node (Node (Node Leaf 4 Leaf) 
           2 
           (Node Leaf 5 Leaf)) 
     1
     (Node (Node Leaf 6 Leaf) 
           3 
           (Node Leaf 7 Leaf))
>>
*)
Fixpoint cons_perf (h:nat) (v:nat) :tree nat := 
match h with 
| 0 => Leaf
| S p => Node (cons_perf p (2*v)) v (cons_perf p (2*v+1))
end.
Definition perfect (h:nat) := cons_perf h 1.

(* Compute (perfect 3) *)
(* Prints the desired output as per the example. *)


(* 
  4. Prove that the height of [perfect h] is in fact [h].  
  Hint 1: induct on [h].  
  Hint 2: don't introduce all the variables. 
  Hint 3: [Nat.max_idempotent].
*)

Lemma cons_pref_height: forall (h:nat) (v:nat), height(cons_perf h v) =  h.
Proof.
    intro h.
    induction h.
      - intro v. simpl. trivial.
      - intro v. simpl. rewrite (IHh (v+(v+0))). rewrite (IHh (v+(v+0)+1)). rewrite -> Nat.max_idempotent. trivial.
Qed.  

(* 
  I am using the lemma: "height(cons_perf h v) =  h forall h and v" proved above as a helper in the following proof.
*)
Theorem perfect_height: forall (h:nat), height(perfect h) = h.
Proof.
  intro h.
  unfold perfect.
  apply (cons_pref_height h 1).
Qed.



