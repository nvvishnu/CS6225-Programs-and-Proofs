(**
* PSet 2a : Logic in Coq [360 points]
*)

(* Exercise: types [10 points].
Using [Definition], define a value of each of the following types:
- [nat]
- [Set]
- [0 * 1 = 0]  (* hint: [eq_refl] *)
- [Prop]
- [Type]
*)

Definition t1 : nat := 0 (* FILL IN *).
(*
  Check t1. 
  Output: nat
*)
Definition t2 : Set := bool(* FILL IN *).
(*
  Check t2.
  Output: Set
*)
Definition t3 : 0*1 = 0 := eq_refl 0 (* FILL IN *).
(*
  Check t3.
  Output: 0 * 1 = 0
*)
Definition t4 : Prop := False(* FILL IN *).
(*
  Check t4.
  Output: Prop
*)
Definition t5 : Type := Prop(* FILL IN *).
(*
  Check t5.
  Output: Type
*)

(* Exercise: implication [20 points].
Prove the following theorems.  State English intuition before starting the Coq
proof.  When you're done with the Coq proof, revisit the intuition and see
whether you still agree with it; revise if necessary.
Hint: intros, apply, and/or assumption.
*)

Theorem imp1 : forall P Q : Prop,
  P -> (Q -> P).
(* 
  Intuition:
    To prove P -> (Q->P) for all P and Q,
      1. We will take arbitary P and Q //intros p q helps achieve this.
      2. Assume P is true and then prove Q->P // intros p_proof is used for this.
      3. To prove Q->P, we will assume Q is also true and then prove P. // intros q_proof helps with this.
      4. We already have P is true as an assumption and hence, the proof is complete. // assumption performs this.
*)
Proof.
  intros p q.
  intros p_proof.
  intros q_proof.
  assumption.
Qed.

Theorem imp2 : forall P Q R : Prop,
  (P -> (Q -> R)) -> (Q -> (P -> R)).
(* 
  Intuition:
    1. Assume arbitary P,Q,R. // intros p q r.
    2. Consider (P->(Q->R)) is true and try to prove Q->(P->R). // intros p_q_r
    3. Consider Q to be true and try to prove P->R  //intros q_proof
    4. Assume P to be true and try to prove R. //intros p_proof
    5. Given P is true, Q->R is true from p_q_r and given Q is also true, R is true as we know Q->R is true.
    //apply p_q_r makes it sufficient to prove P and Q to prove R. And P and Q are true from assumptions.
  This completes our proof.  
*)
Proof.
  intros p q r.
  intros p_q_r.
  intros q_proof.
  intros p_proof.
  apply p_q_r.
  assumption.
  assumption.
Qed.


(* Exercise: implication program [20 points].
Look at the printed value of the following theorem. Explain in your own words
the functional program you see, as if you were writing English intuition for the
theorem.
*)

Theorem imp3 : forall P Q R : Prop,
  ((P -> Q) -> (P -> R)) -> (P -> (Q -> R)).
Proof.
  intros P Q R evPQPR evP evQ.
  apply evPQPR.
  - intros evPagain. assumption.
  - assumption.
Qed.

Print imp3.


(* 
  Intuition: To prove imp3, we need to prove R is true assuming that (P -> Q) -> (P-> R) ,P,Q are true.
  evPQPR is a value of type of (P -> Q) -> (P -> R) which is the proof for the same.
  evP is proof for P and evQ is proof for Q(They are values of that type).
    
  Use P and Q are true to obtain P -> Q is true and apply this on (P -> Q) -> (P-> R) to obtain that (P->R) is true.
  Apply P on (P->R) to obtain R.  
  The body of the functional program consists of these applications.  
*)

(* Exercise: conjunction [20 points].
Prove the following theorems.  State English intuition before starting the Coq
proof.
Hint: intros, apply, split, destruct, and/or assumption.
*)

Theorem conj1 : forall P Q : Prop,
  P -> (Q -> (P /\ Q)).
(* 
  Intuition:  
  1. Introduce arbitary p and q. //intros p q
  2. Assume P to be true and try to prove Q->(P /\ Q). //intros p_proof.
  3. Assume Q to be true and try to prove (P /\ Q). //intros q_proof.
  4. Each part of the conjunction is true from the assumptions. 
  // split splits the conjunction into two goals each of which are true from the assumption.
*)
Proof.
  intros p q.
  intros p_proof.
  intros q_proof.
  split.
  all: assumption.
Qed.

Theorem conj2 : forall P Q R : Prop,
  (P -> (Q -> R)) -> ((P /\ Q) -> R).
(* 
  Intuition:
  1. Consider arbitary p,q and r. // intros p q r.
  2. Consider P -> (Q -> R) is true and try to prove ((P /\ Q) -> R) // intros p_q_r.
  3. Assume (P /\ Q) to be true and try to prove R. //intros p_and_q.
  4. Apply the fact that P and Q are true (obtained by destructing p_and_q) // destruct p_and_q
    to P->(Q->R) to prove R.
  //apply p_q_r makes it sufficient to prove P and Q to prove that R is true. 
  P and Q are true follows from assumption.  
*)
Proof.
  intros p q r.
  intros p_q_r.
  intros p_and_q.
  destruct p_and_q.
  apply p_q_r.
  all: assumption.
Qed.

(* Exercise: conjunction associative [20 points].
Prove the following theorem. *)

Theorem conj3 : forall P Q R : Prop,
  (P /\ (Q /\ R)) -> ((P /\ Q) /\ R).
(* 
  Intuition: 
  We will skip the obvious parts like intros and be bit more brief about the intuition from now on.
    1.Assume (P /\ (Q /\ R)) is true.
    2.Destruct the disjunctions to obtain that each of P,Q and R are true
    3.Split the goal so that it suffices to prove each of P,Q and R are true, all of which follows from assumptions.
*)
Proof.
  intros p q r.
  intros p_q_r.
  destruct p_q_r as [H1 H0].
  destruct H0.
  split.
  split.
  all:assumption.
Qed.

(* Print conj3. *)

(* 
  Exercise: direct proof conjunction associative [20 points].
  The following definition gives a program that directly proves that conjunction
  is associative.  (And it's likely though not certain that it's the same program
  you produced in the previous exercise using tactics.)  Rewrite the program so
  that it still proves the theorem, but doesn't use a nested pattern match.
  Hint: deep pattern matching with conj.
*)

Definition direct_conj3 (P Q R : Prop) (evP_QR : P /\ Q /\ R)
  : (P /\ Q) /\ R
:=
match evP_QR with
| conj evP evQR =>
  match evQR with
  | conj evQ evR => conj (conj evP evQ) evR
  end
end.

Definition direct_conj3' (P Q R : Prop) (evP_QR : P /\ Q /\ R)
  : (P /\ Q) /\ R
:=
match evP_QR with
| conj evP (conj evQ evR) => conj (conj evP evQ) evR
end.

(* 
Exercise: disjunction [20 points].
Prove the following theorems.  State English intuition before starting the Coq
proof.
Hint: intros, left, right, apply, split, destruct, and/or assumption.
*)

Theorem disj1 : forall P : Prop,
  P -> P \/ P.
(* 
  Intuition:
    1. Assume P is true.
    2. To prove P \/ P is true, it suffices to prove the left part of the disjunction(P) to be true. 
    3. The fact P is true is clear from the assumption.

*)
Proof.
  intro p.
  intro p_proof.
  left.
  assumption.
Qed.

(* give a different proof, resulting in a different program,
   than the one you gave for [disj1]. *)
Theorem disj1' : forall P : Prop,
  P -> P \/ P.
(* 
  Intuition:
    1. Assume P is true.  
    2. To prove P \/ P is true, we can prove either the left part of disjunction or the right part.
      Last time, we proved the left part. This time, we will prove the right part(P).
    3. P is true is an assumption itself.
  This completes the proof.
  
*)
Proof.
  intro p.
  intro p_proof.
  right. 
  assumption.
Qed.
 
(*
  Print disj1.
  Print disj1'.
  The above two proofs results in different programs.(or_intror and or_introl)
*)

Theorem disj2 : forall P : Prop,
  P \/ P -> P.
(* 
  Intuition: 
    1. Consider the two cases of P \/ P.
      a) P is true: The goal P is true from assumption.
      b) P is true: The goal P is true from assumption.
*)
Proof.
  intro p.
  intros p_or_p.
  destruct p_or_p.
  - assumption.
  - assumption.  
Qed.

Theorem disj3 : forall P Q R : Prop,
  (P -> R) -> (Q -> R) -> (P \/ Q -> R).
(* 
  Intuition:
    1.  Assume (P -> R),(Q -> R) and P \/ Q are true. Now, we need to prove R is true.
    2. Consider the two cases of P \/ Q
      a) P is true: R is true using (P->R) and that P is true. 
      b) Q is true: Q is true and (Q->R) implies R is true.

*)
Proof.
  intros p q r.
  intros p_imply_r q_imply_r p_or_q.
  destruct p_or_q.
  - apply p_imply_r. assumption.
  - apply q_imply_r. assumption.  
Qed.

(* 
Exercise: and distributes over or [30 points].
In the notes we prove that \/ distributes over /\.  Now state and
prove a theorem that shows /\ distributes over \/.
*)

Theorem and_distr_or : forall P Q R,
  P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
(* 
  Intuition: 
    1. Obtain P and (Q \/ R) are true by assuming (P /\ (Q \/ R)) is true and destructing it.
    2. Consider the two cases of Q \/ R
      a) Q is true: P is true and Q is true(from assumptions). This implies (P /\ Q) is true which is the left side of the disjunctive goal.
      b) R is true: P is true and R is true(from assumptions). This implies (P /\ R) is true which is the right side of the disjunctive goal.

*)
Proof.
  intros p q r.
  intro p_and_q_or_r.
  destruct p_and_q_or_r as [p_proof q_or_r].
  destruct q_or_r.
  - left. split; assumption.
  - right. split; assumption. 
Qed.

(* 
  Exercise: true and false [20 points].
  Prove the following theorems. The second uses a new connective,
  [P <-> Q], which means [(P -> Q) /\ (Q -> P)], i.e., "if and only if" or
  "iff".
  Hint: intros, left/right, exact, split, assumption, apply, destruct.
  You also might find [unfold iff] helpful. 
 *)

Theorem tf1 : True \/ False.
(* 
  Intuition: 
  For proving true or false, it suffices to prove true. // left reduces the goal from true or false to true.
  We know that true is true(I is a value with type true). Thus, our goal is proved. // exact I uses I which is a Prop of type true
  indicating that true is true  
*)
Proof.
  left. exact I.
Qed.
(* Check I. *)
Locate "<->".
Print iff.

Theorem tf2 : forall P : Prop,
  P <-> (True <-> P).
(* 
  Intuition: 
    1. Split the goal(iff) into two subgoals: if and only if
      a) Proving p -> True <-> p:
         i) Assume p is true and split iff into if and only if.
                A) To prove True->p, assume True and p is true follows from assumption.
                B) To prove p->True, assumpe p is true and use I to prove true.
        
      b) Proving True <-> p -> p:
           i) Assume True <-> p is true and apply it so that it suffices to prove True( p is true follows from it).
           ii) Use exact I to prove True.          
*)
Proof.
  intro p.
  split.
  - intro p_proof. split;intro. assumption. exact I.
  - intro. apply H. exact I.
  
Qed.

Print False.
(* Exercise: negation [20 points].  *)

Theorem neg1 : forall P : Prop,
  P /\ ~P -> False.
(* 
  Intuition:
  1. Assume P and ~P are true.
  2. This is a contradiction which can be used to prove anything and thus False will be true in this case. 
*)
Proof.
  intros p p_and_negp.
  destruct p_and_negp.
  contradiction.    
Qed.

Print not.

(* This theorem is known as reasoning by _contrapositive_ *)
Theorem neg2 : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
(* 
  Intuition:
   1. Assume P-> Q and ~Q.
   2. Expand the definition of not and assume P is true. Now, it suffices to prove False.
   3. Use P is true and (P->Q) is true to obtain Q is true.
   4. Now, we have Q and ~Q are true which is a contradiction and can be used to prove False.

*)  
Proof.
  intros p q p_imply_q notq.
  unfold not.
  intro p_proof.
  apply p_imply_q in p_proof.
  contradiction.  
Qed.

(* Exercise: de Morgan [30 points].  *)

(* This theorem is the "backwards" direction of DeMorgan2 from the
   notes, and this direction is actually provable in constructive logic. *)
Theorem neg3 : forall P Q : Prop,
  ~P \/ ~Q -> ~(P /\ Q).
(* 
  Intuition:
  1. Consider arbitary p,q  // intros p,q.
  2. Assume ~P \/ ~Q can consider the two cases.
    a) ~P is true: Expand the definition of not and assume P /\ Q is true. Destruct P /\ Q to obtain that each of P and Q are true
      Each of ~P and P are true which is a contradiction.
    b) ~Q is true: Expand the definition of not and assume P /\ Q is true. Destruct P /\ Q to obtain that each of P and Q are true
      Each of ~Q and Q are true which is a contradiction.
*)
Proof.
  intros p q notp_or_notq.
  destruct notp_or_notq.
  - unfold not. intro p_and_q. destruct p_and_q. contradiction.
  - unfold not. intro p_and_q. destruct p_and_q. contradiction.
Qed.


(* Exercise: double negation of excluded middle [30 points].
Hint: go right, then go left. *)

Theorem deMorgan : forall P Q : Prop,
  ~(P \/ Q) -> ~P /\ ~Q.
   
Proof.
  unfold not.
  intros P Q PorQ_imp_false.
  split.
  - intros P_holds. apply PorQ_imp_false. left. assumption.
  - intros Q_holds. apply PorQ_imp_false. right. assumption.
Qed.


Theorem dbl_neg_ex_middle : forall P : Prop,
  ~~(P \/ ~P).
(* 
  Intuition:    
  1. Assume ~(P \/ ~P) and try to prove False.
  2. Apply deMorgan's law to obtain (~P) \/ (~~P) and use contradiction to prove False.
  
*)
Proof.
  intros p.
  intro ass1.
  apply deMorgan in ass1.
  destruct ass1.
  contradiction.
Qed.

(* Exercise: xor [40 points].
Define your own inductive type for exclusive or.
Prove that [P] xor [Q] holds iff [(P \/ Q) /\ (~P \/ ~Q)] holds.

Hints:
- The [left] and [right] tactics will work on any inductive type
  with two constructors.
- You will likely need a new tactic [inversion], which is like
  [destruct] except that it will also remember the original
  formula you are destructing, keeping that formula as part of the
  assumptions.
*)

Print or.
Print and.
Check conj.
Inductive xor (P:Prop) (Q:Prop) : Prop := 
| xor1 : P -> ~Q -> xor P Q
| xor2 : ~P -> Q -> xor P Q. 

Print xor.
Theorem xor_impl: forall P Q: Prop, xor P Q <-> (P \/ Q) /\ (~P \/ ~Q). 
Proof.
  intros p q.
  split.
    - intro p_xor_q. destruct p_xor_q.
          + split.
            * left. assumption.
            * right. assumption.
          + split.
            * right. assumption.
            * left. assumption.
    - intro a. destruct a. destruct H.
      + destruct H0.
          * contradiction.
          * apply xor1. assumption. assumption.
      + destruct H0. 
        * apply xor2. assumption. assumption.
        * contradiction.       
Qed.
  


(**
 * Proofs are Programs [60 points].
 *)

(*
For the following prove them by directly writing down the Coq program that is
the proof, rather than using tactics to help construct the proof.
  (A -> B) -> ((B -> C) -> (A -> C))
  A -> (A \/ B)
  B -> (A \/ B)
  (A -> C) -> ((B -> C) -> ((A \/ B) -> C))
  A /\ B -> A
  A /\ B -> B
  (C -> A) -> ((C -> B) -> (C -> (A /\ B)))
  (A -> (B -> C)) -> ((A /\ B) -> C)
  ((A /\ B) -> C) -> (A -> (B -> C))
  (A /\ ~A) -> B
  (A -> (A /\ ~A)) -> ~A
  A -> (A -> B) -> B

Here's an example of what we mean, using the first proposition
from above:
*)

(* (A -> B) -> ((B -> C) -> (A -> C)) *)
Definition example : forall A B C : Prop,
  (A -> B) -> ((B -> C) -> (A -> C))
:=
  fun (A B C : Prop) (ab : A -> B) (bc : B -> C) (a : A) =>
    bc (ab a).

Print example.
(* A -> (A \/ B) *)
Definition prob1: forall A B: Prop, A -> (A \/ B) :=
   fun (A B : Prop) (a:A) => or_introl a. 

(* Print prob1. *)

(* B -> (A \/ B) *)
Definition prob2: forall A B: Prop, B -> (A \/ B) :=
   fun (A B : Prop) (b:B) => or_intror b.

(* Print prob2.*)

(* (A -> C) -> ((B -> C) -> ((A \/ B) -> C)) *)

Definition prob3: forall A B C:Prop,(A -> C) -> ((B -> C) -> ((A \/ B) -> C)) :=
fun (A B C: Prop) (ac: A->C)   (bc: B->C) (aorb: A \/ B) => match aorb with
|or_introl a => ac a
|or_intror b => bc b
end.

(* Print prob3. *)

(* A /\ B -> A *)
Definition prob4: forall A B: Prop, A /\ B -> A := 
fun (A B: Prop) (a_and_b: A /\ B) => match a_and_b
with conj a b => a
end.

(* Print prob4. *)

(* A /\ B -> B *)

Definition prob5: forall A B: Prop, A /\ B -> B := 
fun (A B: Prop) (a_and_b: A /\ B) => match a_and_b
with conj a b => b
end.

(* Print prob5. *)
(* (C -> A) -> ((C -> B) -> (C -> (A /\ B))) *)

Definition prob6: forall A B C: Prop, (C -> A) -> ((C -> B) -> (C -> (A /\ B))) :=
fun (A B C: Prop) (ca: C->A) (cb:C->B) (c:C) =>
conj (ca c) (cb c).

(* Print prob6. *)

(*   (A -> (B -> C)) -> ((A /\ B) -> C) *)
Definition prob7: forall A B C: Prop, (A -> (B -> C)) -> ((A /\ B) -> C) :=
fun (A B C: Prop) (abc: A->(B->C)) (a_and_b: A/\B)  => match a_and_b with conj a b => abc a b end.

(* Print prob7. *)



(*  ((A /\ B) -> C) -> (A -> (B -> C)) *)
Definition prob8: forall A B C: Prop, ((A /\ B) -> C) -> (A -> (B -> C)) :=
fun (A B C:Prop) (a_and_b_c:(A /\ B) -> C) (a:A) (b:B) =>
a_and_b_c (conj a b).

(* Print prob8. *)

(*  (A /\ ~A) -> B *)
Definition prob9: forall A B: Prop, (A /\ ~A) -> B :=
fun (A B: Prop) (a_and_nega: A /\ ~A) => match a_and_nega with
| conj a nega => False_rect B (False_ind False (nega a)) end.

(* Print prob9. *)

(*  (A -> (A /\ ~A)) -> ~A *)
Definition prob10: forall A: Prop, (A -> (A /\ ~A)) -> ~A :=
fun (A : Prop) (ass1 : A -> A /\ ~ A) (a : A) =>
match (ass1 a) with conj H H0 => False_ind False (H0 H)
end.

(* Print prob10. *)

(*  A -> (A -> B) -> B *)
Definition prob11: forall A B: Prop, A -> (A -> B) -> B :=
fun (A B:Prop) (a:A) (ab:A->B) => ab a.

(* Print prob11. *)

(* You will need to use pattern matching for proofs/programs involving
   conjunction, disjunction, and negation.  Specifically, [conj] will
   be useful for conjunction, [or_introl] and [or_intror] for disjunction,
   and [not] and [False_rect] for negation.  You can review those
   by examing the output of these: *)

Print and.
Print or.
Print not.
Print False_rect.


(*
Ignore all the lines below this:
  Theorem a: forall A:Prop, (A -> (A /\ ~A)) -> ~A.
  Proof.
    intro A.
    intro ass1.
    unfold not.
    intro a.
    apply ass1 in a.
    destruct a.
    contradiction.
  Qed.
*)
