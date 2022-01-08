Require Import Frap.

Set Implicit Arguments.


Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

Definition pid (* process id *) := nat.

Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| If (e : arith) (then_ else_ : cmd)
| While (e : arith) (body : cmd)
| Send (receiver : pid) (e : arith)
| Recv (sender : pid) (x : var).

Definition valuation := fmap var nat.

Definition state := list (pid * valuation * cmd).

(* Here are some notations for the language, which again we won't really
 * explain. *)
Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Infix "+" := Plus : arith_scope.
Infix "-" := Minus : arith_scope.
Infix "*" := Times : arith_scope.
Delimit Scope arith_scope with arith.
Notation "x <- e" := (Assign x e%arith) (at level 75).
Notation "p ! e" := (Send p e%arith) (at level 75).
Notation "p ? x" := (Recv p x) (at level 75). 
Infix ";;" := Sequence (at level 76, right associativity). (* This one changed slightly, to avoid parsing clashes. *)
Notation "'when' e 'then' then_ 'else' else_ 'done'" := (If e%arith then_ else_) (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" := (While e%arith body) (at level 75).

Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Minus e1 e2 => interp e1 v - interp e2 v
  | Times e1 e2 => interp e1 v * interp e2 v
  end.

(* Check if this is fine *)
Fixpoint terminated (s : state) := match s with
[] => True
| (id,v,c) :: s1 =>  match c with 
  Skip => terminated s1
  |_ => False 
end
end.

Inductive context := (* fill in *)
| Hole
| CSeq (C : context) (c : cmd).

Inductive plug : context -> cmd -> cmd -> Prop := (* fill in *)
| PlugHole : forall c, plug Hole c c
| PlugSeq : forall c C c' c2,
  plug C c c'
  -> plug (CSeq C c2) c (Sequence c' c2).

(* 5 points *)
Inductive step0 : valuation * cmd -> valuation * cmd -> Prop := (* fill in *)
| StepAssign : forall v x e,
  step0 (v, Assign x e) (v $+ (x, interp e v), Skip)
| StepSeq1 : forall v c1 c2 v' c1',
  step0 (v, c1) (v', c1')
  -> step0 (v, Sequence c1 c2) (v', Sequence c1' c2)
| StepSeq2 : forall v c2,
  step0 (v, Sequence Skip c2) (v, c2)
| StepIfTrue : forall v e then_ else_,
  interp e v <> 0
  -> step0 (v, If e then_ else_) (v, then_)
| StepIfFalse : forall v e then_ else_,
  interp e v = 0
  -> step0 (v, If e then_ else_) (v, else_)
| StepWhileTrue : forall v e body,
  interp e v <> 0
  -> step0 (v, While e body) (v, Sequence body (While e body))
| StepWhileFalse : forall v e body,
  interp e v = 0
  -> step0 (v, While e body) (v, Skip).

(* 5 points *)
Inductive step : state -> state -> Prop := (* fill in *)
StepSkip: forall s1 s2 p, 
step s1 s2 -> step (p::s1) (p::s2)
| StepSwap: forall p1 p2 s,
step (p1::(p2::s)) (p2::(p1::s))
| StepReduce: forall v c v' c' s i c1 c2 C,
  plug C c c1
  -> step0 (v, c) (v', c')
  -> plug C c' c2
  -> step ((i,v,c1)::s) ((i,v',c2)::s)
| StepComm: forall i1 v1 i2 v2 C1 C2 e1 x s c3 c4 c1 c2,
  plug C1 (i2!e1) c1 -> plug C2 (i1 ? x) c2 -> plug C1 Skip c3 -> plug C2 Skip c4 ->
  step ((i1,v1,c1)::(i2,v2,c2)::s) ((i1,v1,c3)::(i2,v2$+ (x, interp e1 v1),c4)::s). 

Hint Constructors plug step0 step.


Ltac step1 :=
   eapply TrcRefl || eapply TrcFront ||
   eapply StepAssign || eapply StepSeq2 || eapply StepSeq1
  || (eapply StepIfTrue; [ simplify; equality ])
  || (eapply StepIfFalse; [ simplify; equality ])
  || (eapply StepWhileTrue; [ simplify; equality ])
  || (eapply StepWhileFalse; [ simplify; equality ])
(*Ltac step2 :=*)
  ||  eapply StepComm
  || eapply StepReduce
  || eapply StepSkip
  || eapply StepSwap.
Ltac stepper := simplify; try equality; repeat step1. (*( step2; repeat step1). trc; try step2;repeat step1).*)

Definition ex1 : state := [(0, $0, 1 ! 42); (1, $0, 0 ? "x")].

(* 5 points *)
Theorem thm1 : exists v l, step^* ex1 ((1,v,Skip)::l) 
                                 /\ v $? "x" = Some 42.
Proof.
  do 2 eexists. 
  unfold ex1. simplify. propositional.
  eapply TrcFront.  
  
  eapply StepComm.  
  econstructor.
  econstructor.
  econstructor.
  econstructor. 

  simplify.
  eapply TrcFront.
  eapply StepSwap.
  eapply TrcRefl.
  simplify. 
  trivial.
Qed.


(* Lone sender blocks : 2.5 points *)
Theorem thm2 : forall pid1 v pid2 e st, 
  step ^* [(pid1, v, pid2 ! e)] st -> terminated st -> False.
Proof.
  induct 1; simplify.
  equality.
  induct H.
  invert H.
  invert H.
  invert H1.
  invert H0.
Qed.
(* Lone receiver blocks : 2.5 points *)
Theorem thm3 : forall pid1 v pid2 x st,
  step ^* [(pid1, v, pid2 ? x)] st -> terminated st -> False.
Proof.
  induct 1; simplify.
  equality.
  induct H.
  invert H.
  invert H.
  invert H1.
  invert H0.
Qed.

Example ex4 : state := [(0, $0, 1 ! 42;; 
                                2 ? "x");
                        (1, $0, 0 ? "x";;
                                2 ! "x" + 1);
                        (2, $0, 1 ? "x";;
                                0 ! "x" + 1)].

(* 5 points *)
Theorem thm4 : exists v l, 
  step ^* ex4 ((0, v, Skip)::l) /\ v $? "x" = Some 44.
Proof.
  do 2 eexists. 
  unfold ex4. simplify. propositional.
  eapply TrcFront.  
  
  eapply StepComm.  
  econstructor.
  econstructor.
  econstructor.
  econstructor. 
  econstructor.
  econstructor.
  econstructor.
  econstructor.

  eapply TrcFront.  
  eapply StepSwap.
  eapply TrcFront.
  eapply StepSkip.
  eapply StepSwap.

  eapply TrcFront.  
  eapply StepReduce.
  econstructor.
  eapply StepSeq2.
  econstructor.
  
  eapply TrcFront.  
  eapply StepComm.  
  econstructor.
  econstructor.
  econstructor.
  econstructor. 
  econstructor.
  econstructor.

  eapply TrcFront.  
  eapply StepSkip.
  eapply StepReduce.
  econstructor.
  eapply StepSeq2.
  econstructor.  

  eapply TrcFront.  
  eapply StepSkip.
  eapply StepSwap.

  eapply TrcFront.  
  eapply StepSwap.

   eapply TrcFront.  
  eapply StepReduce.
  econstructor.
  eapply StepSeq2.
  econstructor.

  eapply TrcFront.  
  eapply StepSkip.
  eapply StepSwap.

    eapply TrcFront.  
  eapply StepSwap.

  eapply TrcFront.  
  eapply StepComm.  
  econstructor.
  econstructor.
  econstructor.
  econstructor. 

      eapply TrcFront.  
  eapply StepSwap.
  eapply TrcRefl.
  simplify.
  trivial.
Qed.


Definition producer (recv_pid : nat) (num_msgs : nat) :=
  "i" <- num_msgs;;
  while "i" loop
    recv_pid ! "i";;
    "i" <- "i" - 1
  done;;
  recv_pid ! 0.
  
Definition consumer (send_pid : nat) :=
  "again" <- 1;;
  "sum" <- 0;;
  while "again" loop
    send_pid ? "again";;
    "sum" <-  "sum" + 2 * "again"
  done.

(* Try to automate the proof *)

(* 5 points *)
Theorem thm5 : exists v l, 
  step ^* [(0, $0, producer 1 2); (1, $0, consumer 0)] ((1,v,Skip)::l) 
        /\ v $? "sum" = Some 6.
Proof.


  
  
  do 2 eexists. 
  unfold producer. unfold consumer. simplify. propositional.

  eapply TrcFront.    
  eapply StepReduce.
  econstructor.
  econstructor.
  econstructor.
  econstructor. 

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq2.
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq1.
  eapply StepWhileTrue.
  simplify.  equality.
  econstructor.

  eapply TrcFront.
  eapply StepSwap.

  eapply TrcFront.    
  eapply StepReduce.
  econstructor.
  econstructor.
  econstructor.
  econstructor. 

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq2.
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  econstructor.
  econstructor.
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq2.
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepWhileTrue.
  simplify.  equality.
  econstructor.
  
   eapply TrcFront.
  eapply StepSwap. 

  eapply TrcFront.
  eapply StepComm.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  
  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq1.
  eapply StepSeq1.  
  eapply StepSeq2.
  econstructor.

   eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  eapply StepSeq1.
  eapply StepSeq1.
  econstructor.  
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  eapply StepSeq1.
  eapply StepSeq2.
  econstructor.  

   eapply TrcFront.
  eapply StepSwap.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq1.
  eapply StepSeq2.  
  econstructor.

   eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  eapply StepSeq1.
  econstructor.  
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  eapply StepSeq2.
  econstructor.  

  simplify.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  econstructor.
  simplify. equality.
  econstructor.

  eapply TrcFront.
  eapply StepSwap.

   eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  econstructor.
   eapply StepWhileTrue.  
  simplify. equality.
  econstructor.


  eapply TrcFront.
  eapply StepComm.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  
  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq1.
  eapply StepSeq1.  
  eapply StepSeq2.
  econstructor.

   eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  eapply StepSeq1.
  eapply StepSeq1.
  econstructor.  
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  eapply StepSeq1.
  eapply StepSeq2.
  econstructor.  

   eapply TrcFront.
  eapply StepSwap.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq1.
  eapply StepSeq2.  
  econstructor.

   eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  eapply StepSeq1.
  econstructor.  
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  eapply StepSeq2.
  econstructor.  

  simplify.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  econstructor.
  simplify. equality.
  econstructor.

  eapply TrcFront.
  eapply StepSwap.

  

   eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  econstructor.
   eapply StepWhileFalse.  
  simplify. equality.
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  eapply StepSeq2.
  econstructor.

  
  eapply TrcFront.
  eapply StepComm.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.

  eapply TrcFront.
  eapply StepSwap.

   eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  eapply StepSeq1.
  eapply StepSeq2.
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  eapply StepSeq1.
  econstructor.  
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  eapply StepSeq2.
  econstructor.  
  
  simplify.
  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepWhileFalse.
  simplify. equality.
  econstructor.
  
  econstructor.
  simplify. trivial.
Qed.

(*Lemma util: forall n v l ,(step) ^* [(0, $0, producer 1 n); (1, $0, consumer 0)] ((1, v, Skip) :: l) /\ v $? "sum" = Some (n * (n + 1)) -> 
exists v, v $? "i"= Some n-> exists v', v' $? "sum" = Some (S (n + S (n+0))) ->
exists v'', 
(step) ^*
  [(1, v',
   while "again" loop 0 ? "again";; "sum" <- "sum" + 2 * "again" done);
  (0, v, while "i" loop 1 ! "i";; "i" <- "i" - 1 done;; 1 ! 0)] ((1, v'', Skip) :: l) /\ v'' $? "sum" = Some (S (n + 1 + n * S (n + 1))).
Proof.
  simplify.
  do 2 eexists.
  simplify; propositional.
  unfold producer in *. unfold consumer in *.
  simplify.
  eexists.
  split.

  eapply TrcFront in H2.  
  eapply StepReduce in H2.
  econstructor.
  econstructor.
  econstructor.
  econstructor. 

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq2.
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq1.
  eapply StepWhileTrue.
  simplify.  equality.
  econstructor.

  eapply TrcFront.
  eapply StepSwap.

  eapply TrcFront.    
  eapply StepReduce.
  econstructor.
  econstructor.
  econstructor.
  econstructor. 

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq2.
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  econstructor.
  econstructor.
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq2.
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepWhileTrue.
  simplify.  equality.
  econstructor.
  
   eapply TrcFront.
  eapply StepSwap. 

  eapply TrcFront.
  eapply StepComm.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
 

  invert H2.
  invert H. 
  2:{
  invert H4.
  invert H.
  invert H7.
  invert H6.
    invert H9. invert H11. invert H10. invert H2. invert H4. invert H. invert H7. invert H6.
    invert H9. invert H11. invert H10. invert H2. invert H5. invert H. invert H7. invert H6.
    invert H9. invert H11. invert H10. invert H2. invert H4. invert H. invert H8. invert H7.
  invert H9; invert H11; invert H10; invert H4; invert H2; invert H; invert H7; invert H6. 

   
  invert H7. invert H6. invert H10; simplify. try equality. invert H9.  invert H11. invert H6. invert H8. 
  *)
(*Lemmma util: 
(step) ^*
        [(1, $0 $+ ("again", 1) $+ ("sum", 0),
         while "again" loop 0 ? "again";; "sum" <- "sum" + 2 * "again" done);
        (0, $0 $+ ("i", n), while "i" loop 1 ! "i";; "i" <- "i" - 1 done;; 1 ! 0)]
        [(1, $0 $+ ("again", S n) $+ ("sum", n) $+ ("again", n) $+ ("sum", n), Skip);
        (n, $0 $+ ("i", n), Skip)]
*)



 Definition trsys_of (e : state) := {|
    Initial := {e};
    Step := step
  |}.


(*Theorem safety : forall e t, hasty $0 e t
    -> invariantFor (trsys_of e) unstuck.*)

(* Challenge problem : Additional 5% of course grade! *)
Theorem thm6 : forall n, exists v l,
  step ^* [(0, $0, producer 1 n); (1, $0, consumer 0)] ((1,v,Skip)::l) 
        /\ v $? "sum" = Some (n * (n + 1)).
Proof.

  do 2 eexists. 
  unfold producer. unfold consumer. simplify. propositional.
  

  eapply TrcFront.    
  eapply StepReduce.
  econstructor.
  econstructor.
  econstructor.
  econstructor. 

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq2.
  econstructor.
  
  eapply TrcFront.    
  eapply StepSwap.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq1.
  econstructor.
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq2.
  econstructor.

   eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  econstructor.
  econstructor.
  econstructor.

  
   eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq2.
  econstructor.

  simplify. 
  
  induct n; simplify. 

   eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  econstructor.
  simplify. equality.
  econstructor.

   eapply TrcFront.
  eapply StepSwap.  

    eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq1.
  eapply StepWhileFalse.
  simplify.  equality.
  econstructor.

  eapply TrcFront.    
  eapply StepReduce.
  econstructor.
  eapply StepSeq2.
  econstructor.

   eapply TrcFront.
  eapply StepComm.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.  
  econstructor.
  econstructor.  

  eapply TrcFront.
  eapply StepSwap.  

    eapply TrcFront.
  eapply StepReduce.
  econstructor.
  eapply StepSeq1.
    eapply StepSeq2.
  econstructor.

  eapply TrcFront.
  eapply StepReduce.
  econstructor.
  eapply StepSeq1.  
  econstructor.
  econstructor.
  
  simplify.

   eapply TrcFront.
  eapply StepReduce.
  econstructor.
  eapply StepSeq2.
  econstructor.

  eapply TrcFront.
  eapply StepReduce.
  econstructor.
  eapply StepWhileFalse.
  simplify. equality.
  econstructor.  
  
  econstructor.
  simplify. 
Admitted.

(*

  do 2 eexists. 
  unfold producer. unfold consumer. simplify. propositional.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  econstructor.
  econstructor.
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq2.
  econstructor.
  
  simplify.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  econstructor.   
  eapply StepWhileTrue.  
  simplify. equality.
  econstructor.

  eapply TrcFront.
  eapply StepSwap.

  eapply TrcFront.    
  eapply StepReduce.
  econstructor.
  econstructor.
  econstructor.
  econstructor. 

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq2.
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  econstructor.
  econstructor.
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq2.
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepWhileTrue.
  simplify.  equality.
  econstructor.
  
  eapply TrcFront.
  eapply StepSwap. 

  eapply TrcFront.
  eapply StepComm.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  
  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq1.
  eapply StepSeq1.  
  eapply StepSeq2.
  econstructor.

   eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  eapply StepSeq1.
  eapply StepSeq1.
  econstructor.  
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  eapply StepSeq1.
  eapply StepSeq2.
  econstructor.  

   eapply TrcFront.
  eapply StepSwap.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.
  eapply StepSeq1.
  eapply StepSeq2.  
  econstructor.

   eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  eapply StepSeq1.
  econstructor.  
  econstructor.

  eapply TrcFront.
  eapply StepReduce.  
  econstructor.  
  eapply StepSeq2.
  econstructor.  

  simplify.
  

  


 fold consumer.

  fold producer.

  
  unfold producer in IHn.
  unfold consumer in IHn.
  simplify. 
  invert IHn.
  invert H.
  invert H0.
  invert H.
  
  invert H0.
  invert H5.
  invert H4.
  invert H2.
  invert H9.

  
  econstructor.



  
  eapply StepWhileTrue.
  simplify.  equality.
  econstructor.*)
 