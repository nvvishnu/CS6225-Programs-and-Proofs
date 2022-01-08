(** CS6225 Spring 2020 @ IITM : Problem Set 7 *)

Require Import Frap.

(* Authors:
 * Ben Sherman (sherman@csail.mit.edu),
 * Joonwon Choi (joonwonc@csail.mit.edu),
 * Adam Chlipala (adamc@csail.mit.edu)
 *)

(* In this problem set, we will work with the following simple imperative language with
 * a nondeterministic choice operator. Your task is to define both big-step as well as
 * a particular kind of small-step operational semantics for this language
 * (one that is in fact deterministic), and to prove a theorem connecting the two:
 * if the small-step semantics aborts, then the big-step semantics may abort.
 *
 * This is the first problem set so far in this class that is truly open-ended.
 * We want to give you the flexibility to define the operational semantics as
 * you wish, and if you'd like you may even differ from the template shown here
 * if you find it more convenient.
 * Additionally, this is the first problem set where it is *NOT* sufficient to
 * just get the file compiling without any use of [admit] or [Admitted].
 * This will not necessarily guarantee that you have given reasonable semantics
 * for the programming language, and accordingly, will not necessarily
 * guarantee that you will earn full credit. For instance, if you define
 * your small-step semantics as the empty relation (which is incorrect),
 * the theorem you must prove to connect your big-step and small-step
 * semantics will be trivial.
 *)

(** * Syntax *)

(* Basic arithmetic expressions, as we've seen several times in class. *)
Inductive arith : Set :=
| Const : nat -> arith
| Var : var -> arith
| Plus : arith -> arith -> arith
| Eq : arith -> arith -> arith
(* should return 1 if the two expressions are equal, and 0 otherwise. *)
| Lt : arith -> arith -> arith
(* should return 1 if the first expression is less than then second, and 0 otherwise. *)
.

(* The simple imperative language with a [Choose] syntax for
 * nondeterminism. The intended meaning of the program
 * [Choose c c'] is that either [c] should run or [c'] should run.
 *)
Inductive cmd :=
| Assign : var -> arith -> cmd
| Skip : cmd
| Seq : cmd -> cmd -> cmd
| Choose : cmd -> cmd -> cmd (* Here's the main novelty: nondeterministic choice *)
| If : arith -> cmd (* then *) -> cmd (* else *) -> cmd
| While : arith -> cmd -> cmd
| Abort : cmd (* This command should immediately terminate the program *)
.

(** Notations *)

Delimit Scope cmd_scope with cmd.

Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Infix "+" := Plus : arith_scope.
Infix "==" := Eq (at level 75) : arith_scope.
Infix "<" := Lt : arith_scope.
Delimit Scope arith_scope with arith.
Notation "x <- e" := (Assign x e%arith) (at level 75) : cmd_scope.
Infix "<|>" := Choose (at level 78) : cmd_scope.
Infix ";;" := Seq (at level 80) : cmd_scope.

Notation "'if_' c 'then' t 'else' f" := (If c%arith t f) (at level 75) : cmd_scope.
Notation "'while' c 'do' p" := (While c%arith p) (at level 75) : cmd_scope.


(** * Examples *)

(* All nondeterministic realizations of [test_prog1] terminate
 * (either normally or by aborting). [test_prog1 5] may abort,
 * but [test_prog1 6] always terminates normally.
 *)
Definition test_prog1 (k : nat) : cmd := (
  "target" <- 8 ;;
  ("x" <- 3 <|> "x" <- 4) ;;
  ("y" <- 1 <|> "y" <- k) ;;
  if_ "x" + "y" == "target"
     then Abort
     else Skip
  )%cmd.

(* No matter the value of [num_iters], [test_prog2 num_iters]
 * always may potentially fail to terminate, and always
 * may potentially abort.
 *)
Definition test_prog2 (num_iters : nat) : cmd := (
   "acc" <- 0 ;;
   "n" <- 0;;
   while ("n" < 1) do (
     (Skip <|> "n" <- 1) ;;
     "acc" <- "acc" + 1
   ) ;;
   if_ "acc" == S num_iters
     then Abort
     else Skip
  )%cmd.


(* We've seen the expression language in class a few times,
 * so here we'll just give you the interpreter for that
 * expression language.
 *)
Definition valuation := fmap var nat.

Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Eq e1 e2 => if interp e1 v ==n interp e2 v then 1 else 0
  | Lt e1 e2 => if lt_dec (interp e1 v) (interp e2 v) then 1 else 0
  end.

(** ** Part 1: Big-step operational semantics *)

(* You should define some result type (say, [result]) for values that commands
   in the language run to, and define a big-step operational semantics
   [eval : valuation -> cmd -> result -> Prop]
   that says when a program *may* run to some result in *some* nondeterministic
   realization of the program. Then you should also define a predicate
   [big_aborted : result -> Prop]
   that describes which results indicate that the program aborted.
 *)

(* Change Definition to Fixpoint - Check if it's fine *)
Inductive result : Type := 
| Aborted: result
| Terminated: valuation -> result.

(* 5 points *)
Inductive eval : valuation -> cmd -> result -> Prop :=
| EvalSkip : forall v,
  eval v Skip (Terminated v)
| EvalAssign : forall v x e,
  eval v (Assign x e) (Terminated (v $+ (x, interp e v)))
| EvalSeq : forall v c1 v1 c2 v2,
  eval v c1 (Terminated v1)
  -> eval v1 c2 v2
  -> eval v (Seq c1 c2) v2
|EvalSeqAbort: forall v c1 c2,
eval v c1 (Aborted) -> eval v (Seq c1 c2) Aborted
| EvalIfTrue : forall v e then_ else_ v',
  interp e v <> 0
  -> eval v then_ v'
  -> eval v (If e then_ else_) v'
| EvalIfFalse : forall v e then_ else_ v',
  interp e v = 0
  -> eval v else_ v'
  -> eval v (If e then_ else_) v'
| EvalWhileTrue : forall v e body v' v'',
  interp e v <> 0
  -> eval v body (Terminated v')
  -> eval v' (While e body) v''
  -> eval v (While e body) v''
|EvalWhileTrueAbort: forall v e body,
interp e v <> 0
-> eval v body Aborted -> eval v (While e body) Aborted
| EvalWhileFalse : forall v e body,
  interp e v = 0
  -> eval v (While e body) (Terminated v)
| EvalAbort: forall v,
  eval v Abort Aborted
| EvalChoose1: forall v c1 v1 c2,
eval v c1 v1
-> eval v (Choose c1 c2) v1
|EvalChoose2: forall v c2 v2 c1,
eval v c2 v2
-> eval v (Choose c1 c2) v2
.

Definition big_aborted (t: result) : Prop := match t with
| Aborted => True
| Terminated _ => False
end.


(* Prove that your big-step semantics behaves appropriately
 * for the example program:
 *)

Ltac eval1 :=
     apply EvalSkip 
  || apply EvalAssign 
  || eapply EvalSeq
  || eapply EvalSeqAbort
  || (apply EvalIfTrue; [ simplify; equality | ])
  || (apply EvalIfFalse; [ simplify; equality | ])
  || (eapply EvalWhileTrue; [ simplify; equality | | ])
  || (eapply EvalWhileTrueAbort; [ simplify; equality | | ])
  || (apply EvalWhileFalse; [ simplify; equality ])
  || eapply EvalAbort
  || (eapply EvalChoose1; [ simplify; equality | ])
  || (eapply EvalChoose2; [ simplify; equality | ])
.
Ltac evaluate := simplify; try equality; repeat eval1.

(* 5 points *)
Example test_prog1_reachable :
  exists res, eval $0 (test_prog1 5) res /\ big_aborted res.
Proof.
  eexists; propositional.
  evaluate; simplify.
  eapply EvalChoose1.
  eapply EvalAssign.
  eapply EvalChoose2.
  eapply EvalAssign.
  evaluate; simplify.
  simplify.
  propositional.
Qed.


(* 5 points *)
Example test_prog1_unreachable :
  forall res, eval $0 (test_prog1 6) res -> big_aborted res -> False.
Proof.
  induct 1; simplify.
  Check JMeq.JMeq.
  invert H;  invert H0; invert H9; invert H5;  invert H7; invert H6;invert H3; invert H5; invert H7; simplify;  apply IHeval2;simplify; equality. 

    invert H.  invert H4. invert H6. invert H3.  invert H7. invert H5. invert H5. invert H3. invert H7. invert H5. invert H5.
   invert H3. invert H4. invert H6. invert H4. invert H4. invert H2.
Qed.
  (** ** Part 2: Small-step deterministic operational semantics *)

(* Next, you should define a small-step operational semantics for this
   language that in some sense tries to run *all* possible nondeterministic
   realizations and aborts if any possible realization aborts.
   Define a type [state] that represents the underlying state that the
   small-step semantics should take steps on, and then define a small-step
   semantics
   [step : state -> state -> Prop]
   .

   Here's the twist: we ask that you define an operational semantics that
   is *deterministic*, in the sense of the following formal statement:
   [forall s1 s2 s2', step s1 s2 -> step s1 s2' -> s2 = s2'].

   The operational model that we have in mind in this: when we encounter
   a nondeterministic choice, we execute the left branch. If the left
   branch terminates without aborting, we backtrack and try the
   other nondeterministic choice.

   Note that if any possible realization does not terminate,
   we allow the deterministic small-step semantics to diverge as well.
   (It is actually possible to define a semantics that always "finds" aborts,
   even if some branches of nondeterminism diverge!  However, the proof of that
   variant would likely be significantly more complicated, and we haven't tried
   it ourselves.)

   Define a function
   [init : valuation -> cmd -> state]
   that builds starting states for the small-step semantics,
   a predicate
   [small_aborted : state -> Prop]
   that describes which states are considered aborted, and
   a predicate
   [small_terminated : state -> Prop]
   that describes states that have run to completion without any
   nondeterministic branch aborting.
 *)

Inductive state : Type :=
| AbortState : state
| Running: valuation -> cmd -> state
.
(* We need to have old valuation to be able to backtrack *)

(* 5 points *)
(*Inductive step: state -> state -> Prop :=
|StepAborted: step AbortState AbortState
|StepAbort: forall v,
  step (Running v v Abort) AbortState 
| StepAssign : forall v x e,
  step (Running v v (Assign x e)) (Running (v $+ (x, interp e v)) (v $+ (x, interp e v)) Skip)
| StepSeq1 : forall v c1 c2 v' c1',
  step (Running v v c1) (Running v' v' c1')
  -> step (Running v v (Seq c1 c2)) (Running v' v' (Seq c1' c2))
| StepSeq2 : forall v c2,
  step (Running v v (Seq Skip c2)) (Running v v c2)
| StepIfTrue : forall v e then_ else_,
  interp e v <> 0
  -> step (Running v v (If e then_ else_)) (Running v v then_)
| StepIfFalse : forall v e then_ else_,
  interp e v = 0
  -> step (Running v  v (If e then_ else_)) (Running v v else_)
| StepWhileTrue : forall v e body,
  interp e v <> 0
  -> step (Running v v (While e body)) (Running v v (Seq body (While e body)))
| StepWhileFalse : forall v e body,
  interp e v = 0
  -> step (Running v v (While e body)) (Running v v Skip)
| StepChoose1Term: forall v v' c1' c2 c1,
  step (Running v v c1) (Running v' v' c1')
  -> step (Running v v (Choose c1 c2)) (Running v' v (Choose c1' c2))
| StepChoose1TermSkip: forall v c2 c1 v' v'',
  step (Running v' v' c1) (Running v'' v'' Skip)
  -> step(Running v  v (Choose c1 c2)) (Running v v c2)
  (*step (Running v (Choose Skip c2)) (Running v c2)*)
| StepChoose1Abort: forall v c1 c2,
    step (Running v v c1) AbortState
  -> step (Running v v (Choose c1 c2)) (AbortState).*)

Inductive step: state->state-> Prop :=
|StepAborted: step AbortState AbortState
|StepAbort: forall v,
  step (Running v Abort) AbortState 
| StepAssign : forall v x e,
  step (Running v (Assign x e)) (Running (v $+ (x, interp e v)) Skip)
| StepSeq1 : forall v c1 c2 v' c1',
  step (Running v c1) (Running v' c1')
  -> step (Running v (Seq c1 c2)) (Running  v' (Seq c1' c2))
| StepSeq2 : forall v c2,
  step (Running v (Seq Skip c2)) (Running v c2)
| StepIfTrue : forall v e then_ else_,
  interp e v <> 0
  -> step (Running v (If e then_ else_)) (Running v then_)
| StepIfFalse : forall v e then_ else_,
  interp e v = 0
  -> step (Running v (If e then_ else_)) (Running v else_)
| StepWhileTrue : forall v e body,
  interp e v <> 0
  -> step (Running v (While e body)) (Running v (Seq body (While e body)))
| StepWhileFalse : forall v e body,
  interp e v = 0
  -> step (Running v (While e body)) (Running v Skip)
(*| StepChoose1Term: forall v v' c1' c2 c1,
  step (Running v c1) (Running v' c1')
  -> step (Running v (Choose c1 c2)) (Running v' (Choose c1' c2))*)
| StepChoose1TermSkip: forall v v' c1 c2,
  step (Running v c1) (Running v' Skip)
  -> step (Running v (Choose c1 c2) ) (Running v' Skip)
| StepChooseBacktrack: forall v v' c1 c2,
  step (Running v c1 ) (Running v' Skip)
  -> step (Running v  (Choose c1 c2) ) (Running v c2 )
  (*step (Running v (Choose Skip c2)) (Running v c2)*)
| StepChoose1Abort: forall v c1 c2,
    step (Running v c1) AbortState
  -> step (Running v (Choose c1 c2)) (AbortState).

Definition init (v:valuation) (c:cmd) :state := Running v c.

Definition small_aborted (s:state) : Prop := match s with
| AbortState => True
| Running  _ _ => False
end.

Definition small_terminated (s:state) :Prop := match s with
| Running _ Skip => True
| _ => False
end.

(* Prove that your small-step semantics behaves appropriately
 * for the example program:
 *)
Ltac step1 :=
  apply TrcRefl || eapply TrcFront
  || apply StepAssign || apply StepSeq2 || eapply StepSeq1
  || (apply StepIfTrue; [ simplify; equality ])
  || (apply StepIfFalse; [ simplify; equality ])
  || (eapply StepWhileTrue; [ simplify; equality ])
  || (apply StepWhileFalse; [ simplify; equality ])
  || apply StepAborted || apply StepAbort 
  (*|| (eapply StepChoose1Term; [ simplify; equality ])*)
  || (eapply StepChoose1TermSkip; [ simplify; equality ])
  || (eapply StepChoose1Abort; [ simplify; equality ]).
Ltac stepper := simplify; try equality; repeat step1.


(* 5 points *)
Example test_prog1_reachable_small :
  exists st, step^* (init $0 (test_prog1 5)) st /\ small_aborted st.
Proof.
  eexists; propositional.
  unfold test_prog1.
  eapply TrcFront.
  econstructor.
  econstructor.
  econstructor.
   econstructor.

  eapply TrcFront.
  econstructor.
  eapply StepSeq1.
  eapply StepSeq2.


  eapply TrcFront.
  eapply StepSeq1.
  eapply StepSeq1.  
  eapply StepChoose1TermSkip.
  econstructor.

  eapply TrcFront.
  eapply StepSeq1.
  eapply StepSeq2.

  eapply TrcFront.
  eapply StepSeq1.
  eapply StepChooseBacktrack.
  eapply StepAssign.
  
  eapply TrcFront. 
  eapply StepSeq1.
  eapply StepAssign.

  eapply TrcFront. 
  eapply StepSeq2.

  eapply TrcFront. 
  eapply StepIfTrue.
  simplify.
  linear_arithmetic.

  eapply TrcFront. 
  eapply StepAbort.
  
   eapply TrcRefl.   
   simplify.
   propositional.
Qed.



(* 5 points *)
Example test_prog1_unreachable_small :
  forall st, step^* (init $0 (test_prog1 6)) st -> small_aborted st -> False.
Proof.
  simplify.
  unfold test_prog1 in *.
  
  invert H.
  invert H0.
  invert H1.
  invert H6.
  invert H1.
  invert H3.
  invert H2.

  invert H0.
  invert H.
  simplify.
  invert H6.
  invert H2.
  invert H3.
  invert H1.
  invert H0.
  invert H.
  invert H6.
  invert H1.
  invert H2.
  invert H3.
  
  invert H0.
  invert H.
  invert H7.
  invert H2.
  invert H3.
  invert H1.
  
  invert H0.
  invert H.
  invert H6.
  invert H1.
  invert H2.  

  invert H0.
  invert H.
  invert H6.
  invert H1.
  
  invert H0.
  invert H.
  invert H2.
  
  invert H0.
  invert H.
  simplify.
  equality.

  simplify.
  invert H2.
  invert H0.
  invert H.
  invert H1.  
  invert H2.

  
  invert H0.
  invert H.
  invert H1.
  invert H6.
  
  invert H0.
  invert H6.
  invert H.
  invert H6.
  invert H2.
  
  invert H0.
  invert H.
  simplify. 
  equality.
  simplify.

  invert H1.
  invert H0.
  invert H.
  invert H3.  
  invert H2.

  
  invert H0.
  invert H.
  invert H1.
  invert H6.  
  invert H1.

  
  invert H0.
  invert H.
  invert H6.
  invert H1.
  invert H7.
  invert H1.
  invert H2.

  invert H0.
  invert H.
  invert H6.
  invert H2.
  invert H1.
   
  invert H0.
  invert H.
  invert H6.
  invert H2.
  
  invert H0.
  invert H.
  simplify.
  equality.
  invert H1.
  invert H0.
  invert H.
  invert H2.
  
  invert H1.  
  invert H0.
  invert H.
  invert H6.
  invert H2.
  
  invert H0.
  invert H.
  invert H6.
  invert H1.
  
  invert H0.
  invert H.
  simplify.
  equality.
  invert H2.
  invert H0.
  invert H.
  invert H2.
  invert H6.
  invert H.
  invert H6.
  invert H6.
Qed.

(** ** Part 3: A lemma on big step semantics *)

(* 10 points *)
Lemma lem: forall c1 c2 c3 v res,
  eval v (c1;;(c2;;c3))%cmd res ->
  eval v ((c1;;c2);;c3)%cmd res.
Proof.
  induct c1;simplify. 
  induct c2;simplify.
     - invert H. invert H5. invert H3. invert H2. eapply EvalSeq. eapply EvalSeq. eapply EvalAssign. eapply EvalAssign. assumption. 
      eapply EvalSeqAbort. eapply EvalSeq. eassumption. assumption.  eapply EvalSeqAbort.  eapply EvalSeqAbort. assumption.
     - invert H. invert H5. invert H3. invert H2. eapply EvalSeq. eapply EvalSeq. eapply EvalAssign. eapply EvalSkip. assumption.
      eapply EvalSeqAbort. eapply EvalSeq. eassumption. assumption. eapply EvalSeqAbort. eapply EvalSeqAbort. assumption.
    -  invert H. invert H5. invert H3. invert H2. eapply EvalSeq. eapply EvalSeq. eapply EvalAssign. eapply EvalSeq. eassumption. eassumption.
        assumption. eapply EvalSeqAbort. eapply EvalSeq. eassumption. assumption. eapply EvalSeqAbort. eapply EvalSeqAbort. assumption.
     - invert H. invert H5. invert H3. invert H2. eapply EvalSeq. eapply EvalSeq. eapply EvalAssign. eapply EvalChoose1.  eassumption. assumption.
      eapply EvalSeq. eapply EvalSeq. eapply EvalAssign. eapply EvalChoose2. eassumption. assumption. eapply EvalSeqAbort. eapply EvalSeq. eassumption.
      assumption. eapply EvalSeqAbort. eapply EvalSeqAbort. assumption.
    -  invert H. invert H5. invert H3. invert H2. eapply EvalSeq. eapply EvalSeq. eapply EvalAssign.  eapply EvalIfTrue. assumption. eassumption. assumption.
      eapply EvalSeq. eapply EvalSeq. eapply EvalAssign. eapply EvalIfFalse. assumption. eassumption. assumption. eapply EvalSeqAbort. eapply EvalSeq. eassumption. assumption.
      eapply EvalSeqAbort.  eapply EvalSeqAbort. assumption.
    - invert H. invert H5. invert H3. invert H2. eapply EvalSeq. eapply EvalSeq. eapply EvalAssign. eapply EvalWhileTrue. assumption. eassumption. eassumption. assumption.
      eapply EvalSeq. eapply EvalSeq. eapply EvalAssign. eapply EvalWhileFalse. assumption. assumption.
      eapply EvalSeqAbort. eapply EvalSeq. eassumption. assumption.
      eapply EvalSeqAbort. eapply EvalSeqAbort. assumption.
    - invert H. invert H5. invert H3. invert H2. eapply EvalSeqAbort.  eapply EvalSeq. eassumption. assumption. 
       eapply EvalSeqAbort. eapply EvalSeqAbort. assumption.
    - invert H. invert H5. invert H3. eapply EvalSeq. eapply EvalSeq. eapply EvalSkip. eassumption. assumption.
      eapply EvalSeqAbort. eapply EvalSeq. eassumption. assumption.
       eapply EvalSeqAbort. eapply EvalSeqAbort. assumption.
    - invert H. invert H5. invert H3. eapply EvalSeq. eapply EvalSeq. eapply EvalSeq. eassumption. eassumption. eassumption. assumption.
      eapply EvalSeqAbort. eapply EvalSeq. eassumption. assumption.
            eapply EvalSeqAbort. eapply EvalSeqAbort. eassumption. 
    -  invert H. invert H5. invert H3. 
        eapply EvalSeq. eapply EvalSeq. eapply EvalChoose1. eassumption. eassumption. assumption. 
      eapply EvalSeq. eapply EvalSeq. eapply EvalChoose2. eassumption. eassumption. assumption. 
      eapply EvalSeqAbort. eapply EvalSeq. eassumption. assumption.
      eapply EvalSeqAbort. eapply EvalSeqAbort. eassumption. 
    - invert H. invert H5. invert H3. 
      eapply EvalSeq. eapply EvalSeq. eapply EvalIfTrue. assumption. eassumption. eassumption. eassumption.
      eapply EvalSeq. eapply EvalSeq. eapply EvalIfFalse. assumption. eassumption. eassumption. eassumption.
      eapply EvalSeqAbort. eapply EvalSeq. eassumption. assumption.
      eapply EvalSeqAbort. eapply EvalSeqAbort. eassumption. 
    - invert H. invert H5. invert H3. 
      eapply EvalSeq. eapply EvalSeq. eapply EvalWhileTrue. assumption. eassumption. eassumption. eassumption. assumption.
      eapply EvalSeq. eapply EvalSeq. eapply EvalWhileFalse. assumption. eassumption. eassumption. 
      eapply EvalSeqAbort. eapply EvalSeq. eassumption. assumption.
      eapply EvalSeqAbort. eapply EvalSeqAbort. eassumption. 
    -  invert H. invert H5. invert H3.
      eapply EvalSeqAbort. eapply EvalSeq. eassumption. assumption.  
      eapply EvalSeqAbort. eapply EvalSeqAbort. eassumption. 
Qed.


(** ** Part 4: Connection between big- and small-step semantics *)

(* Prove the following theorem demonstrating the connection between the big-step
 * and small-step semantics:
 *
 * If the small-step semantics aborts, then the big-step semantics may
 * potentially abort.
 *)

(* 40 points *)
Lemma util:forall  v c1, step (Running v c1) AbortState -> eval v  c1 Aborted.
Proof.
  simplify.
  induct c1.
  invert H.
  invert H.
  invert H.
  invert H.
  eapply EvalChoose1.
  eapply IHc1_1.
  assumption.
  invert H.
  invert H.
  eapply EvalAbort.
Qed.

Lemma util_2: forall z ,step^* AbortState z -> z= AbortState.
Proof. 
  induct 1; simplify.
  equality.
  invert H.
  apply IHtrc.
 equality.
Qed.

 Lemma util_3: forall v c v0 c0, step(Running v c) (Running v0 c0) -> forall res, eval v0 c0 res -> eval v c res.
Proof.
  induct 1; simplify.

  invert H.
  constructor.

  invert H0.
  econstructor.
  apply IHstep.
  eassumption.
  assumption.

  apply EvalSeqAbort.
  apply IHstep.
  assumption.

  econstructor.
  constructor.
  assumption.

  constructor.
  assumption.
  assumption.

  apply EvalIfFalse.
  assumption.
  assumption.

  invert H0.
  econstructor.
  assumption.
  eassumption.
  assumption.
  apply EvalWhileTrueAbort.
  assumption.
  assumption.

  invert H0.
  apply EvalWhileFalse. 
  assumption.

  invert H0.
  apply EvalChoose1.
  apply IHstep.
  econstructor.
  apply EvalChoose2.
  assumption.
Qed.

Theorem small_abort_big_may_abort_util : forall v c s,
         step (init v c) s
      -> small_aborted s
      -> exists res, eval v c res /\ big_aborted res.
Proof.
  simplify.
  invert H.
  
  eexists.
  split.
  eapply EvalAbort.
  simplify.
  propositional.

  eexists.
  split.
  eapply EvalAssign.
  simplify.
  equality.

  eexists.
  split.
  eapply EvalSeqAbort.
  simplify.
  equality.
  simplify.
  propositional.

  eexists.
  split.
  eapply EvalSeq.
  eapply EvalSkip.
  simplify.
  equality.
  simplify.
  equality.

  eexists.
  split.
  eapply EvalIfTrue.
  simplify.
  assumption.
  simplify. equality.
  simplify. equality.

  eexists.
  split.
  eapply EvalIfFalse.
  simplify.
  equality.
  simplify. equality.
  simplify. equality.

  eexists.
  split.
  eapply EvalWhileTrue.
  simplify.
  assumption.
  simplify. equality.
  simplify. equality.
  simplify. equality.

  eexists.
  split.
  eapply EvalWhileFalse.
  simplify.
  assumption.
  simplify. equality.
  simplify. equality.
  simplify. equality.
  
  eexists.
  split.
  eapply EvalChoose1.
  eapply util.
  assumption.
  simplify. propositional.

  Unshelve.
  exact Aborted.
  exact Aborted.
  exact Aborted.
  exact Aborted.
  exact $0.
Qed.

Theorem small_abort_big_may_abort : forall v c s,
         step^* (init v c) s
      -> small_aborted s
      -> exists res, eval v c res /\ big_aborted res.
Proof.
  
  induct 1. simplify.
  invert H.

  cases y.
  invert H0.
  eapply small_abort_big_may_abort_util.  
  assumption.
  invert H1.
  apply util_2 in H2.
  rewrite H2.
  eapply small_abort_big_may_abort_util.  
  assumption.

  unfold init in *. 
  simplify.  
assert(small_aborted z -> exists res : result, eval v0 c0 res /\ big_aborted res).
  apply IHtrc.
  equality.
  apply H2 in H1.
  invert H1.
  destruct H3.
eexists.
  split.
 eapply (util_3 v c v0 c0).
 assumption.
  eassumption.
 assumption.
Qed.
 (* As an additional challenge, you  you may want to prove the following
 * theorem. Note that this is *NOT* required for this assignment and
 * will not affect your grade.
 *
 * If the small-step semantics terminates without aborting, then the
 * big-step semantics may *not* abort.
 *)

(*
Theorem small_terminates_big_will_not_abort :
       forall v c s,
         step^* (init v c) s
      -> small_terminated s
      -> forall res,
             eval v c res
          -> big_aborted res
          -> False.
Proof.
Admitted.
*)
