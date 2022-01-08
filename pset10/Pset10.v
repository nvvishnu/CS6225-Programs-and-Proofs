(** CS6225 Spring 21 @ IITM : PSet 10 -- 90 points *)

(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 10 *)

Require Import Frap.

(* Authors:
 * Joonwon Choi (joonwonc@csail.mit.edu)
 * Adam Chlipala (adamc@csail.mit.edu)
 *)

Set Implicit Arguments.

(** * Hoare Logic with Input/Output Traces *)

(* Hoare logic as covered in lecture is only the beginning, so far as
 * programming features that can be supported. In this problem set, we
 * will implement one of variant, a Hoare logic that deals with
 * input/output traces.
 *
 * As we learned in compiler verification, behaviors of a program can be
 * defined as sequences of communications with the outside world. Hoare logic
 * certainly can be used for proving properties about program behaviors.
 * Besides valuation and heap, we will need to keep track of traces of a program
 * to ensure the properties we want, sometimes by proving invariants in the
 * middle of the program.
 *
 * The problem set consists of 4 tasks; basically we ask you to formally prove
 * the correctness of some programs using Hoare logic:
 * 1) To design a big-step operational semantics of the given language.
 * 2) To define a Hoare logic for the language, and to prove the consistency
 *    between the semantics and the logic.
 * 3) To verify three example programs we provide, using Hoare logic.
 * 4) To design your own interesting program and to verify it.
 *)

(** * Language syntax *)

(* There is nothing special with the definitions of [exp] and [bexp]; they are
 * exactly same as we've seen in the lecture.
 *)
Inductive exp :=
| Const (n : nat)
| Var (x : string)
| Read (e1 : exp)
| Plus (e1 e2 : exp)
| Minus (e1 e2 : exp)
| Mult (e1 e2 : exp).

Inductive bexp :=
| Equal (e1 e2 : exp)
| Less (e1 e2 : exp).

(* [heap] and [valuation] are also as usual. *)
Definition heap := fmap nat nat.
Definition valuation := fmap var nat.

(* Besides [heap] and [valuation], we have one more component to verify using
 * Hoare logic, called [io]. We keep track of inputs and outputs of a certain
 * program, regarding them as meaningful communication with the outside world.
 * When a program is executed, it generates [trace], which is a list of [io]s,
 * meaning inputs and outputs that occurred during the execution. Traces are
 * also called behaviors of a program.
 *)
Inductive io := In (v : nat) | Out (v : nat).
Definition trace := list io.

(* We now have two types of assertions: [iassertion] is used only for asserting
 * properties of internal states. [assertion] can be used for asserting
 * properties of [trace]s as well as internal states.
 *)
Definition iassertion := heap -> valuation -> Prop.
Definition assertion := trace -> heap -> valuation -> Prop.

(* [cmd] has more constructors than what we've seen.  The new ones are called
 * [Input] and [Output]. As expected, semantically they generates [io]s,
 * eventually forming a [trace] of a program.
 *)
Inductive cmd :=
| Skip
| Assign (x : var) (e : exp)
| Write (e1 e2 : exp)
| Seq (c1 c2 : cmd)
| If_ (be : bexp) (then_ else_ : cmd)
| While_ (inv : assertion) (be : bexp) (body : cmd)

| Assert (a : iassertion) (* Note that we are using [iassertion], not
                           * [assertion], for [Assert]. While [valuation] and
                           * [heap] are internal states directly manipulated by
                           * a program, [trace] is rather an abstract notion for
                           * defining a behavior of a program.
                           *)

(* The new constructors are below! *)
| Input (x : var) (* [Input] takes an input from the external world and assigns
                   * the value to the local variable [x].
                   *)
| Output (e : exp). (* [Output] prints the value of [e]. *)

(** We here provide fancy notations for our language. *)

Coercion Const : nat >-> exp.
Coercion Var : string >-> exp.
Notation "*[ e ]" := (Read e) : cmd_scope.
Infix "+" := Plus : cmd_scope.
Infix "-" := Minus : cmd_scope.
Infix "*" := Mult : cmd_scope.
Infix "=" := Equal : cmd_scope.
Infix "<" := Less : cmd_scope.
Definition set (dst src : exp) : cmd :=
  match dst with
  | Read dst' => Write dst' src
  | Var dst' => Assign dst' src
  | _ => Assign "Bad LHS" 0
  end.
Infix "<-" := set (no associativity, at level 70) : cmd_scope.
Infix ";;" := Seq (right associativity, at level 75) : cmd_scope.
Notation "'when' b 'then' then_ 'else' else_ 'done'" :=
  (If_ b then_ else_) (at level 75, b at level 0) : cmd_scope.
Notation "{{ I }} 'while' b 'loop' body 'done'" := (While_ I b body) (at level 75) : cmd_scope.
Notation "'assert' {{ I }}" := (Assert I) (at level 75) : cmd_scope.
Notation "x '<--' 'input'" := (Input x) (at level 75) : cmd_scope.
Notation "'output' e" := (Output e) (at level 75) : cmd_scope.
Delimit Scope cmd_scope with cmd.

Infix "+" := plus : reset_scope.
Infix "-" := Init.Nat.sub : reset_scope.
Infix "*" := mult : reset_scope.
Infix "=" := eq : reset_scope.
Infix "<" := lt : reset_scope.
Delimit Scope reset_scope with reset.
Open Scope reset_scope.


(** * Task 1: A big-step operational semantics for commands *)

(* Your first task is to define a big-step operational semantics for commands.
 * While it should be very similar to what we've seen in class, it should
 * also represent something about [io]s (or [trace]). Make sure the semantics
 * captures the effects of [Input]/[Output] on [trace]s. The most
 * recent event should appear at the *front* of the list in the trace.
 *
 * We provide the signature of the big-step semantics below. Replace the
 * [Axiom] below with your own definition of the semantics.
 * The first three arguments are the trace, heap, and valuation before execution,
 * and the final three arguments are the trace, heap, and valuation after execution.
 *)

(** * Define your semantics here! *)
Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).
Fixpoint eval (e : exp) (h : heap) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x => v $! x
  | Read e1 => h $! eval e1 h v
  | Plus e1 e2 => eval e1 h v + eval e2 h v
  | Minus e1 e2 => eval e1 h v - eval e2 h v
  | Mult e1 e2 => eval e1 h v * eval e2 h v
  end.

Fixpoint beval (b : bexp) (h : heap) (v : valuation) : bool :=
  match b with
  | Equal e1 e2 => if eval e1 h v ==n eval e2 h v then true else false
  | Less e1 e2 => if eval e2 h v <=? eval e1 h v then false else true
  end.
(* 10 points *)
Inductive exec : trace -> heap -> valuation -> cmd ->
             trace -> heap -> valuation -> Prop:=
| ExSkip : forall h v t,
  exec t h v Skip t h v
| ExAssign : forall h v x e t,
  exec t h v (Assign x e) t h (v $+ (x, eval e h v))
| ExWrite : forall h v e1 e2 t,
  exec t h v (Write e1 e2) t (h $+ (eval e1 h v, eval e2 h v)) v
| ExSeq : forall h1 v1 c1 h2 v2 c2 h3 v3 t t1 t2,
  exec t h1 v1 c1 t1 h2 v2
  -> exec t1 h2 v2 c2 t2 h3 v3
  -> exec t h1 v1 (Seq c1 c2) t2 h3 v3
| ExIfTrue : forall h1 v1 b c1 c2 h2 v2 t t1,
  beval b h1 v1 = true
  -> exec t h1 v1 c1 t1 h2 v2
  -> exec t h1 v1 (If_ b c1 c2) t1 h2 v2
| ExIfFalse : forall h1 v1 b c1 c2 h2 v2 t t1,
  beval b h1 v1 = false
  -> exec t h1 v1 c2 t1 h2 v2
  -> exec t h1 v1 (If_ b c1 c2) t1 h2 v2
| ExWhileFalse : forall I h v b c t,
  beval b h v = false
  -> exec t h v (While_ I b c) t h v
| ExWhileTrue : forall I h1 v1 b c h2 v2 h3 v3 t t1 t2,
  beval b h1 v1 = true
  -> exec t h1 v1 c t1 h2 v2
  -> exec t1 h2 v2 (While_ I b c) t2 h3 v3
  -> exec t h1 v1 (While_ I b c) t2 h3 v3
| ExInput: forall h v x t p,
  exec t h v (Input x) (In p::t) h (v $+ (x, p))
|ExOutput: forall h v t p,
  exec t h v (Output p) ((Out (eval p h v))::t) h v
| ExAssert : forall t h v (a : iassertion),
  a h v
  -> exec t h v (Assert a) t h v.

(** * Task 2 : Hoare logic *)

(* We also ask you to define a Hoare logic for our language. The logic should
 * derive triples of the form {{ P }} c {{ Q }}, where "P" and "Q" have type
 * [assertion] and "c" has type [cmd]. It should be also very similar to the
 * Hoare logic we've defined in class.
 *)

(* The logic should be consistent with the semantics you defined, so we
 * also ask you to prove a soundness relation between your Hoare logic and your
 * semantics.  You will need this consistency to prove the correctness of
 * example programs we will provide soon.
 *)

(** Task 2-1: Define your Hoare logic here! *)

(* 10 points *)
Inductive hoare_triple : assertion -> cmd -> assertion -> Prop:=
| HtSkip : forall P, hoare_triple P Skip P
| HtAssign : forall (P : assertion) x e,
  hoare_triple P (Assign x e) (fun q h v => exists v', P q h v' /\ v = v' $+ (x, eval e h v'))
| HtWrite : forall (P : assertion) (e1 e2 : exp),
  hoare_triple P (Write e1 e2) (fun q h v => exists h', P q h' v /\ h = h' $+ (eval e1 h' v, eval e2 h' v))
| HtSeq : forall (P Q R : assertion) c1 c2,
  hoare_triple P c1 Q
  -> hoare_triple Q c2 R
  -> hoare_triple P (Seq c1 c2) R
| HtIf : forall (P Q1 Q2 : assertion) b c1 c2,
  hoare_triple (fun q h v => P q h v /\ beval b h v = true) c1 Q1
  -> hoare_triple (fun q h v => P q h v /\ beval b h v = false) c2 Q2
  -> hoare_triple P (If_ b c1 c2) (fun q h v => Q1 q h v \/ Q2 q h v)
| HtWhile : forall (I P : assertion) b c,
  (forall q h v, P q h v -> I q h v)
  -> hoare_triple (fun q h v => I q h v /\ beval b h v = true) c I
  -> hoare_triple P (While_ I b c) (fun q h v => I q h v /\ beval b h v = false)
| HtAssert : forall (P : assertion) (I : iassertion),
  (forall q h v, P q h v-> I h v)
  -> hoare_triple P (Assert I) P
| HtInput: forall (P : assertion) x ,
  hoare_triple P (Input x) (fun q h v => exists q' v' p, P q' h v' /\ q = (In p)::q' /\ v = v' $+ (x,p))
|HtOutput: forall (P : assertion) p ,
  hoare_triple P (Output p) (fun q h v => exists q', P q' h v /\ q = (Out (eval p h v))::q')
| HtConsequence : forall (P Q P' Q' : assertion) c,
  hoare_triple P c Q
  -> (forall q h v, P' q h v -> P q h v)
  -> (forall q h v, Q q h v -> Q' q h v)
  -> hoare_triple P' c Q'.


(** Task 2-2: Prove the consistency theorem. *)

Lemma hoare_triple_big_step_while: forall (I : assertion) b c,
  (forall tr tr' h v h' v', exec tr h v c tr' h' v'
                     -> I tr h v
                     -> beval b h v = true
                     -> I tr' h' v')
  -> forall tr tr' h v h' v', exec tr h v (While_ I b c) tr' h' v'
                       -> I tr h v
                       -> I tr' h' v' /\ beval b h' v' = false.
Proof.
  induct 2; eauto.
Qed.

(* That main theorem statement literally translates our intuitive description of
 * [hoare_triple] from above. *)

(* 10 points *)
Theorem hoare_triple_big_step :
  forall pre c post,
    hoare_triple pre c post ->
    forall tr h v tr' h' v',
      exec tr h v c tr' h' v' ->
      pre tr h v -> post tr' h' v'.
Proof.
  induct 1; eauto; invert 1; eauto.
  simplify.
  eapply hoare_triple_big_step_while; eauto.
  
  simplify. eexists. eexists. eexists. split. eassumption. split. simplify. trivial. 
  trivial.
Qed.

Lemma HtStrengthenPost : forall (P Q Q' : assertion) c,
  hoare_triple P c Q
  -> (forall t h v, Q t h v -> Q' t h v)
  -> hoare_triple P c Q'.
Proof.
  simplify; eapply HtConsequence; eauto.
Qed.


(** * Task 3: Verification of some example programs *)

(* Now it's time to verify programs using the Hoare logic you've just defined!
 * We provide three example programs and three corresponding correctness
 * theorems. You are required to prove the theorems stated below using Hoare
 * logic.
 *)

Ltac ht1 := apply HtSkip || apply HtAssign || apply HtWrite || eapply HtSeq || eapply HtIf || eapply HtWhile || eapply HtAssert || eapply HtInput || eapply HtOutput
            || eapply HtStrengthenPost.

Ltac t := cbv beta; propositional; subst;
          repeat match goal with
                 | [ H : ex _ |- _ ] => invert H; propositional; subst
                 end;
          simplify;
          repeat match goal with
                 | [ _ : context[?a <=? ?b] |- _ ] => destruct (a <=? b); try discriminate
                 | [ H : ?E = ?E |- _ ] => clear H
                 end; simplify; propositional; auto; try equality; try linear_arithmetic.

Ltac ht := simplify; repeat ht1; t.


(** Task 3-1: adding two inputs -- prove [add_two_inputs_ok] *)

Example add_two_inputs :=
  ("x" <-- input;;
   "y" <-- input;;
   output ("x" + "y"))%cmd.

(* 10 points *)
Theorem add_two_inputs_ok:
  forall tr h v tr' h' v',
    exec tr h v add_two_inputs tr' h' v' ->
    tr = nil ->
    exists vx vy, tr' = [Out (vx + vy); In vy; In vx].
Proof.
  unfold add_two_inputs. simplify.
  invert H. invert H6. invert H10. invert H4. invert H8.
  unfold eval. exists p. exists p0. simplify. trivial.
Qed.

(** Task 3-2: finding the maximum of three numbers -- prove [max3_ok] *)

Example max3 :=
  ("x" <-- input;;
   "y" <-- input;;
   "z" <-- input;;
   when "x" < "y" then
     when "y" < "z" then
       output "z"
     else
       output "y"
     done
   else
     when "x" < "z" then
       output "z"
     else
       output "x"
     done
   done)%cmd.

(* 10 points *)
Inductive max3_spec : trace -> Prop :=
| M3s: forall x y z mx,
    mx >= x ->
    mx >= y ->
    mx >= z ->
    (mx = x \/ mx = y \/ mx = z) ->
    max3_spec [Out mx; In z; In y; In x].

Theorem max3_ok:
  forall tr h v tr' h' v',
    exec tr h v max3 tr' h' v' ->
    tr = nil ->
    max3_spec tr'.
Proof.
  unfold max3. simplify.
  ht. invert H. invert H5. invert H9. invert H4. invert H8. invert H4. invert H9. invert H8. invert H10. invert H0. invert H9. invert H11. invert H1. simplify.
 simplify.  cases(p1 <=? p0). invert H0.  cases (p0 <=? p). invert H2. eapply M3s. linear_arithmetic. linear_arithmetic. linear_arithmetic. trivial. linear_arithmetic.
  invert H11. invert H9. simplify. cases(p0 <=? p). invert H0.  cases (p1 <=? p0).  eapply M3s. linear_arithmetic. linear_arithmetic. linear_arithmetic. linear_arithmetic. invert H1.
  invert H10. invert H8. invert H9. invert H11. simplify. cases(p0 <=? p). cases(p1<=?p). invert H1. eapply M3s. linear_arithmetic. linear_arithmetic. linear_arithmetic. linear_arithmetic.
  cases(p1<=?p). invert H0. invert H0. invert H11. invert H8. simplify. cases(p1<=?p); cases(p0 <=? p). 
  eapply M3s. linear_arithmetic. linear_arithmetic. linear_arithmetic. linear_arithmetic.
  invert H0. invert H9. invert H9.
Qed.  
  
(** Task 3-3: Fibonacci sequence -- prove [fibonacci_ok] *)

Inductive fibonacci_spec : trace -> Prop :=
| Fs0: fibonacci_spec nil
| Fs1: fibonacci_spec [Out 1]
| Fs2: fibonacci_spec [Out 1; Out 1]
| Fsn:
    forall x y tr,
      fibonacci_spec (Out y :: Out x :: tr) ->
      fibonacci_spec (Out (x + y) :: Out y :: Out x :: tr).

Fixpoint fib (n:nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    match n' with
    | 0 => 1
    | S n'' => fib n' + fib n''
    end
  end.

(* 20 points *)
Example fibonacci (n: nat) :=
  ("cnt" <- 0;;
   "x" <- 0;;
   "y" <- 1;;
   output "y";;
  {{ fun q h v =>  
  ( (v $! "cnt") = 0 -> q= [Out (v $! "y")] /\ (v$! "y" =1) /\ (v$! "x" =0))  /\
  ((v $! "cnt") > 0 -> (exists q', ((Out (v $! "y") :: Out (v $! "x") :: q')  = q) %reset))
    /\ (q = nil->False) /\ fibonacci_spec q 
}}
  (*{{ fun q h v  =>  let l := v $! "cnt" in (v $? "x" = Some (fib l)) /\  v $? "y" = Some (fib (S l)) /\ fibonacci_spec q }}(* You may change this loop invariant to make your
                            * proof easier! *)*)
(*q=(Out (fib (S l)))::(Out (fib l))::tr  /\ *) 
   while "cnt" < n loop
     "tmp" <- "y";;
     "y" <- "x" + "y";;
     "x" <- "tmp";;
     "cnt" <- "cnt" + 1;;
     output "y"
   done)%cmd.

Lemma fib_hoare:  forall n,
hoare_triple (fun q h v => q = nil) (fibonacci n) (fun q h v => fibonacci_spec q).
Proof.
  
  
  unfold fibonacci. simplify. ht.

  apply Fs1.
  cases (x1 $! "cnt").
  assert (0 = 0). trivial. apply H in H2. 
  invert H2. invert H5. 
  rewrite H2. rewrite H3. simplify. exists []. trivial. 

  cases (x1 $! "cnt"). invert Heq.   
  assert(S n0 > 0). linear_arithmetic. apply H1 in H2. invert H2.  eexists. eauto.   
  cases x. 
  assert(False). apply H3. trivial. invert H1.
  simplify.
  cases (x1 $! "cnt"). 
  assert (0 = 0). trivial. apply H in H1. 
  invert H1. invert H4. 
  rewrite H1. rewrite H6. simplify. rewrite H2. rewrite H1. apply Fs2.
  
 assert( S n0 > 0). linear_arithmetic. apply H0 in H1.
  invert H1. rewrite <- H2. eapply Fsn. rewrite H2. assumption.
Qed. 


Theorem fibonacci_ok (n: nat):
  forall tr h v tr' h' v',
    exec tr h v (fibonacci n) tr' h' v' ->
    tr = nil ->
    fibonacci_spec tr'.
Proof.  
  eapply hoare_triple_big_step. eapply fib_hoare.
Qed.


(** * Task 4: Implement your own program to verify. *)

(* The last task is to implement your own program and to verify its correctness
 * using Hoare logic. Note that the three examples we provided above had nothing
 * to do with [heap]s. Design a program that uses the heap and loops in a nontrivial
 * manner and prove its correctness.
 *)

(* 20 points *)

(** Define your own program and prove its correctness here! *)

(* The following program converts n elements in the heap to val. Such a program can be used in functions like vector.assign() in C++
to replace all the elements in an array *)


(* gen_out produces the expected trace - [(Out val),(Out val).....n times] where n is the size of the array. *)
Fixpoint gen_out (n:nat) (val:nat) : trace := match n with
| 0 => []
| S n' => ((Out val)::gen_out n' val)
end.


(* Definition of the program. We will verify the correctness of the program by outputting the value in the heap immediately after its update.
The expected trace should be [(Out val),(Out val).....n times] as mentioned above *)
Example non_trivial(n: nat) (val:nat) := 
   ("i" <- 0;;
  {{fun t h v => v $! "i" <= n  /\ t = gen_out (v $! "i") val (* /\
forall j, (v  $! "i") > j -> *["a"+"j"] = val }}*) }}
  while "i" < n loop
          *["a" + "i"] <- val;;
          Output *["a" + "i"];; 
    "i" <- "i" + 1
    done)%cmd. 

(* Utility lemma *)
Lemma util: forall n val,  ((Out val) :: gen_out n val = gen_out (n+1) val).
Proof.
simplify.
induct n; simplify; try equality.
Qed.

(* Prove a strong hoare triplet on the non_trivial program *)
Lemma non_trivial_hoare (n:nat) (val:nat) :
hoare_triple (fun q h v => q = nil) (non_trivial n val) (fun q h v => (v $! "i" = n) /\q = gen_out n val).
Proof. 
  unfold non_trivial. ht.
  apply util.
  assert( (v $! "i")   = n ).
  linear_arithmetic. rewrite H0. trivial.
Qed.

(* The post condition is weakened as per the requirement of the lemma on big step semantics *)
Lemma non_trivial_hoare' (n:nat) (val:nat) : 
hoare_triple (fun q h v => q = nil) (non_trivial n val) (fun q h v => q = gen_out n val).
Proof.
  eapply HtStrengthenPost. 
  eapply non_trivial_hoare. 
  simplify. propositional.
Qed. 


(* The main lemma which proves that the program produces the expected output *)
Theorem non_trivial_ok (n:nat) (val:nat) :
forall tr h v tr' h' v',
    exec tr h v (non_trivial n val) tr' h' v' ->
    tr = nil -> tr' = gen_out n val.
Proof.
   eapply hoare_triple_big_step. eapply non_trivial_hoare'.
Qed.

(*Compute (gen_out 7 3).*)

(* Fib_hoare *)
(* assert(0=0). equality. apply H4 in H2. invert H2. invert H5. invert H3. eexists. eauto.
  eauto.  

  2:{   

   cases (x1 $! "cnt").
  assert(0=0). trivial. apply H in H1. invert H1. invert H4. rewrite H1. rewrite H2. econstructor.


  cases x. 
  assert(False). apply H3. trivial. invert H1.

  simplify. assert( S n0 > 0). linear_arithmetic. apply H0 in H1.
  invert H1. rewrite <- H2. eapply Fsn. rewrite H2. assumption.
}
  
  

2:{  simplify. assert( S n0 > 0). linear_arithmetic. apply H1 in H2.
  invert H2.   
2:{ eapply Fsn. assumption. 
  cases x. 

  

   cases (x1 $! "cnt").
  assert(0=0). trivial. apply H4 in H2. invert H2. invert H5. invert H3. eexists. eauto.
  assert(S n0 > 0). linear_arithmetic. apply H6 in H2. invert H2. invert H3. eexists.
  eauto.
*)


  (*apply Fs1.
  cases (x1 $! "cnt").
  assert (0 = 0). trivial. apply H3 in H1. 
  invert H1. invert H4. 
  rewrite H1. rewrite H2. simplify. constructor.

  simplify. assert( S n0 > 0). linear_arithmetic. apply H5 in H1.
  invert H1. eapply Fsn. assumption. 
  
  cases x. 
  assert(False). apply H1. trivial. invert H2.
  

   cases (x1 $! "cnt").
  assert(0=0). trivial. apply H4 in H2. invert H2. invert H5. invert H3. eexists. eauto.
  assert(S n0 > 0). linear_arithmetic. apply H6 in H2. invert H2. invert H3. eexists.
  eauto.  *)

(*
  ("i" <- 0;;
  "sum" <- 0;;
  {{fun t h v => forall j, j < "i" v $? "sum" = sum_upto i }}
  while "i" < "n" loop
        "sum" <- "sum" +  *["a" + "i"];;
        *["a" + "i"] <- "sum" ;; Output "sum"
    "i" <- "i" + 1
    done )%cmd.

(* Example non_trivial:=
  ( "a" <-- input;;
    "b" <-- input;;
    "c" <-- input;;
    "d" <-- input;;
    *["x"+"0"] <- "a";;
    *["x"+"1"] <- "b";;
    *["x"+"2"] <- "c";;
    *["x"+"3"] <- "d";;
    "i" <- 0;;
    {{fun _ _ _ => True}}
    while "i" < 3 loop
        "j" <- 0;; 
      {{fun _ _ _ => True }}
        while "j" < 3-"i" loop
          when  Less  *["x" + "j" + 1] *["x" + "j" ]  then
            "y" <- *["x" + "j"];;
            *["x" + "j"] <- *["x" + "j" +1];;
            *["x" + "j" + 1] <- "y";;
            "j" <- "j"+1
        else Skip
          done
        done;;
      "i" <- "i" + 1
    done;;
    Output *["x"+"0"];;
    Output *["x"+"1"];;
    Output *["x"+"2"];;
    Output *["x"+"3"]
)%cmd.
*)
(* 
Another non trivial program which was initially tried 
We are verifying the correctness of the program by checking the trace. Note that we are outputing the contents of heap. Thus, we can verify that the program sorted correctly
using the trace itself. We check that the trace produced by the execution of the program is as expected *)

Inductive non_trivial_spec : trace -> Prop :=
| M4s: forall a b c d m1 m2 m3 m4,
    (m1 >= m2) -> (m2 >=m3) -> (m3 >= m4) -> 
    (m1 = a \/ m1 = b \/ m1 = c \/ m1 = d) ->
    (m2 = a \/ m2 = b \/ m2 = c \/ m2 = d) ->
    (m3 = a \/ m3 = b \/ m3 = c \/ m3 = d) ->
    (m4 = a \/ m4 = b \/ m4 = c \/ m4 = d) ->
    non_trivial_spec [Out m4; Out m3 ; Out m2 ;Out m1 ;In d; In c; In b; In a].

Theorem non_trivial_ok:
  forall tr h v tr' h' v',
    exec tr h v non_trivial tr' h' v' ->
    tr = nil ->
    non_trivial_spec tr'.
Proof.
  unfold non_trivial. simplify. ht.
 invert H. invert H5. invert H9. invert H4. invert H8. invert H4. invert H9. invert H4. invert H8. invert H4. invert H9. invert H4. invert H8. invert H4. invert H9. invert H4. simplify.
  invert H8. invert H4. invert H9. invert H4. invert H10. simplify. invert H0.
  invert H8. invert H6. simplify. invert H11. invert H4. invert H10. invert H6. invert H5. invert H11. simplify.
  invert H5. invert H9. invert H13. invert H9. invert H5. simplify. invert H10. invert H7. simplify.
  invert H0. invert H1. simplify. invert H11. simplify. invert H9. simplify. invert H10. invert H5. invert H11. invert H5. invert H10. simplify.
  invert H4. simplify. simplify. invert H12. invert H9. simplify. simplify. 
  invert H13.  simplify. invert H10. invert H5. simplify. invert H10. invert H7. simplify.
  invert H0. invert H1. simplify. invert H11. simplify. invert H9. simplify. invert H10. invert H5. invert H11. invert H5. invert H10. simplify.
  invert H4. simplify. simplify. invert H12. invert H9. simplify. simplify. 


  invert H13.  invert H10. simplify.
  eapply M4s. 

  invert H4. invert H8. invert H4. invert H9. simplify.
  invert H4. invert H8. invert H10. invert H9. invert H6. invert H11. invert H6. invert H10. simplify. invert H0.
  invert H6. simplify. invert H8. invert H5. invert H10. invert H5. invert H9. invert H5. simplify.
  invert H10.  invert H12. invert H9. simplify. simplify.



