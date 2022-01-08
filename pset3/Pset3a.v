Require Import Frap Pset3aSig.

(* The [Prog] datatype defines abstract syntax trees for this language.
 *)

Print Prog.


(* Define [run] such that [run p n] gives the final state
 * that running the program [p] should result in, when the
 * initial state is [n].
 *)
Fixpoint run (p : Prog) (initState : nat) : nat :=
match p with
| Done  => initState
| AddThen a b   => run b (initState+a)
| MulThen a b   => run b (initState*a)
| SetToThen a b => run b a
end.

Theorem run_Example1 : run Done 0 = 0.
Proof.
  simplify. equality.
Qed.

Theorem run_Example2 : run (MulThen 5 (AddThen 2 Done)) 1 = 7.
Proof.
  simplify. equality.
Qed.

Theorem run_Example3 : run (SetToThen 3 (MulThen 2 Done)) 10 = 6.
Proof.
  simplify. equality.
Qed.

(* Define [numInstructions] to compute the number of instructions
 * in a program, not counting [Done] as an instruction.
 *)

(* We will define a utlity function that will be used to compute the number of instructions *)
Fixpoint numinsutil (p: Prog) (count:nat) :nat := 
match p with 
| Done => count
| AddThen a b => numinsutil b (count+1)
| MulThen a b => numinsutil b (count+1)
| SetToThen a b => numinsutil b (count+1)
end.

Definition numInstructions (p : Prog) : nat := numinsutil p 0.

Theorem numInstructions_Example :
  numInstructions (MulThen 5 (AddThen 2 Done)) = 2.
Proof.
  simplify. equality.
Qed.

(* Define [concatProg] such that [concatProg p1 p2] is the program
 * that first runs [p1] and then runs [p2].
 *)
Fixpoint concatProg (p1 p2 : Prog) : Prog := match p1 with 
| Done => p2
| AddThen a b   => AddThen a (concatProg b p2)
| MulThen a b   => MulThen a (concatProg b p2)
| SetToThen a b => SetToThen a (concatProg b p2)
end.

Theorem concatProg_Example :
     concatProg (AddThen 1 Done) (MulThen 2 Done)
     = AddThen 1 (MulThen 2 Done).
Proof.
  simplify. equality.
Qed.

(* Prove that the number of instructions in the concatenation of
 * two programs is the sum of the number of instructions in each
 * program.
 *)

(* We will use the following lemma in the proof for the theorem *)
Lemma util_val: forall (p1: Prog) (v:nat), numinsutil p1 v = v + numinsutil p1 0.
Proof.
  simplify.
  induct p1.
    (* Initial proof based on case by case analysis *)
    
      - simplify. ring.
    - unfold numinsutil. simplify. rewrite IHp1. fold numinsutil. rewrite -> (IHp1 1). linear_arithmetic.
    - unfold numinsutil. simplify. rewrite IHp1. fold numinsutil. rewrite -> (IHp1 1). linear_arithmetic.
    - unfold numinsutil. simplify. rewrite IHp1. fold numinsutil. rewrite -> (IHp1 1). linear_arithmetic.
     
    (* Try to perform proof automation *)
    (* 
      try match goal with 
      | [ |- numinsutil Done = _ ] => simplify; ring
      | _ => unfold numinsutil; simplify; rewrite IHp1; fold numinsutil; rewrite -> (IHp1 1); linear_arithmetic
      end.
    *)     
Qed.


Theorem concatProg_numInstructions
  : forall (p1 p2 : Prog), numInstructions (concatProg p1 p2)
                      = numInstructions p1 + numInstructions p2.
Proof.
  induct p1.
   - simplify. equality.   
   - unfold concatProg. simplify. fold concatProg. unfold numInstructions in IHp1. unfold numInstructions.
     simplify. rewrite (util_val p1 1). rewrite (util_val (concatProg p1 p2) 1). rewrite IHp1. linear_arithmetic.
   - unfold concatProg. simplify. fold concatProg. unfold numInstructions in IHp1. unfold numInstructions.
     simplify. rewrite (util_val p1 1). rewrite (util_val (concatProg p1 p2) 1). rewrite IHp1. linear_arithmetic.
   - unfold concatProg. simplify. fold concatProg. unfold numInstructions in IHp1. unfold numInstructions.
     simplify. rewrite (util_val p1 1). rewrite (util_val (concatProg p1 p2) 1). rewrite IHp1. linear_arithmetic.

(* 
all:   unfold concatProg; simplify; fold concatProg; unfold numInstructions in IHp1; unfold numInstructions;
     simplify; rewrite (util_val p1 1); rewrite (util_val (concatProg p1 p2) 1); rewrite IHp1; linear_arithmetic.
*)
Qed.           


(* Prove that running the concatenation of [p1] with [p2] is
   equivalent to running [p1] and then running [p2] on the
   result. *)
Theorem concatProg_run
  : forall (p1 p2 : Prog) (initState : nat),
    run (concatProg p1 p2) initState =
    run p2 (run p1 initState).
Proof.
    induct p1.
      - simplify. equality.
      - simplify. rewrite (IHp1 (p2) (initState+n)). equality.
      - simplify. rewrite (IHp1 (p2) (initState*n)). equality.
      - simplify. rewrite (IHp1 (p2) (n)). equality.
Qed.

(* Ignore the below lines: *)
(*
Lemma dum: forall (p:Prog), numinsutil p 0 = numInstructions p.
Proof.
  simplify.
  unfold numInstructions. rewrite numInstructions.
  linear_arithmetic.
Admitted.
*)
(* Lemma concatProg_numInstructions
  : forall (p1 p2 : Prog) (v:nat), numinsutil (concatProg p1 p2) v
                      = numinsutil p1 v + numinsutil p2 0.
Proof. 
  induct p1.
    - simplify.
*)
