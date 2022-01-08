(** * 6.887 Formal Reasoning About Programs, Spring 2017 - Pset 4 *)

Require Import Frap Pset6Sig.


Theorem increment2_init_turn_ok :
  invariantFor increment2_sys increment2_init_turn_inv.
Proof.
  apply invariant_induction; simplify.
  invert H. invert H0. invert H1.
  unfold increment2_init_turn_inv;simplify.
  simplify.  
  equality.
  invert H0. invert H1.

  unfold increment2_init_turn_inv; simplify.
  equality.

  unfold increment2_init_turn_inv; simplify.
  equality.

  unfold increment2_init_turn_inv; simplify.
  equality.
    
  unfold increment2_init_turn_inv; simplify.
  equality.
  
  unfold increment2_init_turn_inv; simplify.  
  equality.
  
  unfold increment2_init_turn_inv; simplify.  
  equality.
  
  unfold increment2_init_turn_inv; simplify.  
  equality.

  unfold increment2_init_turn_inv; simplify.  
  equality.
  
  unfold increment2_init_turn_inv; simplify.  
  equality.
  
  unfold increment2_init_turn_inv; simplify.  
  invert H0. 
  invert H1.  
Qed.

Theorem increment2_flag_ok:
  invariantFor increment2_sys increment2_flag_inv.
Proof.
  apply invariant_induction; simplify.
  invert H. invert H0. invert H1. 

  eapply Flag_inv;simplify.
  equality.
  equality.
  equality.
  equality.
  equality.
  
  invert H0. invert H1. invert H.
  simplify.

  eapply Flag_inv; simplify; try equality.

  eapply Flag_inv; simplify; try equality.

  simpl flag_false. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0. assumption.
  invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0. assumption. 
  eapply Flag_inv. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0. equality. equality. 
  equality. simpl flag_false. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0. equality.

  simpl flag_false. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. assumption.
  eapply Flag_inv. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0. equality. equality.
  simpl Flag2. equality. simpl flag_false. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0.
  assumption. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0. assumption.
  eapply Flag_inv. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0. equality.
  equality. equality. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0.

  simpl flag_false. assumption. simpl flag_false. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0.
  assumption.

  eapply Flag_inv. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0; equality.
  simpl Flag1. equality. simpl Flag2; equality. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0.
  simpl flag_false; equality. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0.
  simpl flag_false; equality. 
  
  eapply Flag_inv. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0.
  equality. equality. simpl Flag2. equality. simpl flag_false. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0.
  assumption. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0. assumption.

  eapply Flag_inv. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0.
  equality. equality. simpl Flag2. equality. simpl flag_false. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0.
  assumption. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0. assumption.
   
  eapply Flag_inv. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0.
  equality. equality. simpl Flag2. equality. simpl flag_false. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0.
  equality. invert H. invert H0. invert H3. invert H. simpl flag_false in H4. simpl Flag1 in H0. assumption.
  
  eapply Flag_inv. invert H. invert H0. invert H1. simpl flag_false in H4. simpl flag_false in H5. all: try equality.
  simpl flag_false. invert H. invert H0. simpl flag_false in H4. simpl flag_false in H5. invert H1. 
  all:try equality; try assumption. simpl flag_false. invert H1.  all: simpl flag_false;try equality; try assumption. 
  all: invert H;invert H0;simpl flag_false in H4;assumption.
Qed.

Definition contribution_from (pr: increment_program) : nat :=
match pr with 
| UnsetFlag => 1
| Done => 1
| _ =>0
end.
Definition instruction_ok (flag1 flag2 turn: bool) (pr1 pr2: increment_program) (f:bool) :=
match pr1,pr2 with
| SetFlag,SetFlag => flag1  = false /\ flag2 = false
| SetFlag,SetTurn => flag1 = false /\ flag2 = true
| SetFlag,ReadFlag => flag1 = false /\ flag2=true (*/\ turn = f*)
| SetFlag,ReadTurn => flag1 = false /\ flag2=true (*/\ turn = f*)
| SetFlag,Read => flag1 = false /\ flag2=true (*/\ turn = negb f*)
| SetFlag,Write n => flag1 = false /\ flag2=true /\ n =0
| SetFlag,UnsetFlag => flag1 = false /\ flag2=true
| SetFlag,Done => flag1 = false /\ flag2 = false
| SetTurn,SetTurn => flag1 = true /\ flag2 = true
| SetTurn,ReadFlag => flag1 = true /\ flag2=true (*/\ turn = f*)
| SetTurn,ReadTurn => flag1 = true /\ flag2=true (*/\ turn = f*)
| SetTurn,Read => flag1 = true /\ flag2=true (*/\ turn = negb f \/ flag1 = false)*)
| SetTurn,Write n => flag1 = true /\ flag2=true /\ n = 0 (*/\ turn = f*)
| SetTurn,UnsetFlag => flag1 = true /\ flag2= true (*/\ turn = f*)
| SetTurn,Done => flag1 = true /\ flag2 = false (*/\ turn = f*)
| ReadFlag,ReadFlag => flag1 = true /\ flag2=true
| ReadFlag,ReadTurn => flag1 = true /\ flag2=true 
| ReadFlag,Read => flag1 = true /\ flag2=true  /\ turn = negb f 
| ReadFlag,Write n => flag1 = true /\ flag2=true /\ n = 0 /\ turn = negb f 
| ReadFlag,UnsetFlag => flag1 = true /\ flag2= true 
| ReadFlag, Done => flag1 = true /\ flag2 = false 
| ReadTurn,ReadTurn => flag1 = true /\ flag2=true 
| ReadTurn,Read => flag1 = true /\ flag2=true  /\ turn = negb f 
| ReadTurn,Write n => flag1 = true /\ flag2=true /\ n = 0 /\ turn = negb f 
| ReadTurn,UnsetFlag => flag1 = true /\ flag2= true 
| ReadTurn, Done => flag1 = true /\ flag2 = false 
| Read,Read => False
| Read,Write n => False
| Read,UnsetFlag => flag1 = true /\ flag2= true  (*/\ turn = f*)
| Read, Done => flag1= true /\flag2=false
| Write n,Write a => False
| Write n,UnsetFlag => flag1 = true /\ flag2= true /\ n=1
| Write n, Done => flag1= true /\flag2=false /\ n=1
| UnsetFlag,UnsetFlag => flag1 = true /\ flag2= true
| UnsetFlag, Done => flag1= true /\flag2=false
| Done, Done => flag1= false /\ flag2=false
| _,_ => True
end.


Definition program_ok  (s : threaded_state inc_state (increment_program * increment_program)) :=
match s.(Private) with
| (pr1,pr2) => instruction_ok s.(Shared).(Flag1) s.(Shared).(Flag2) s.(Shared).(Turn) pr1 pr2 false 
               /\ instruction_ok s.(Shared).(Flag2) s.(Shared).(Flag1) s.(Shared).(Turn) pr2 pr1 true 
              /\ s.(Shared).(Global) = contribution_from pr1 + contribution_from pr2
end.
Inductive increment2_inv_util : threaded_state inc_state (increment_program * increment_program) -> Prop:=
| Inc2Inv: forall p,
  program_ok p -> increment2_inv_util p.
Lemma Inc2Inv' : forall p,
  program_ok p
  -> increment2_inv_util p.
Proof.
  intros.
  apply Inc2Inv; assumption.
Qed.


Theorem increment2_inv_util_ok: invariantFor increment2_sys increment2_inv_util.
Proof. 
  apply invariant_induction; simplify.

  invert H.
  invert H0.
  invert H1.
  apply Inc2Inv'.

  unfold program_ok.
  simplify.
  equality.


  invert H.
  invert H0.

-  invert H; simplify.

  cases pr2; simplify.

  apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  
    apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.

    apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.

    apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.

      apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.

        apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional. 

        apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.

        apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.

        apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  cases pr2; simplify; try equality.
  cases pr2; simplify; try equality.

  apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  cases pr2; simplify; try equality. propositional. 
  cases pr2; simplify; try equality.

  apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  cases pr2; simplify; try equality.
  cases pr2; simplify; try equality.

    apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  cases pr2; simplify; try equality.
  cases pr2; simplify; try equality.

      apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  cases pr2; simplify; try equality.
  cases pr2; simplify; try equality.

      apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  cases pr2; simplify; try equality.  propositional.
    cases pr2; simplify; try equality.  propositional.

  apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  cases pr2; simplify; try equality.
  cases pr2; simplify; try equality. 
    cases pr2; simplify; try equality. 

    apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  cases pr2; simplify; try equality.
  cases pr2; simplify; try equality. 
-   invert H; simplify.

  cases pr1; simplify.

  apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  
    apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.

    apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.

    apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.

      apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.

        apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional. 

        apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.

        apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.

        apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  cases pr1; simplify; try equality.
  cases pr1; simplify; try equality.

  apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  cases pr1; simplify; try equality. propositional. 
  cases pr1; simplify; try equality.

  apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  cases pr1; simplify; try equality.
  cases pr1; simplify; try equality.

    apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  cases pr1; simplify; try equality.
  cases pr1; simplify; try equality.

      apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  cases pr1; simplify; try equality.
  cases pr1; simplify; try equality.

      apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  cases pr1; simplify; try equality.  propositional.
    cases pr1; simplify; try equality.  propositional.

  apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  cases pr1; simplify; try equality.
  cases pr1; simplify; try equality. 
    cases pr1; simplify; try equality. 

    apply Inc2Inv'; unfold program_ok; simplify.
  invert H1. simplify. propositional.
  cases pr1; simplify; try equality.
  cases pr1; simplify; try equality. 
Qed. 
  
Theorem invariant_weaken : forall {state} (sys : trsys state)
  (invariant1 invariant2 : state -> Prop),
  invariantFor sys invariant1
  -> (forall s, invariant1 s -> invariant2 s)
  -> invariantFor sys invariant2.
Proof.
  unfold invariantFor; simplify.
  apply H0.
  eapply H.
  eassumption.
  assumption.
Qed.
  
Theorem increment2_correct_ok :
  invariantFor increment2_sys increment2_inv.
Proof.
  simplify.
  apply invariant_weaken with (invariant1 := increment2_inv_util); simplify.
  eapply increment2_inv_util_ok.
  unfold increment2_inv.
  simplify.
  invert H; simplify.
  unfold program_ok in H1. simplify. rewrite H0 in H1.
  simplify. equality.
Qed.
