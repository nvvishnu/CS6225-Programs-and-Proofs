(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 7 *)

Require Import Frap Pset9Sig.

(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 7 *)

(** KC: Use can use admitted lemmas in subsequent proofs and 
    get the full points for that proof or lemma. For example,
    you can prove the theorem [validator_ok] towards the end 
    without proving other lemmas and get 5 ponints. *)


Require Import Frap Pset9Sig.

Ltac iffer :=
  match goal with
  | [H : context [if ?e then _ else _] |- _] => cases e; try equality
  end.

Ltac matcher :=
  match goal with
  | [H : context [match ?e with _ => _ end] |- _] => cases e; try equality
  end.

Ltac split_and :=
  match goal with
  | [H : _ && _ = true |- _] => apply andb_true_iff in H; destruct H
  end.

Ltac invert_Some :=
  match goal with
  | [H : Some _ = Some _ |- _] => invert H
  end.

Hint Constructors plug step0 cstep generate.
Hint Resolve peel_cseq.
Scheme Equality for arith.
Scheme Equality for cmd.

Definition sameValuationExcept (v1 v2: valuation) (md: maydiff) :=
  forall x, md $? x = None -> v1 $? x = v2 $? x.

(* 5 points *)
Lemma arithNotReading_ok:
  forall e md v1 v2,
    arithNotReading e md = true ->
    sameValuationExcept v1 v2 md ->
    interp e v1 = interp e v2.
Proof.
  simplify.
  
  induct e; simplify; try iffer; try equality.  

  unfold sameValuationExcept in H0.
  apply H0 in Heq.
  rewrite Heq. trivial.

  split_and. apply IHe1 with (v1:=v1) (v2:=v2) in H. apply IHe2 with (v1:=v1) (v2:=v2) in H0. rewrite H. rewrite H0. trivial. assumption. assumption.
    split_and. apply IHe1 with (v1:=v1) (v2:=v2) in H. apply IHe2 with (v1:=v1) (v2:=v2) in H0. rewrite H. rewrite H0. trivial. assumption. assumption.
    split_and. apply IHe1 with (v1:=v1) (v2:=v2) in H. apply IHe2 with (v1:=v1) (v2:=v2) in H0. rewrite H. rewrite H0. trivial. assumption. assumption.
Qed.

(* 5 points *)
Lemma sameValuationExcept_add:
  forall v1 v2 md x v,
    sameValuationExcept v1 v2 md ->
    md $? x = None ->
    sameValuationExcept (v1 $+ (x, v)) (v2 $+ (x, v)) md.
Proof.
  simplify.
  unfold sameValuationExcept.
    unfold sameValuationExcept in H.
    simplify.
    cases(x==v x0).  
   simplify. trivial.   
    simplify. apply H. assumption.
Qed.

(* 5 points *)
Lemma sameValuationExcept_md_add:
  forall v1 v2 md x v v',
    sameValuationExcept v1 v2 md ->
    sameValuationExcept v1 (v2 $+ (x, v)) (md $+ (x, v')).
Proof.
  simplify.
  unfold sameValuationExcept.
  unfold sameValuationExcept in H.
  simplify.
  cases(x==vx0).
  simplify. invert H0.
 simplify. apply H. assumption.
Qed.
  

Hint Immediate includes_refl.

Check cmd_eq_dec.

(* 2 points *)
Lemma cmd_eq_dec_refl {A} : forall c (t f : A),
    (if cmd_eq_dec c c then t else f) = t.
Proof.

  simplify.
  cases (cmd_eq_dec).  
  trivial.
  equality.
Qed.


Ltac rewrite_cmd_eq_dec_refl :=
  match goal with
  | [H : context[if cmd_eq_dec ?c ?c then _ else _] |- _] => rewrite cmd_eq_dec_refl in H
  end.

(* 5 points *)
Lemma validator_same_true_md:
  forall c md nmd,
    validator' c c md = Some nmd -> md = nmd.
Proof.
  induct c; simplify.

  invert H.

  trivial.

  invert H.

  trivial.

  iffer. matcher. iffer. iffer. matcher. matcher. 

  
  matcher. 
  apply IHc1 in Heq. rewrite <- Heq in H.  apply IHc2. assumption.
  

  iffer. matcher. iffer. matcher.

  

  iffer. iffer. matcher.

  

  iffer. matcher.
Qed.
Hint Resolve validator_same_true_md sameValuationExcept_md_add sameValuationExcept_add arithNotReading_ok.
Ltac dum:= repeat eauto; rewrite_cmd_eq_dec_refl; eauto.

Lemma validator_step0_ok:
  forall c1 c2 md fmd,
    validator' c1 c2 md = Some fmd ->
    forall v1 v2,
      sameValuationExcept v1 v2 md ->
      forall l v1' c1',
        step0 (v1, c1) l (v1', c1') ->
        exists vc2',
          step0 (v2, c2) l vc2' /\
          (exists nmd,
              validator' c1' (snd vc2') nmd = Some fmd /\
              sameValuationExcept v1' (fst vc2') nmd).
Proof.  

  simplify.
  
  induct H1; simplify; try equality; eauto.

  matcher. invert H. eexists. split. econstructor. eexists. simplify. split. trivial. assumption. 
  matcher. iffer. simplify. eexists. split. econstructor. eexists. simplify. split. trivial. invert H. 
  apply sameValuationExcept_md_add. assumption.

  matcher. matcher. matcher. iffer. invert e. invert H.
  eexists. split. econstructor. exists(fmd). simplify. split. trivial.
  unfold sameValuationExcept. simplify.  unfold sameValuationExcept in H0. 
  apply H0. assumption.

  iffer. iffer. iffer. invert e0. invert H.
  eexists. split. econstructor. exists(fmd). simplify. split. trivial.  
  eapply  sameValuationExcept_add. assumption. assumption.
  
  matcher. iffer. iffer. iffer. invert e0. invert H. 
   eexists. split. econstructor. exists(fmd). simplify. split. trivial.  
  unfold sameValuationExcept. simplify. unfold sameValuationExcept in H0. 
  cases(fmd $?x0). simplify. invert Heq0. 
  assert(v1 $? x0 = v2 $? x0).  apply H0. assumption.
  rewrite H1.
   eapply  sameValuationExcept_add. eassumption. eassumption. assumption.

  matcher. iffer. iffer. iffer. invert e0. invert H. 
   eexists. split. econstructor. exists(fmd). simplify. split. trivial.  
  assert(interp e1 v1 = interp e1 v2). eapply arithNotReading_ok. split_and. eassumption. split_and. assumption.
  rewrite H. assert(interp e2 v1 = interp e2 v2). eapply arithNotReading_ok. split_and. eassumption. split_and. assumption.
  rewrite H1.   eapply  sameValuationExcept_add. eassumption. eassumption. 
  
   matcher. iffer. iffer. iffer. invert e0. invert H. 
   eexists. split. econstructor. exists(fmd). simplify. split. trivial.  
  assert(interp e1 v1 = interp e1 v2). eapply arithNotReading_ok. split_and. eassumption. split_and. assumption.
  rewrite H. assert(interp e2 v1 = interp e2 v2). eapply arithNotReading_ok. split_and. eassumption. split_and. assumption.
  rewrite H1.   eapply  sameValuationExcept_add. eassumption. eassumption. 

   matcher. iffer. iffer. iffer. invert e0. invert H. 
   eexists. split. econstructor. exists(fmd). simplify. split. trivial.  
  assert(interp e1 v1 = interp e1 v2). eapply arithNotReading_ok. split_and. eassumption. split_and. assumption.
  rewrite H. assert(interp e2 v1 = interp e2 v2). eapply arithNotReading_ok. split_and. eassumption. split_and. assumption.
  rewrite H1.   eapply  sameValuationExcept_add. eassumption. eassumption. 


  matcher. matcher. matcher.  invert Heq. eexists. split. econstructor. eexists.
  split. simplify. eassumption. assumption.


  matcher. matcher. matcher. matcher. iffer. invert H. invert e1. eexists. split. econstructor. 
  assert(interp e0 v1' = interp e0 v2).
  split_and.  split_and.
  apply arithNotReading_ok with (md:=fmd). assumption. assumption. rewrite <- H. assumption.
   simplify. exists(m). split. 
  assert(fmd=m).
apply validator_same_true_md with (c:=c2_1). assumption. 
rewrite H in Heq. rewrite H. assumption. 
  assert(fmd=m).
apply validator_same_true_md with (c:=c2_1). assumption. 
rewrite <- H. assumption.

  


  matcher. matcher. matcher. iffer. iffer. invert H. invert e1. 
eexists. split. eapply Step0IfFalse. 
  assert(interp e0 v1' = interp e0 v2).
  split_and.  split_and. 
  apply arithNotReading_ok with (md:=fmd). assumption. assumption. rewrite <- H. assumption.
   simplify. exists(m). split. 
  assert(fmd=m).
apply validator_same_true_md with (c:=c2_1). assumption. 
    assert(fmd=m0).
  apply validator_same_true_md with (c:=c2_2). assumption. 
rewrite <- H. rewrite <-  H2 in Heq0. assumption.
    assert(fmd=m).
apply validator_same_true_md with (c:=c2_1). assumption. 
rewrite <- H.
assumption.



  matcher. matcher. iffer. iffer. invert H. invert e1. 
  eexists. split. econstructor.  assert(interp e0 v1' = interp e0 v2).
  apply arithNotReading_ok with (md:=fmd). assumption. assumption. rewrite <- H. assumption.
   simplify. exists(fmd). split. rewrite Heq.
    assert(fmd=m).
  apply validator_same_true_md with (c:=c2).  assumption. rewrite <- H. rewrite Heq.
  Check cmd_eq_dec.
  cases(cmd_eq_dec). rewrite Heq0. trivial. equality. assumption.



  matcher. matcher. iffer. iffer. invert H. invert e1. 
  eexists. split. eapply Step0WhileFalse.  assert(interp e0 v1' = interp e0 v2).
  apply arithNotReading_ok with (md:=fmd). assumption. assumption. rewrite <- H. assumption.
   simplify. exists(fmd). split. trivial. assumption.


  matcher. iffer. iffer. invert e1. invert H.
  assert((interp e0 v1' )= (interp e0 v2)).
  apply arithNotReading_ok with (md:=fmd). assumption. assumption. 
  rewrite H.
  eexists. split. econstructor.
  exists(fmd). simplify. split. trivial. assumption.  

Qed.



(* 5 points *)
Lemma cstep_Sequence:
  forall l v c1 c2 v' c1',
    cstep (v, c1) l (v', c1') ->
    cstep (v, c1 ;; c2) l (v', c1' ;; c2).
Proof.
   simplify.
  
  induct H; simplify; try equality. eauto.
Qed.



(* 20 points *)
Lemma validator_stepc_ok:
  forall C c c1,
    plug C c c1 ->
    forall c2 md fmd,
      validator' c1 c2 md = Some fmd ->
      forall v1 v2,
        sameValuationExcept v1 v2 md ->
        forall v1' c' l,
          step0 (v1, c) l (v1', c') ->
          forall c1',
            plug C c' c1' ->
            exists vc2' : valuation * cmd,
              cstep (v2, c2) l vc2' /\
              (exists nmd,
                  validator' c1' (snd vc2') nmd = Some fmd /\
                  sameValuationExcept v1' (fst vc2') nmd).
Proof.  
  induct 1; simplify.
  
  invert H2. specialize validator_step0_ok. simplify.
  specialize (H2 c c2 md fmd H v1 v2 H0 l v1' c1' H1). simplify.
  invert H2. cases x. destruct H3. invert H3. 
  eexists. propositional.
  2:{ eexists. propositional. eassumption. eassumption. }
  
  econstructor. econstructor. eassumption. econstructor.

   invert H3. matcher. matcher. 
  specialize (IHplug c0_1 md m Heq v1 v2 H1 v1' c'0 l H2 c'1 H8).

  invert IHplug. destruct H3. invert H4. cases x. eexists. propositional.
  eapply cstep_Sequence. eassumption. eexists. propositional. simplify. 
  rewrite H4. assumption. assumption.
Qed.   
  
(* 20 points *)
Lemma validator_ok':
  forall md s t,
    (match validator' s t md with
     | Some _ => True
     | None => False
     end)->
    forall sv tv,
      sameValuationExcept sv tv md ->
      (sv, s) =| (tv, t).
Proof.
  simplify.
apply simulation with 
    (R := fun vc1 vc2 => exists md, (match validator' (snd vc1) (snd vc2) md with
     | Some _ => True
     | None => False
     end /\  sameValuationExcept (fst vc1) (fst vc2) md) ).

  
  simplify. matcher. invert H1. destruct H3. matcher. cases vc1. cases vc2. cases vc1'. 
  invert H2. specialize (validator_stepc_ok C c2 c H9 c0 x m0 Heq0 v v0 H3 v1 c' l H10 c1 H11).
 (* apply simulation with (R:= fun vc1 vc2 => ((fst vc1) = (fst vc2) /\ (snd vc2) = constAssignCodeMotion (snd vc1)). *)
  simplify. invert H. destruct H1. invert H1. eexists. propositional. eassumption. 
  eexists. propositional. rewrite H1. propositional. assumption.


  simplify. invert H1. invert H2. cases c2; try equality.
  simplify. exists md. split. assumption. assumption. 
Qed. 


(* 5 points *)
Theorem validator_ok:
  forall v s t, validator s t = true -> (v, s) =| (v, t).
Proof.
  simplify.
  unfold validator in H. simplify.  
  apply validator_ok' with (md:=$0).
  matcher.
  unfold sameValuationExcept.
  simplify.
  trivial.
Qed.

(* validator_stepc_ok *)
 (*simplify.
  
  
  induct H2. simplify.*)

  (*eexists. split. econstructor. econstructor. invert H0. specialize validator_step0_ok. simplify.
  specialize (H0 c1 c2 md fmd). apply H4 in H0. rewrite H4 in H0. simplify. 
  apply H0 in H4 with (v1:=v1') (v2:= v2) (v1':=v2') (v2':= v3'). . v1' v2). 

 eexists. simplify. split. trivial. assumption. 
  matcher. iffer. simplify. eexists. split. econstructor. eexists. simplify. split. trivial. invert H. 
  apply sameValuationExcept_md_add. assumption.

  matcher. matcher. matcher. iffer. invert e. invert H.
  eexists. split. econstructor. exists(fmd). simplify. split. trivial.
  unfold sameValuationExcept. simplify.  unfold sameValuationExcept in H0. 
  apply H0. assumption.

  iffer. iffer. iffer. invert e0. invert H.
  eexists. split. econstructor. exists(fmd). simplify. split. trivial.  
  eapply  sameValuationExcept_add. assumption. assumption.
  
  matcher. iffer. iffer. iffer. invert e0. invert H. 
   eexists. split. econstructor. exists(fmd). simplify. split. trivial.  
  unfold sameValuationExcept. simplify. unfold sameValuationExcept in H0. 
  cases(fmd $?x0). simplify. invert Heq0. 
  assert(v1 $? x0 = v2 $? x0).  apply H0. assumption.
  rewrite H1.
   eapply  sameValuationExcept_add. eassumption. eassumption. assumption.

  matcher. iffer. iffer. iffer. invert e0. invert H. 
   eexists. split. econstructor. exists(fmd). simplify. split. trivial.  
  assert(interp e1 v1 = interp e1 v2). eapply arithNotReading_ok. split_and. eassumption. split_and. assumption.
  rewrite H. assert(interp e2 v1 = interp e2 v2). eapply arithNotReading_ok. split_and. eassumption. split_and. assumption.
  rewrite H1.   eapply  sameValuationExcept_add. eassumption. eassumption. 
  
   matcher. iffer. iffer. iffer. invert e0. invert H. 
   eexists. split. econstructor. exists(fmd). simplify. split. trivial.  
  assert(interp e1 v1 = interp e1 v2). eapply arithNotReading_ok. split_and. eassumption. split_and. assumption.
  rewrite H. assert(interp e2 v1 = interp e2 v2). eapply arithNotReading_ok. split_and. eassumption. split_and. assumption.
  rewrite H1.   eapply  sameValuationExcept_add. eassumption. eassumption. 

   matcher. iffer. iffer. iffer. invert e0. invert H. 
   eexists. split. econstructor. exists(fmd). simplify. split. trivial.  
  assert(interp e1 v1 = interp e1 v2). eapply arithNotReading_ok. split_and. eassumption. split_and. assumption.
  rewrite H. assert(interp e2 v1 = interp e2 v2). eapply arithNotReading_ok. split_and. eassumption. split_and. assumption.
  rewrite H1.   eapply  sameValuationExcept_add. eassumption. eassumption. 


  matcher. matcher. matcher.  invert Heq. eexists. split. econstructor. eexists.
  split. simplify. eassumption. assumption.


  matcher. matcher. matcher. matcher. iffer. invert H. invert e1. eexists. split. econstructor. 
  assert(interp e0 v1' = interp e0 v2).
  split_and.  split_and.
  apply arithNotReading_ok with (md:=fmd). assumption. assumption. rewrite <- H. assumption.
   simplify. exists(m). split. 
  assert(fmd=m).
apply validator_same_true_md with (c:=c2_1). assumption. 
rewrite H in Heq. rewrite H. assumption. 
  assert(fmd=m).
apply validator_same_true_md with (c:=c2_1). assumption. 
rewrite <- H. assumption.

  


  matcher. matcher. matcher. iffer. iffer. invert H. invert e1. 
eexists. split. eapply Step0IfFalse. 
  assert(interp e0 v1' = interp e0 v2).
  split_and.  split_and. 
  apply arithNotReading_ok with (md:=fmd). assumption. assumption. rewrite <- H. assumption.
   simplify. exists(m). split. 
  assert(fmd=m).
apply validator_same_true_md with (c:=c2_1). assumption. 
    assert(fmd=m0).
  apply validator_same_true_md with (c:=c2_2). assumption. 
rewrite <- H. rewrite <-  H2 in Heq0. assumption.
    assert(fmd=m).
apply validator_same_true_md with (c:=c2_1). assumption. 
rewrite <- H.
assumption.



  matcher. matcher. iffer. iffer. invert H. invert e1. 
  eexists. split. econstructor.  assert(interp e0 v1' = interp e0 v2).
  apply arithNotReading_ok with (md:=fmd). assumption. assumption. rewrite <- H. assumption.
   simplify. exists(fmd). split. rewrite Heq.
    assert(fmd=m).
  apply validator_same_true_md with (c:=c2).  assumption. rewrite <- H. rewrite Heq.
  Check cmd_eq_dec.
  cases(cmd_eq_dec). rewrite Heq0. trivial. equality. assumption.



  matcher. matcher. iffer. iffer. invert H. invert e1. 
  eexists. split. eapply Step0WhileFalse.  assert(interp e0 v1' = interp e0 v2).
  apply arithNotReading_ok with (md:=fmd). assumption. assumption. rewrite <- H. assumption.
   simplify. exists(fmd). split. trivial. assumption.


  matcher. iffer. iffer. invert e1. invert H.
  assert((interp e0 v1' )= (interp e0 v2)).
  apply arithNotReading_ok with (md:=fmd). assumption. assumption. 
  rewrite H.
  eexists. split. econstructor.
  exists(fmd). simplify. split. trivial. assumption.  


  induct 1; simplify.
  econstructor.
  econstructor.
  
  
  invert H0; simplify; try equality.
  invert H. invert H1. eauto. econstructor. 

  eauto.
  econstructor.

  
  eauto.
2:{
  econstructor.
}

  eauto.
  
  eassumption.

  eauto.    
  cases(cmd_eq_dec c1 Skip).  
  rewrite e.
  invert e.
 eapply Step0Seq.
  rewrite e in H0. invert H0.
2: {eauto. }
  
  

  simplify.
  assert(exists vc2',
          step0 (v2, c2) l vc2' /\
          (exists nmd,
              validator' c1' (snd vc2') nmd = Some fmd /\
              sameValuationExcept v1' (fst vc2') nmd)).  

  apply validator_step0_ok with (c1:=c) (md:=md) (v1:=v1).
  assumption. assumption. assumption.
  
  induct H; induct H3.
  assert( exists vc2', step0 (v2, c2) l vc2' /\
          (exists nmd,
              validator' c0 (snd vc2') nmd = Some fmd /\
              sameValuationExcept v1' (fst vc2') nmd)). 
  eapply validator_step0_ok.
  eassumption.
  eassumption.
  eassumption.

  
  
  invert H. destruct H3. cases(x).
  exists (v,c1).
  split. 
  econstructor. econstructor. eassumption. econstructor.
  assumption.
  
  

  
  

  invert H0. matcher. matcher. 
eapply IHplug0.
  

  eexists. cases(vc2').
  eapply IHplug0.

  

  


  
  

  
  2: { eassumption. }
  econstructor.
  econstructor.

  cases(x).   
  exists v c.
  invert H.
  eassumption.
  eassumption.*)

(* validator'_ok *)
(*  simplify. propositional.  
  cases vc2.  
  invert H2; simplify; subst.
  invert H1. matcher. invert H2.

  eapply validator_stepc_ok in H4.
  invert H4. destruct H2. 
  invert H4. destruct H7.
  eexists. propositional. exact H2. 

  eexists. 
2:{ econstructor. }
3:{ eassumption. }
3:{ econstructor. }


split. 2:{
  exact H7. }




invert H4. destruct H7. exact H7. }
induct H2; eauto.

matcher. induct ; eauto.
2:{ 
split. matcher. 

invert H2.  cases x0. simplify. 


   


  invert H4. destruct H2. cases vc2. exact H2. simplify. matcher. 
  simple eapply CStep.
 simple apply plug_cfoldExprs1.
  exact H.
  exact H3.
  simple apply plug_cfoldExprs1.
   exact H4.
  apply cfoldExprs_ok' in H3.
  
  cases vc2. simplify. subst. (* [H2] *)
  info_eauto.
  simplify. trivial.
  equality.

  
    
  simplify.  propositional.
  eexists; propositional.
  cases vc2.
  specialize skip_or_step.
  simplify. specialize (H3 v c). propositional. invert H4. invert H1. matcher. invert Heq. invert H4.
  cases(snd vc1). invert H5. econstructor. econstructor. econstructor.

invert H3.
  simplify. subst. econstructor. econstructor. 2:{ econstructor. } 
  invert Heq.
  econstructor.
  info_eauto.
2:{ eassumption.
  simplify. trivial.
  equality.

    2: { simplify. propositional. matcher.  } (* agree_on_termination *)
  2: { simplify. propositional. } (* R *)
  simplify. propositional. (* one_step *)

  
  (* apply simulation *)
*)
