(* No points will be awarded for Theorems/Lemmas using previous Admitted
* Theorems/Lemmas *)

Require Import Frap Pset8Sig.

Set Implicit Arguments.

Hint Constructors subtype.
Check "$<:".
(* 10 points *)
Lemma subtype_refl : forall t1, t1 $<: t1.
Proof.
  simplify.
  induct t1.
  - apply StFun. assumption. assumption.
  - apply StTupleNilNil.
  - apply StTupleCons. assumption. assumption.
Qed.


Lemma subtype_trans_strong: forall t1 t2 t3, (t1 $<: t2 -> t2 $<: t3 -> t1 $<: t3) /\ (t3$<: t2 -> t2$<:t1 -> t3$<:t1).
Proof. 
    induct t1. simplify.
      - simpl. split. simplify. invert H. invert H0. apply StFun. destruct IHt1_1 with (t2:=t1) (t3:=t2). apply H0. assumption. assumption.
      destruct IHt1_2 with (t2:=t0) (t3:=t4). apply H. assumption. assumption.
      simplify. invert H0. invert H. apply StFun. destruct IHt1_1 with (t2:=t1') (t3:=t1'0). apply H. assumption. assumption.
      destruct IHt1_2 with (t2:=t2') (t3:=t2'0). apply H0. assumption. assumption.    
    -   simplify. split. simplify. invert H. assumption. simplify. invert H0. assumption. invert H. apply StTupeNilCons.
    -   simplify.
         split.
         simplify.
        invert H.
        invert H0. 
        apply StTupeNilCons.
        invert H0.  apply StTupeNilCons. apply StTupleCons. destruct IHt1_1 with (t2:=t1) (t3:=t2). apply H. assumption. assumption.
        destruct IHt1_2 with (t2:=t0) (t3:=t4). apply H. assumption. assumption.

        simplify. invert H0. invert H.  apply StTupleCons. destruct IHt1_1 with (t2:=t1') (t3:=t1'0). apply H0. assumption. assumption.
        destruct IHt1_2 with (t2:=t2') (t3:=t2'0). apply H0. assumption. assumption.
Qed.

(* 10 points *)
Lemma subtype_trans : forall t1 t2 t3, t1 $<: t2 -> t2 $<: t3 -> t1 $<: t3.
Proof.
   apply subtype_trans_strong.
Qed.


(******************************************************************************)
(** Progress *)
(******************************************************************************)

(* canonical forms of well-typed values *)

Lemma canonical_Fun_util t1 t2 t': hasty $0 TupleNil t' -> t' $<: Fun t1 t2 -> False.
Proof.
  induct 1; simplify.
  invert H.
  apply IHhasty.
  apply subtype_trans with (t2:=t). assumption. assumption.
Qed.

Lemma canonical_Fun_util_2 e1 e2 t1 t2 t': hasty $0 (TupleCons e1 e2) t' -> t' $<: Fun t1 t2 -> False.
Proof.
  induct 1;simplify.
  invert H1.
apply IHhasty.
  apply subtype_trans with (t2:=t). assumption. assumption.
Qed.





(* 10 points *)
Lemma canonical_Fun v t1 t2 :
  hasty $0 v (Fun t1 t2) ->
  value v ->
  exists x e',
    v = Abs x e'.
Proof.
  simplify.
  invert H.
  - simplify. invert H1. 
  - exists (x). exists(e1). trivial.
  - invert H0.
  - invert H0.
  - invert H0.
     + eexists. eexists. auto.
     + apply canonical_Fun_util in H2. invert H2. assumption.
     +apply canonical_Fun_util_2 with (e1:=e1) (e2:=e2) in H2. invert H2. assumption.
Qed.
    
 
Lemma util_3_1 t1 t2 t': hasty $0 TupleNil t' -> t' $<: TupleTypeCons t1 t2 -> False.
Proof.
  induct 1;simplify.
  invert H.
  apply IHhasty.
  apply subtype_trans with (t2:=t). assumption. assumption.
Qed.

Lemma util_3_2 t1 t2 t' x v: hasty $0 (Abs x v) t' -> t' $<: TupleTypeCons t1 t2 -> False.
Proof.
  induct 1;simplify.
  invert H0.
  apply IHhasty.
  apply subtype_trans with (t2:=t). assumption. assumption.
Qed.


(* 10 points *)
Lemma canonical_TupleCons v t1 t2 :
  hasty $0 v (TupleTypeCons t1 t2) ->
  value v ->
  exists v1 v2,
    v = TupleCons v1 v2 /\
    value v1 /\
    value v2.
Proof.
  simplify.
  invert H.
  - simplify. invert H1.
  - invert H0.
  - invert H0. exists(e1). exists(e2). split. trivial. propositional.
  - invert H0.
  - invert H0.
    + apply util_3_2 with (x:=x) (v:=e1) in H2. invert H2. assumption.
    + apply util_3_1 in H2. invert H2. assumption.
    + exists e1. exists e2. propositional. 
Qed.


Hint Constructors plug step0.
Hint Resolve subtype_refl subtype_trans canonical_Fun canonical_TupleCons.

Lemma util_4_1 e1 e2:exists x e', e1 = Abs x e' -> value e2 -> exists p, step0 (App e1 e2) p.
Proof.
  eexists.
  eexists.
  simplify.
  rewrite H.
  eexists.
  econstructor.
  assumption.
  Unshelve.  
  exact "a".
  exact TupleNil.
Qed. 

Ltac t0 := match goal with
           | [ H : ex _ |- _ ] => invert H
           | [ H : _ /\ _ |- _ ] => invert H
           | [ |- context[_ $+ (?x, _) $? ?y] ] => cases (x ==v y); simplify
           | [ |- context[?x ==v ?y] ] => cases (x ==v y); simplify

           | [ H : step _ _ |- _ ] => invert H
           | [ H : step0 _ _ |- _ ] => invert1 H
           | [ H : hasty _ _ _ |- _ ] => invert1 H
           | [ H : proj_t _ _ _ |- _ ] => invert1 H
           | [ H : plug _ _ _ |- _ ] => invert1 H
           | [ H : subtype _ _ |- _ ] => invert1 H
           | [ H : Some _ = Some _ |- _ ] => invert H
           end; subst.

Ltac t := simplify; subst; propositional; repeat (t0; simplify); try equality. 

Lemma util_4_2_1 t t' t0 n : hasty $0 TupleNil t' ->  t' $<: t0 ->   proj_t t0 n t -> False.
Proof.
  induct 1; simplify.

  invert H.
  invert H0.

  apply IHhasty.
  eauto. assumption.
Qed.  

Lemma util_4_2 e t t' n:  hasty $0 e t' ->  proj_t t' n t ->  value e -> value (Proj e n) \/ (exists e' : exp, step (Proj e n) e'). 
Proof.
  induct 1; simplify.
  t.
  t.
  t.
  invert H2.
  t.
  invert H2.  invert H1.
  right. eexists. eauto.
  eauto.

  invert H2.
  
  invert H2. 
  invert H1.
  apply util_3_2 with (t1:=t) (t2:=t2) in H.
  equality.
  assumption.

    apply util_3_2 with (t1:=t1) (t2:=t2) in H.
    equality.
  assumption.
    
  apply util_4_2_1 with (t':=t') in H1.
  equality.
  assumption.
  assumption.
  
  induct n; simplify; eauto.
Qed. 

(* 10 points *)
Lemma progress : forall e t,
    hasty $0 e t
    -> value e
      \/ (exists e' : exp, step e e').
Proof.
  induct 1; simplify; try equality.

  left. constructor.

  propositional. right. 
  destruct util_4_1 with (e1:=e1) (e2:=e2) in H.  
  apply canonical_Fun in H.
  invert H.
  invert H4.
  econstructor. 
  econstructor. econstructor. econstructor.  
  eapply Beta.
  assumption.
  assumption.

  invert H3. 
  invert H2. 
  right.
  eauto.

  invert H1.
  invert H2.
  right. eauto.

 
  right.
  invert H3.
  invert H2.
  eauto.
  
  left. constructor.
  

  first_order.  
  left. eauto.
  invert H2. right. eauto.
  invert H1. right. eauto.
  invert H1. right. eauto.

  
  first_order.
  apply util_4_2 with (t:=t) (t':=t').
  assumption.   assumption.   assumption. 
  right. invert H1. eauto.
Qed.  


(******************************************************************************)
(** Preservation *)
(******************************************************************************)

(* 10 points *)
Lemma weakening_override : forall V G G' (x : var) (t : V),
    (forall x' t', G $? x' = Some t' -> G' $? x' = Some t')
    -> (forall x' t', G $+ (x, t) $? x' = Some t'
                -> G' $+ (x, t) $? x' = Some t').
Proof.
    simplify.
    cases(x==vx').
    simplify. assumption.
    simplify. apply H. assumption.
Qed.

(* 10 points *)
Lemma weakening : forall G e t,
    hasty G e t
    -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
            -> hasty G' e t.
Proof.
  induct 1; simplify.

    constructor.
    apply H0.
    assumption.

    econstructor.
    apply IHhasty.
    simplify.
    apply weakening_override with (G:=G).
    assumption.
    assumption.

    econstructor.
    apply IHhasty1.
    assumption.
    apply IHhasty2.
    assumption.
  
    econstructor.
    econstructor.
    apply IHhasty1.
    assumption.
    apply IHhasty2.
    assumption.

    
    econstructor.
    apply IHhasty.
    assumption.
    assumption.
    
    econstructor.
    eapply IHhasty.
    assumption.
    assumption.
Qed.

(* 10 points *)
Lemma substitution : forall G x t' e t,
    hasty (G $+ (x, t')) e t ->
    forall e',
      hasty $0 e' t' ->
      hasty G (subst e' x e) t.
Proof.
  induct 1; simplify.

  cases (x0 ==v x).

    simplify.
    invert H.
    eapply weakening.
    eassumption.
    simplify.
    equality.

    simplify.
    constructor.
    assumption.

    cases (x0 ==v x).

    constructor.
    invert e.
    eapply weakening.
    eassumption.
    simplify.
    cases (x0 ==v x).

    simplify.
    assumption.

    simplify.
    assumption.

    constructor.
    eapply IHhasty.
    maps_equal.
    assumption.

    econstructor.
    eapply IHhasty1; equality.
    eapply IHhasty2; equality.

    econstructor.
        
    econstructor.
    econstructor.
    eauto.
    apply subtype_refl.
    econstructor.
    eauto.
    apply subtype_refl.

    econstructor.
    eauto. assumption.

    econstructor.
    eauto. assumption.
Qed.
    

Hint Resolve substitution.

Lemma util_6_1 v t1 t t' x e: hasty $0 v t1 -> hasty $0 (Abs x e) t' -> t' $<: Fun t1 t -> hasty $0 (subst v x e) t.
Proof.  
  simplify.
  induct H0.
  invert H1.
  eapply HtSub with (t':=t2).
  eapply substitution.  
  eassumption.

  
  eapply HtSub with (t':=t1).
  assumption.
  assumption.
  assumption.

  apply IHhasty.
  assumption.   
  trivial.
  trivial.
  apply subtype_trans with (t2:=t0).
  assumption.
  assumption.
Qed.     


Lemma util_6_2 x e v t :  hasty $0 (App (Abs x e) v) t ->hasty $0 (subst v x e) t.
Proof.
  simplify.

  induct H. 
  invert H.
  eapply substitution.  
  eassumption.
  assumption.

  eapply util_6_1.
  eassumption.
  eassumption.
 assumption.
    eapply HtSub.
  eassumption. assumption.
Qed.


Lemma util_6_3 v1 v2 t t' t2:  hasty $0 (TupleCons v1 v2) t' -> t' $<: TupleTypeCons t t2 -> hasty $0 v1 t.
Proof.

  simplify.
  induct H.
  invert H1.
  eapply HtSub with (t':=t1).
  eassumption.
  assumption.
  
  

  apply IHhasty with (v4:=v2).  
  trivial.
  trivial.  
  apply subtype_trans with (t2:=t0).
  assumption.
  assumption.    
Qed. 
  

Lemma util_6_4 v1 v2 t: hasty $0 (Proj (TupleCons v1 v2) 0) t -> hasty $0 v1 t.
Proof.  
  
  simplify.
  induct H.
  invert H0.
  invert H. assumption.

  eapply util_6_3.
  eassumption.
  eassumption.  

  eapply HtSub with (t':=t').
  eapply IHhasty.
  trivial.
Qed.

Lemma util_6_5 v1 v2 t t' t2:  hasty $0 (TupleCons v1 v2) t' -> t' $<: TupleTypeCons t t2 -> hasty $0 v2 t2.
Proof.

  simplify.
  induct H.
  invert H1.
  eapply HtSub with (t':=t0).
  eassumption.
  assumption.
  
  

  apply IHhasty with (v3:=v1).  
  trivial.
  trivial.  
  apply subtype_trans with (t2:=t0).
  assumption.
  assumption.    
Qed. 


Lemma util_6_6 v1 v2 n t: hasty $0 (Proj (TupleCons v1 v2) (S n)) t -> hasty $0 (Proj v2 n) t.
Proof.

  simplify.
  induct H.
  invert H0.
  invert H. 
  eapply HtProj.
  eassumption.
  assumption.


  
  eapply HtProj.
  eapply util_6_5.
  eassumption.
  eassumption.  
  assumption.


  eapply HtSub.
  eapply IHhasty.
  trivial.
Qed. 
  
(* 10 points *)
Lemma preservation0 : forall e1 e2,
    step0 e1 e2
    -> forall t, hasty $0 e1 t
           -> hasty $0 e2 t.
Proof.
  invert 1; simplify.
    
  apply util_6_2.
  assumption.

  apply util_6_4 with (v2:=v2).
  assumption.

   apply util_6_6 with (v1:=v1).
    assumption.
Qed.  

(* 10 points *)
Lemma generalize_plug : forall e1 C e1',
    plug C e1 e1'
    -> forall e2 e2', plug C e2 e2'
                -> (forall t, hasty $0 e1 t -> hasty $0 e2 t)
                -> (forall t, hasty $0 e1' t -> hasty $0 e2' t).
Proof.

  induct 1; simplify.

    invert H.
    apply H0.
    assumption.

    invert H0.
    induct H2.
    econstructor.
    eapply IHplug.
    eassumption.
    assumption.
    eassumption.
    assumption.


    eapply HtSub with (t':=t').
    eapply IHhasty.
    eassumption.
  eassumption.
  eassumption.
  trivial.
  trivial.
  assumption.
  assumption.

  invert H1.
    induct H3.
    econstructor.
    eassumption.
    eapply IHplug.
    eassumption.
    assumption.
    eassumption.


    eapply HtSub with (t':=t').
    eapply IHhasty.
    eassumption.
  eassumption.
  eassumption.
  trivial.
  trivial.
  trivial.
  assumption.
  assumption.
  assumption.

  invert H0.
    induct H2.
    constructor.
    eapply IHplug.
    eassumption.
    assumption.
    assumption.
    assumption.

  eapply HtSub with (t':=t').
    eapply IHhasty.
    eassumption.
  eassumption.
  eassumption.
  trivial.
  trivial.
  assumption.
  assumption.

  invert H1.
    induct H3.
    constructor.
    assumption.
    eapply IHplug.
    eassumption.
    assumption.
    assumption.


  eapply HtSub with (t':=t').
    eapply IHhasty.
    eassumption.
  eassumption.
  eassumption.
  trivial.
  trivial.
  trivial.
  assumption.
  assumption.
  assumption.

  invert H0.
    induct H2.
    econstructor.
    eapply IHplug.
    eassumption.
    assumption.
    eassumption.
    assumption.


    eapply HtSub with (t':=t').
    eapply IHhasty.
    eassumption.
  eassumption.
  eassumption.
  trivial.
  trivial.
  assumption.
  assumption.
Qed.       

(* 10 points *)
Lemma preservation : forall e1 e2,
    step e1 e2
    -> forall t, hasty $0 e1 t
           -> hasty $0 e2 t.
Proof.
    invert 1; simplify.

    eapply generalize_plug with (e1' := e1).
    eassumption.
    eassumption.
    simplify.
    eapply preservation0.
    eassumption.
    assumption.
    assumption.
Qed.



(******************************************************************************)
(** Safety *)
(******************************************************************************)

(* 10 points *)
Theorem safety :
  forall e t,
    hasty $0 e t -> invariantFor (trsys_of e)
                                 (fun e' => value e'
                                            \/ exists e'', step e' e'').
Proof. 
   simplify.

 
    apply invariant_weaken with (invariant1 := fun e' => hasty $0 e' t).

 
    apply invariant_induction; simplify.
    equality.

    eapply preservation.
    eassumption.
    assumption.

    simplify.
    eapply progress.
    eassumption.
Qed.
