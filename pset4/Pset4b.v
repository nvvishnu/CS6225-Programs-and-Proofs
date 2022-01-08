Require Import Frap Pset4bSig.
Require Import OrdersFacts.

(* Before beginning this problem set, please see Pset4bSig.v,
 * which contains the instructions.
 *)

(* For your convenience, we beforehand provide some useful facts about orders.
 * You can skim through the list of theorems by using "Print," or visiting 
 * this page:
 * https://coq.inria.fr/library/Coq.Structures.OrdersFacts.html
 *)
Include (OrderedTypeFacts Pset4bSig).
Include (OrderedTypeTest Pset4bSig).
(* Print OrderedTypeFacts. 
Print OrderedTypeTest. *)

(* Our solution only needs (at most) the following facts from the above libraries.
 * But it is certainly okay if you use facts beyond these! 
 *)
Check eq_lt.
Check eq_sym.
Check lt_eq.
Check lt_not_eq.
Check lt_trans.
Check compare_refl.
Check compare_lt_iff. (* Note that this one can be used with [apply], despite the fact that it
                       * includes an "if and only if" ([<->]) where other theorems use simple
                       * implication ([->]). *)
Check compare_gt_iff.
Check compare_eq_iff.
Check tree_lt.

Theorem insert_member: forall t n, BST t -> member n (insert n t) = true.
Proof.
  simplify.
  induction t.
    - simplify. rewrite compare_refl. equality.
    - simplify. cases (compare n d). 
      + simpl member. rewrite Heq. equality.
      + simplify. rewrite Heq. rewrite IHt1. equality. destruct H.  assumption.
      + simplify. rewrite Heq. rewrite IHt2. equality. destruct H as [a b]. destruct b as [z y]. destruct y as [b m].  assumption.
Qed.

Lemma insert_lt: forall t n d, lt n d-> tree_lt d t -> tree_lt d (insert n t).
Proof.
    simplify.
    induction t.
      - simplify. unfold Singleton. unfold tree_lt. simplify. split. assumption. split. apply I. apply I.   
      - simplify. cases(compare n d0).
          + simplify. unfold tree_lt. simplify. split. rewrite compare_eq_iff in Heq. apply eq_sym in Heq. apply (eq_lt Heq). assumption.
            split. unfold tree_lt in H0. simplify. all: destruct H0 as [a b]; destruct b as [a1 a2]; assumption.
          + simplify. unfold tree_lt. simplify. split. rewrite compare_lt_iff in Heq. unfold tree_lt in H0. simplify. destruct H0. assumption.
            unfold tree_lt in H0. simplify. destruct H0 as [a b]. destruct b as [a1 a2]. split.
            * apply IHt1 in a1. assumption.
            * assumption.
          + simplify. unfold tree_lt. simplify. rewrite compare_gt_iff in Heq. unfold tree_lt in H0. simplify. destruct H0. 
            split.
            * assumption.
            * split.
              -- destruct H1. assumption.
              -- destruct H1. apply IHt2 in H2. assumption.
Qed.

Lemma insert_gt: forall t n d, lt d n -> tree_gt d t -> tree_gt d (insert n t).
Proof.
    simplify.
    induction t.
      - simplify. unfold Singleton. unfold tree_gt. simplify. split. assumption. split. apply I. apply I.    
      - simplify. cases(compare n d0).
          + simplify. unfold tree_gt. simplify. split. rewrite compare_eq_iff in Heq. apply (lt_eq H). assumption.
            unfold tree_lt in H0. destruct H0 as [a1 a2]. destruct a2 as [a3 a4]. simplify. split; assumption.
          + simplify. unfold tree_gt. simplify. split. rewrite compare_lt_iff in Heq. unfold tree_lt in H0. simplify. destruct H0. assumption.
            unfold tree_lt in H0. simplify. destruct H0 as [a b]. destruct b as [a1 a2]. split.
            * apply IHt1 in a1. assumption.
            * assumption.
          + simplify. unfold tree_gt. simplify. rewrite compare_gt_iff in Heq. unfold tree_gt in H0. simplify. destruct H0. 
            split.
            * assumption.
            * split.
              -- destruct H1. assumption.
              -- destruct H1. apply IHt2 in H2. assumption.
Qed.

Theorem insert_ok: forall t n, BST t -> BST (insert n t).
Proof.
  simplify.
  induction t.  
    - simplify. split. apply I. split. simplify. simpl tree_lt. apply I. split. apply I. simpl tree_gt. apply I.
    - simpl BST in H. destruct H as [a0 a1]. destruct a1 as [a2 a3]. destruct a3 as [a4 a5]. simpl BST. cases (compare n d).
        + simpl BST. repeat split; assumption.
        + simplify. split. 
          * apply IHt1 in a0. assumption.
          * split. rewrite compare_lt_iff in Heq.
             -- apply IHt1 in a0. unfold tree_lt. apply insert_lt. assumption. assumption.
             --  split; assumption.
       + simplify. split.
          * assumption. 
          * split. 
            -- assumption.
            -- apply IHt2 in a4. split. assumption. rewrite compare_gt_iff in Heq. apply insert_gt; assumption.
Qed.

Lemma util_5_1: forall d t1, tree_gt d t1 -> tree_gt d (delete_rightmost t1).
Proof.
  simplify.
  induction t1.
      - simplify. assumption.
      - simpl delete_rightmost. destruct H as [a1 a1_1]. destruct a1_1 as [a2 a3]. cases(t1_2).
        + assumption.
        + unfold tree_lt. simpl tree_forall. split. assumption. split. assumption. apply IHt1_2 in a3. assumption.
Qed.

Lemma util_1: forall t, BST t-> BST(delete_rightmost t).
Proof.
  simplify.
  induction t.
    - simplify. apply I.
    - destruct H as [a1 a2]. destruct a2 as [a3 a4]. destruct a4 as [a5 a6]. simpl delete_rightmost. cases t2.
      + assumption.
      + simpl BST. split. assumption. split. assumption. split. apply IHt2 in a5. assumption. apply (util_5_1 d (Node d0 t2_1 t2_2)). assumption.
Qed.   

Lemma util_2_1: forall d t1 t, tree_gt d t1 -> rightmost t1 = Some t -> lt d t.
Proof.
  simplify.
  induction t1.
    - simpl rightmost in H0. invert H0.
    - unfold tree_lt in H.  simpl tree_forall in H. destruct H as [a1 a1_1]. destruct a1_1 as [a2 a3].
      unfold tree_lt in IHt1_2. cases(t1_2).
        + simplify. invert H0. assumption.
        + apply IHt1_2 in a3. assumption. simplify.  assumption.
Qed.
Lemma util_2_2: forall t d t1, lt d t -> tree_lt d t1 -> tree_lt t t1.
Proof.
  simplify.
  induction t1.
    - unfold tree_lt. simplify. apply I.
    - unfold tree_lt. simpl tree_forall. unfold tree_lt in H0. simpl tree_forall in H0. destruct H0. destruct H1. split. 
        +  apply (lt_trans H0). assumption.
        + split. unfold tree_lt in IHt1_1. apply IHt1_1 in H1. assumption.  unfold tree_lt in IHt1_2. apply IHt1_2 in H2. assumption.
Qed.
                      
Lemma util_2: forall t t1, BST t1 -> rightmost t1 = Some t -> tree_lt t (delete_rightmost t1).
Proof.
    simplify. 
    induction t1.
      - simplify. invert H0.
      - simplify. destruct H as [a1 a1_1]. destruct a1_1 as [a2 a2_2]. destruct a2_2 as [a3 a4]. cases(t1_2).
        + invert H0. assumption.
        + unfold tree_lt. simpl tree_forall. split. apply (util_2_1  d (Node d0 t1_2_1 t1_2_2) t). assumption. assumption. split. 
          apply (util_2_2 t d t1_1). apply (util_2_1  d (Node d0 t1_2_1 t1_2_2) t). assumption. assumption. assumption. apply IHt1_2 in a3. assumption. assumption.
Qed.

Lemma util_3_1: forall d t1 t, tree_lt d t1 -> rightmost t1 = Some t -> lt t d.
Proof.
  simplify.
  induction t1.
    - simpl rightmost in H0. invert H0.
    - unfold tree_lt in H.  simpl tree_forall in H. destruct H as [a1 a1_1]. destruct a1_1 as [a2 a3].
      unfold tree_lt in IHt1_2. cases(t1_2).
        + simplify. invert H0. assumption.
        + apply IHt1_2 in a3. assumption. simplify.  assumption.
Qed.

Lemma util_3_2: forall t d t2, lt t d -> tree_gt d t2 -> tree_gt t t2.
Proof.
  simplify.
  induction t2.
    - unfold tree_gt. simplify. apply I.
    - unfold tree_gt. simpl tree_forall. unfold tree_gt in H0. simpl tree_forall in H0. destruct H0. destruct H1. split. 
        +  apply (lt_trans H). assumption.
        + split. unfold tree_gt in IHt2_1. apply IHt2_1 in H1. assumption.  unfold tree_gt in IHt2_2. apply IHt2_2 in H2. assumption.
Qed.

Lemma util_3: forall d t t1 t2, tree_lt d t1 -> tree_gt d t2 -> rightmost t1= Some t -> tree_gt t t2.
Proof.
  simplify.
  induction t1.
     - simplify. invert H1.
     - apply (util_3_1 d (Node d0 t1_1 t1_2) t) in H. apply (util_3_2 t d t2). assumption. assumption. assumption.
Qed.

Lemma util_4_1: forall d t1, tree_lt d t1 -> tree_lt d (delete_rightmost t1).
Proof.
  simplify.
  induction t1.
      - simplify. assumption.
      - simpl delete_rightmost. destruct H as [a1 a1_1]. destruct a1_1 as [a2 a3]. cases(t1_2).
        + assumption.
        + unfold tree_lt. simpl tree_forall. split. assumption. split. assumption. apply IHt1_2 in a3. assumption.
Qed.

Lemma util_4: forall n d t, tree_lt d t -> tree_lt d (delete n t).
Proof.
   simplify.
   induction t.
      - simplify. assumption.
      - unfold tree_lt. simpl tree_forall. destruct H as [a1 a1_1]. destruct a1_1 as [a2 a3]. case(compare n d0).
        + cases (rightmost t1).
          * simpl tree_forall. split. apply (util_3_1 d t1 t). assumption. assumption. split. fold tree_lt. apply (util_4_1 d t1). assumption. assumption.
          * assumption.
        + simpl tree_forall. split. assumption. split. apply IHt1 in a2. assumption. assumption.
        + simpl tree_forall. split. assumption. split. assumption. apply IHt2 in a3. assumption.
Qed.




Lemma util_5: forall n d t, tree_gt d t -> tree_gt d (delete n t).
Proof.
  simplify.
   induction t.
      - simplify. assumption.
      - unfold tree_gt. simpl tree_forall. destruct H as [a1 a1_1]. destruct a1_1 as [a2 a3]. case(compare n d0).
        + cases (rightmost t1).
          * simpl tree_forall. split. apply (util_2_1 d t1 t). assumption. assumption. split. fold tree_lt. apply (util_5_1 d t1). assumption. assumption.
          * assumption.
        + simpl tree_forall. split. assumption. split. apply IHt1 in a2. assumption. assumption.
        + simpl tree_forall. split. assumption. split. assumption. apply IHt2 in a3. assumption.
Qed.

Theorem delete_ok: forall t n, BST t -> BST (delete n t).
Proof.
  simplify.
  induction t.
      - simplify. apply I.
      - destruct H as [a0 a1]. destruct a1 as [a2 a3]. destruct a3 as [a4 a5]. cases(compare n d).
        + simpl delete. rewrite Heq. cases(rightmost t1).
          * simpl BST. split. apply util_1 in a0. assumption. split. apply util_2. assumption. assumption. split. assumption. apply (util_3 d t t1 t2). all: assumption.
          * assumption.
        + simpl delete. rewrite Heq.  simpl BST. split. apply IHt1 in a0. assumption. split. apply (util_4 n d t1). assumption. split. assumption. assumption.
        + simpl delete. rewrite Heq.  simpl BST. split. assumption. split. assumption. split. apply IHt2 in a4. assumption. apply (util_5 n d t2). assumption.
Qed.
            
             
(* Ignore the following lines *)

(*simpl BST. rewrite Heq. cases(t1).
          * simplify. assumption.
          * simpl. cases(t1_2).
            --  equality
          * simplify. assumption.
          * simplify. *)
(* cases(rightmost t1).
            * simplify. apply IHt1 in a0. simpl delete in a0.
        +*)
(*cases(compare n d).
        + induction t1.
            * simplify. simpl BST. assumption.
            * simplify. )


(* OPTIONAL PART! *)
(*Theorem delete_member: forall t n, BST t -> member n (delete n t) = false.
Proof.
Admitted.*)
