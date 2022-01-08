(** CS6225 -- Pset4a (120 points) *)

(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 3 *)

Require Import Frap Pset4aSig.

(* Define the identity function [id], which just returns its
 * argument without modification.
 *)
Definition id {A : Type} (x : A) : A := x.

(* [compose] is another higher-order function: [compose g f]
 * applies [f] to its input and then applies [g]. Argument order
 * follows the general convention of functional composition in
 * mathematics denoted by the small circle.
 *)
Definition compose {A B C : Type} (g : B -> C) (f : A -> B)
           (x : A) : C := g(f x).

(* If we map the [id] function over any list, we get the
 * same list back.
 *)
Theorem map_id : forall {A : Type} (xs : list A),
    map id xs = xs.
Proof.
  simplify.
  induction xs.
  - simplify. equality.
  - unfold id. simplify. unfold id in IHxs. rewrite IHxs. equality.
Qed.

(* If we map the composition of two functions over the list,
 * it's the same as mapping the first function over the whole list
 * and then mapping the second function over that resulting list.
 *)
Theorem map_compose : forall {A B C : Type} (g : B -> C) (f : A -> B)
                        (xs : list A),
    map (compose g f) xs = map g (map f xs).
Proof.
  simplify.
  induction xs.
  - simplify. equality.
  - unfold compose. simplify. unfold compose in IHxs. rewrite IHxs. equality.
Qed.

(* Next we can show some classic properties that demonstrate a
 * certain sense in which [map] only modifies the elements of
 * a list, but preserves its structure: [map_length] shows it
 * preserves length, and [map_append] and [map_rev] show that
 * it commutes with [++] and [rev], respectively.
 * For each of [length], [++], and [rev], it doesn't matter
 * whether we apply [map] before the operation or after.
 *)
Theorem map_length : forall {A B : Type} (f : A -> B) (xs : list A),
    length (map f xs) = length xs.
Proof.
  induction xs.
  - simplify. equality.
  - unfold length. simplify. unfold length in IHxs. rewrite IHxs. equality.
Qed.

Theorem map_append : forall {A B : Type} (f : A -> B) (xs ys : list A),
    map f (xs ++ ys) = map f xs ++ map f ys.
Proof.
  induction xs.
    - simplify. equality.
    - unfold append. simplify. unfold append in IHxs. rewrite IHxs. equality.
Qed.


Theorem map_rev : forall {A B : Type} (f : A -> B) (xs : list A),
    map f (rev xs) = rev (map f xs).
Proof.
  induction xs.
      - simplify. equality.
      - simpl map. simpl rev. simplify. rewrite  (map_append (f) (rev xs) ([a])). rewrite IHxs. equality.
Qed.

(* [fold] is a higher-order function that is even more general
 * than [map]. In essence, [fold f z] takes as input a list
 * and produces a term where the [cons] constructor is
 * replaced by [f] and the [nil] constructor is replaced
 * by [z].
 *
 * [fold] is a "right" fold, which associates the binary operation
 * the opposite way as the [left_fold] function that we defined
 * in lecture.
 *)
Fixpoint fold {A B : Type} (b_cons : A -> B -> B) (b_nil : B)
         (xs : list A) : B :=
match xs with
| [] => b_nil
| h::t => b_cons h (fold b_cons  b_nil t)
end.

(* For instance, we should have
     fold plus 10 [1; 2; 3]
   = 1 + (2 + (3 + 10))
   = 16
 *)
Example fold_example : fold plus 10 [1; 2; 3] = 16.
Proof.
  simplify. equality.
Qed.

(* Prove that [map] can actually be defined as a particular
 * sort of [fold].
 *)

  
Definition map_is_fold : forall {A B : Type} (f : A -> B) (xs : list A),
    map f xs = fold (fun x ys => cons (f x) ys) nil xs.
Proof.
  intros.
  induction xs.
    - simplify. equality.
    - simpl. rewrite IHxs. simpl fold. equality.
Qed.
   
(* Since [fold f z] replaces [cons] with [f] and [nil] with
 * [z], [fold cons nil] should be the identity function.
 *)
Theorem fold_id : forall {A : Type} (xs : list A),
    fold cons nil xs = xs.
Proof.
  simplify.
  induction xs.
    - simplify. equality.
    - simpl fold. rewrite IHxs. equality. 
Qed.

(* If we apply [fold] to the concatenation of two lists,
 * it is the same as folding the "right" list and using
 * that as the starting point for folding the "left" list.
 *)

(* We will use this lemma to prove the next theorem *)
Lemma app_nil : forall {A:Type} (lst : list A),
  lst ++ nil = lst.
Proof.
  intros A lst.
  induction lst as [ | h t IH].
  - trivial.
  - simpl. rewrite -> IH. trivial.
Qed.

Theorem fold_append : forall {A : Type} (f : A -> A -> A) (z : A)
                        (xs ys : list A),
    fold f z (xs ++ ys) =
    fold f (fold f z ys) xs.
Proof.
  simplify.
  induction xs.
  - simplify. equality.
  - simpl fold. rewrite IHxs. equality.
Qed.

(* Using [fold], define a function that computes the
 * sum of a list of natural numbers.
 *)
Definition sum (lst:list nat) :nat := fold (fun (x:nat) (y:nat)=> x+y) 0 lst.

(* Note that [simplify] fails to reduce [ sum [1; 2; 3] ].
 * This is due to a quirk of [simplify]'s behavior: because
 * unfolding [sum] does not present an immediate opportunity
 * for reduction (since [fold] will still need to be unfolded
 * to its fixpoint definition, no simplification is performed).
 * A simple remedy is to use the tactic [unfold sum] prior to
 * calling [simplify]. This should come in handy for future proofs
 * involving definitions that use [fold], too.
 *)
Example sum_example : sum [1; 2; 3] = 6.
Proof.
  simpl. equality.
Qed.

(* Using [fold], define a function that computes the
 * conjunction of a list of Booleans (where the 0-ary
 * conjunction is defined as [true]).
 *)
Definition all (lst:list bool) :bool := fold (fun (x:bool) (y:bool) => x && y) true lst.

Example all_example : all [true; false; true] = false.
Proof.  
   simplify. equality.
Qed.

(* The following two theorems, [sum_append] and [all_append],
 * say that the sum of the concatenation of two lists
 * is the same as summing each of the lists first and then
 * adding the result.
 *)
Theorem sum_append : forall (xs ys : list nat),
    sum (xs ++ ys) = sum xs + sum ys.
Proof.
  simplify.
  induction xs.
    - simplify. equality.
    - simpl sum. unfold sum. simpl fold. unfold sum in IHxs. rewrite IHxs. linear_arithmetic.
Qed.

Theorem all_append : forall (xs ys : list bool),
    all (xs ++ ys) = andb (all xs) (all ys).
Proof.
  simplify.
  induction xs.
    - simplify. equality.
    - simpl all. unfold all. simpl fold. unfold all in IHxs. rewrite IHxs. ring.
Qed.

(* Just like we defined [map] for lists, we can similarly define
 * a higher-order function [tree_map] which applies a function on
 * elements to all of the elements in the tree, leaving the tree
 * structure in tact.
 *)
Fixpoint tree_map {A B : Type} (f : A -> B) (t : tree A)
  : tree B := match t with
| Leaf => Leaf
| Node a b c => Node (tree_map f a) (f b) (tree_map f c)
end.

Example tree_map_example :
  tree_map (fun x => x + 1) (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 (Node Leaf 4 Leaf)))
  = (Node (Node Leaf 2 Leaf) 3 (Node Leaf 4 (Node Leaf 5 Leaf))).
Proof.
  simplify. equality.
Qed.

(* [tree_map_flatten] shows that [map]
 * and [tree_map] are related by the [flatten] function.
 *)
Theorem tree_map_flatten : forall {A B : Type} (f : A -> B) (t : tree A),
  flatten (tree_map f t) = map f (flatten t).
Proof.
  simplify.
  induction t.
      - simplify. equality.
      - simpl flatten. rewrite IHt1. rewrite IHt2. rewrite  (map_append f (flatten t1) (d::flatten t2)). simpl map. equality.
Qed.


(* Using [fold], define a function that composes a list of functions,
 * applying the *last* function in the list *first*.
 *)
Definition compose_list {A : Type} (lst: list (A -> A)) (y: A) : A := fold (fun (f:A->A) (y:A) => f y) y (lst).

Example compose_list_example :
  compose_list [fun x => x + 1; fun x => x * 2; fun x => x + 2] 1 = 7.
Proof.
  simplify. equality.
Qed.

(* Show that [sum xs] is the same as converting each number
 * in the list [xs] to a function that adds that number,
 * composing all of those functions together and finally
 * applying that large composed function to [0].
 *)
Theorem compose_list_map_add_sum : forall (xs : list nat),
    compose_list (map plus xs) 0 = sum xs.
Proof.
  simplify.
  induction xs.
    - simplify. equality.
    - unfold compose_list. simplify. unfold compose_list in IHxs. rewrite IHxs. simpl sum. equality.
Qed.


(* Ignore the below lines: *)


(*Lemma util: forall {A B:Type} (zs: list B) (xs: list A) (f: A->B), 
  fold (fun (x : A) (ys : list B) => f x :: ys) zs xs = zs++fold (fun (x : A) (ys : list B) => f x :: ys) [] xs. 
Proof.
  simplify.
  induct xs.
    - simplify. rewrite (app_nil zs). equality.
    - simplify. induction zs.
        ++ simplify. equality.
        ++ simplify. 
  
*) 
(* Lemma fold_id_util : forall {A : Type} (xs: list A) (a:A), 
  fold cons [a] xs = a::xs.
Proof.
  simplify.
  induct xs.
    - simplify. equality.
    - 
*)
