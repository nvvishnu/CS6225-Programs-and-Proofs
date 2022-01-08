Require Import Frap Pset3bSig.

(* If we [either] an [option] value with [None]
 * on the right, it leaves that value unchanged,
 * (just as if we put the [None] on the left).
 * This is analogous to how appending [nil]
 * on either side of a list leaves it unchanged.
 *)
Print either.

Theorem either_None_right : forall {A} (xo : option A),
    either xo None = xo.
Proof.
  simplify.
  unfold either.
  cases xo; simplify; equality.
Qed.

(* [either] is associative, just like [++].
 *)
Theorem either_assoc : forall {A} (xo yo zo : option A),
    either (either xo yo) zo = either xo (either yo zo).
Proof.
  simplify.
  unfold either.

  (* This was the initial proof that was used that considers each case *)
  (* cases xo.
    - simplify. equality.
    - cases yo; simplify; equality. 
  *)
  (* This proof uses repeat tactic to hanlde multiple matches in the goal *)
  repeat match goal with
    | [ |- context [match ?f with _  => _ end ]] => cases f; simplify; equality
  end.
Qed.

(* [head] should compute the head of a list, that is,
 * it should return [Some] with the first element of
 * the list if the list is nonempty, and [None]
 * if the list is empty.
 *)
Fixpoint head {A} (xs : list A) : option A :=
match xs with
| h::t => Some h
| [] => None
end.

Example head_example : head [1; 2; 3] = Some 1.
Proof.
  simplify. equality.
Qed.

(* The following theorem makes a formal connection
 * between [either] and [++].
 *)
Theorem either_app_head : forall {A} (xs ys : list A),
    head (xs ++ ys) = either (head xs) (head ys).
Proof.
  simplify.
  induct xs.
    - simplify. equality.
    - unfold head. simplify. equality.
Qed.

(* [leftmost_Node] should compute the leftmost node of
 * a tree.
 *
 * Please implement [leftmost_Node] directly using
 * recursion (i.e., pattern matching) on the [tree] argument,
 * without using the [flatten] operation.
 *)
Print tree.
Fixpoint leftmost_Node {A} (t : tree A) : option A := match t with
| Leaf => None
| Node Leaf b c => Some b 
| Node a b c => leftmost_Node a
end.

Example leftmost_Node_example :
    leftmost_Node (Node (Node Leaf 2 (Node Leaf 3 Leaf)) 1 Leaf)
    = Some 2.
Proof.
  simplify. equality.
Qed.

(* Prove that the leftmost node of the tree is the same
 * as the head of the list produced by flattening the tree
 * with an in-order traversal.
 *)
Lemma util1: forall {A}  (h d:A) (a t b:list A), head(a++h::t) = head((a++h::t)++(d::b)).
Proof.
  simplify.
  induct a.
    - simplify. equality.
    - simplify. equality.
Qed.
Theorem leftmost_Node_head : forall {A} (t : tree A),
      leftmost_Node t = head (flatten t).
Proof.
  induct t.
    - unfold leftmost_Node. unfold head. simplify. equality.
    - cases t1.
        + simplify. equality.  
        + simplify. rewrite -> IHt1. simplify. rewrite (util1 (d0) (d) (flatten t1_1) (flatten t1_2) (flatten t2)). equality.
Qed.

(* Now let's work with the binary tries we defined earlier!
 *
 * Define [lookup] such that [lookup k t] looks up the
 * map entry corresponding to the key [k : list bool] in the
 * binary trie [t : binary_trie A], interpreting [t] such that
 * the value at the root of [t] corresponds to the
 * entry for the key [nil], the left subtree contains entries
 * for those keys that begin with [true], and the right subtree
 * contains entries for those keys that begin with [false].
 *)
Print binary_trie.
Fixpoint lookup {A} (k : list bool) (t : binary_trie A) : option A := match t with
| Leaf => None
| Node a b c => (
                match k with
                | [] => b
                | true::t => lookup t a
                | false::t => lookup t c
              end
          )
end.

Example lookup_example1 : lookup [] (Node Leaf (None : option nat) Leaf) = None.
Proof.
    simplify. equality.
Qed.

Example lookup_example2 : lookup [false; true]
    (Node (Node Leaf (Some 2) Leaf) None (Node (Node Leaf (Some 1) Leaf) (Some 3) Leaf))
                          = Some 1.
Proof.
  simplify. equality.
Qed.


(* [Leaf] represents an empty binary trie, so a lookup for
 * any key should return [None].
 *)
Theorem lookup_empty {A} (k : list bool)
  : lookup k (Leaf : binary_trie A) = None.
Proof.
    unfold lookup. cases k; equality. 
Qed.


(* Define an operation to "insert" a key and optional value
 * into a binary trie. The [insert] definition should satisfy two
 * properties: one is [lookup_insert] below, which says that if we
 * look up a key [k] in a trie where [(k, v)] has just been inserted,
 * the result should be [v]. The other is that lookups on keys different
 * from the one just inserted should be the same as on the original map.
 *
 * If an entry for that key already exists, [insert] should replace
 * that entry with the new one being inserted. Note that [insert] can
 * be used to remove an entry from the trie, too, by inserting [None]
 * as the value.
 *
 * Hint: it may be helpful to define an auxiliary function that inserts
 * a key and optional value into the empty trie.
 *)


Fixpoint insert_util {A} (k: list bool) (v:option A): tree (option A) := 
match k with 
| [] => Node Leaf v Leaf
| true::t => Node (insert_util t v) v Leaf
| false::t => Node Leaf v (insert_util t v)
end.

Fixpoint insert {A} (k : list bool) (v : option A) (t : binary_trie A)
  : binary_trie A :=
match k with
| [] => (
          match t with
           | Leaf => insert_util k v
           | Node a b c => Node a v c
          end
        )
| true::p => (
                match t with
                 | Leaf => insert_util k v
                 | Node a b c => Node (insert p v a) b c 
                end
             )              
| false::p => (
                match t with
                 | Leaf => insert_util k v
                 | Node a b c => Node a b (insert p v c)
                end
             )    
end.
(*match t with 
| Leaf         =>  insert_util k v
| Node a b c   =>  (
                      
                  )
end.*)

Example insert_example1 : lookup [] (insert [] None (Node Leaf (Some 0) Leaf)) = None.
Proof.
  simplify.
  equality.
Qed.
    

Example insert_example2 : lookup [] (insert [true] (Some 2) (Node Leaf (Some 0) Leaf)) = Some 0.
Proof.
  simplify.
  equality.
Qed.

(* We will be using this lemma to prove the following theorem *)
Lemma lookup_insertutil {A} (k: list bool) (v: option A) : lookup k (insert_util k v) = v.
Proof.
   induct k.
    - simplify. equality.
    - simplify. cases (a); equality.
Qed.
         
Theorem lookup_insert {A} (k : list bool) (v : option A) (t : binary_trie A)
  : lookup k (insert k v t) = v.
Proof.
  induct k.
  - simplify. cases t; equality.
  - induct a.
      + simplify. cases t. 
          * apply lookup_insertutil.
          * rewrite (IHk (v) (t1)). equality.
      +  simplify. cases t.
         * apply lookup_insertutil.
         * rewrite (IHk (v) (t2)). equality.
Qed.


(* You've reached the end of the problem set. Congrats!
 *
 * If you're up for a completely optional additional challenge,
 * try defining a left-biased merge function below that merges two
 * binary tries, preferring map entries from the first binary trie
 * when an entry exists for both binary tries. Then prove
 * [lookup_left_biased_merge], which formally states that lookups
 * on the merged binary trie operate in exactly this manner.
 *
 * If you don't want to complete this additional challenge, you
 * can just leave everything below unmodified.
 *)

Fixpoint left_biased_merge {A} (t t' : binary_trie A) : binary_trie A.
Admitted.

Theorem lookup_left_biased_merge {A} (k : list bool) (t t' : binary_trie A)
  : lookup k (left_biased_merge t t') = either (lookup k t) (lookup k t').
Proof.
Admitted.

(* Ignore the below lines: *)
(* Lemma leftmost_Node_1: forall {A} (a c : tree A) (b: A), leftmost_Node (Node a b c) = leftmost_Node a.
Proof. *)
  
(* Print flatten.
Print head.
 Lemma util : forall {A} (a c: tree A) (b: A), head(flatten (Node a b c)) = head(flatten(a)).
Proof.
  simplify.
  induct a.
  - simplify. 
*)