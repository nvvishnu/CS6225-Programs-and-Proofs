module Bst

type tree =
  | Leaf : tree
  | Node : n:int -> tree -> tree -> tree

val tree_mem : int -> tree -> Tot bool
let rec tree_mem x t =
  match t with
  | Leaf -> false
  | Node n t1 t2 -> x = n || tree_mem x t1 || tree_mem x t2


val tree_forall : p:(int -> Tot bool) -> t:tree ->
            Tot (r:bool{r <==> (forall x. tree_mem x t  ==> p x)})
let rec tree_forall p t =
  match t with
  | Leaf -> true
  | Node n t1 t2 -> p n && tree_forall p t1 && tree_forall p t2

let tree_lt n = tree_forall (fun v -> v < n)
let tree_gt n = tree_forall (fun v -> v > n)

val bst : tree -> Tot bool
let rec bst t =
  match t with
  | Leaf -> true
  | Node n lt rt ->
    bst lt && tree_lt n lt &&
    bst rt && tree_gt n rt

let singleton n = Node n Leaf Leaf

val insert :
  x:int -> t:tree{bst t} ->
  Tot (r:tree{bst r /\
     (forall y. tree_mem y r <==> (tree_mem y t \/ x = y))})
let rec insert x t =
  match t with
  | Leaf -> singleton x
  | Node n t1 t2 -> if x = n then      t
                    else if x < n then Node n (insert x t1) t2
                    else               Node n t1 (insert x t2)

val tree_max : t:tree {Node? t && bst t} -> Tot (ans:int{(forall x. x <> ans && tree_mem x t ==> x <ans) /\ (forall t2.forall v. let t1 = Node v t t2 in (bst t1) ==> ((tree_gt ans t2)/\ not(tree_mem ans t2))) 
/\ tree_mem ans t
(*/\(forall t2.forall v. let t1=Node v t t2 in (bst t1) ==> (v > ans))*)
})
let rec tree_max t  = match t with
 |Node v lt Leaf -> v
 |Node v lt rt -> let ans=tree_max rt in assert(tree_gt v rt);assert(tree_lt v lt );
 assert(tree_lt ans lt);assert(forall x. x <> ans && tree_mem x t ==> x < ans);
 ans
 

(*             assert(forall t2.forall v. let t1 = Node v t t2 in (bst t1) ==> (tree_gt ans t2)/\ not(tree_mem ans t2)); *)

 (* TODO (10 points): Define the function [tree_max] (it finds the largest element in a tree)
 * and refine its type so that the function delete (below, in comments)
 * type-checks.
 *
 * Observe that [tree_max] is a total function that returns an int. Hence, it
 * cannot accept [Leaf] as an argument. In F*, whenever you define a data type, you get boolean discriminators for constructors for free. For example: *)

val root1 : tree -> Tot (option int)
let root1 t = match t with
  | Leaf -> None
  | Node v _ _ -> Some v

val root2 : t:tree{Node? t} -> Tot int
let root2 t = match t with
  | Node v _ _ -> v
(* In the above, [Node?] is a implicitly defined function of type [tree -> bool]
   which returns [true] if the given tree is not a [Leaf]. Since we statically
   know that the given tree is not a [Leaf], we have no [Leaf] case in [root2].
   You may want to use [Node?] in your definition of [tree_max] *)


val delete : x:int -> t:tree{bst t} ->
  Tot (r:tree{bst r /\ not (tree_mem x r)  /\
              (forall y. x <> y ==> (tree_mem y t = tree_mem y r))}) (decreases t)
let rec delete x t = match t with
  | Leaf -> Leaf
  | Node n t1 t2 -> if n = x then
                      match t1, t2 with
                      | Leaf, Leaf -> Leaf
                      | _   , Leaf -> t1
                      | Leaf, _    -> t2
                      | _          -> let y = tree_max t1 in let r = Node y (delete y t1) t2 in 
                                     (*assert(bst r);
                                     assert(Node? t1 && bst t1);
                                     assert(bst t2);
                                     assert(bst (Node x t1 t2));*)
                                     (*tree_max_lemma t1 t2 x;*)
                                   (*assert(x <> y);
                                    assert(not (tree_mem x t2));
                                    assert(not (tree_mem x (delete y t1))); *)
                                    assert(not(tree_mem x r)); 
                                    assert(forall p. x <> p ==> (tree_mem p r) = (tree_mem p r));
                                    r
                    else  if x < n then Node n (delete x t1) t2
                                  else Node n t1 (delete x t2)
(* Once you get the definition of [tree_max] right, all of the following lemmas
   come for free (including the commented out ones*) 

val insert_member : t:tree -> v:int -> Lemma (requires (bst t))
                                    (ensures (tree_mem v (insert v t)))
let insert_member tr v = ()

val insert_ok : t:tree -> v:int -> Lemma (requires (bst t))
                                     (ensures (bst (insert v t)))
let insert_ok tr v = ()

val delete_ok : t:tree -> v:int -> Lemma (requires (bst t))
                                     (ensures (bst (delete v t)))
let delete_ok tr v = ()

val delete_member : t:tree -> v:int -> Lemma (requires (bst t))
                                         (ensures (not (tree_mem v (delete v t))))
let delete_member tr v = ()


val tree_max' : t:tree{Node? t} -> Tot int
let rec tree_max' t = match t with
|Node n _ Leaf -> n
|Node _  _ rt -> tree_max' rt



val delete' : x : int -> t:tree -> Tot tree (decreases t)
let rec delete' x t = match t with
  | Leaf -> Leaf
  | Node n t1 t2 -> if n = x then match (t1, t2) with
                      | (Leaf, Leaf) -> Leaf
                      | (_, Leaf) -> t1
                      | (Leaf, _) -> t2
                      | _ ->
                          let y = tree_max' t1 in
                            Node y (delete' y t1) t2
                    else if x < n then Node n (delete' x t1) t2
                         else Node n t1 (delete' x t2)

val tree_max'_lemma : t:tree -> Lemma (requires(Node?t && bst t)) (ensures (let ans = tree_max' t in (forall x. x <> ans && tree_mem x t ==> x <ans) /\ (forall t2.forall v. let t1 = Node v t t2 in (bst t1) ==> ((tree_gt ans t2)/\ not(tree_mem ans t2))) 
/\ tree_mem ans t
))
let rec tree_max'_lemma t  = match t with
 |Node v lt Leaf -> ()
 |Node v lt rt -> let ans=tree_max' rt in assert(tree_gt v rt); assert(tree_lt v lt); tree_max'_lemma rt; assert(tree_mem (ans) rt); assert(ans > v);
 assert(tree_lt ans lt); assert(tree_mem (ans) t);assert(v<ans);assert(forall x. x<> ans && tree_mem x rt ==> x <ans);assert(forall x. x<> ans && tree_mem x lt ==> x <ans); assert(forall x. x <> ans && tree_mem x t ==> x < ans)


val delete'_correct : x:int -> t:tree -> Lemma (requires (bst t)) (ensures (let z=delete' x t in bst z /\ not (tree_mem x z) /\ (forall y. x <> y ==> (tree_mem y t = tree_mem y z)) )) (decreases t)
let rec delete'_correct x t = 
match t with
 |Leaf -> ()
 |Node n t1 t2 -> if n=x then match(t1,t2) with
                     | (Leaf, Leaf) -> ()
                      | (_, Leaf) -> ()
                      | (Leaf, _) -> ()
                      | _ ->
                          let y = tree_max' t1 in let z= Node y (delete' y t1) t2 in 
                          assert(bst t2); 
                          assert(bst t1);
                          delete'_correct y t1;
                          assert(bst (delete' y t1)); 
                          tree_max'_lemma t1;
                          assert(tree_lt y (delete' y t1));
                          assert(bst z);
                          ()
                    else if x < n then delete'_correct x t1 (* Node n (delete' x t1) t2*)
                         else delete'_correct x t2  (*Node n t1 (delete' x t2)*)

val delete'_ok: t:tree -> v:int -> Lemma (requires(bst t)) (ensures(bst (delete' v t) ))
let delete'_ok tr v = delete'_correct v tr
val delete'_member : t:tree -> v:int -> Lemma (requires (bst t))
                                         (ensures (not (tree_mem v (delete' v t))))
let delete'_member tr v = delete'_correct v tr

(* TODO (20 points): Give an extrinsic proof showing the correctness of
   [delete'] (i.e. show the same properties that were shown for [delete])

	 Hint: in the process you need to write the function [tree_max'] and give an
	 extrinsic proof of correctness for it. You should delete the [assume val
	 tree_max'] when doing that. *)

(*Ignore the following lines *)
(*val tree_max_lemma: t1:tree{Node?t1 &&bst t1} -> t2: tree{bst t2} ->  v:nat ->  Lemma
  (requires (bst (Node v t1 t2)))
(ensures (v > tree_max t1))
let tree_max_lemma t1 t2 v = assert(tree_lt v t1);assert(tree_mem (tree_max t1) t1);()*)
