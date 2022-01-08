(**
 * PSet 1: Functional Programming in Coq

  This assignment is designed as a file that you should download and complete in a Coq IDE.
  Before doing that, you need to install Coq.  The installation instructions
  are on the course website.
*)

(* 
 Exercise: mult2 [10 points].
 Define a function that multiplies its input by 2.
*)

Let mult2 (x:nat) :nat := 2*x.

(* What is the function's type? *)

(* The type of the function is : "nat -> nat" *)

Print mult2.
(*
  Output:
    mult2 = fun x : nat => 2 * x : nat -> nat 
*)

(*  What is the result of computing the function on 0?  On 3110? *)
Eval compute in mult2 0.
(* Output: "0:nat" *)
Eval compute in mult2 3110.
(*Output: "6220:nat" *)


(* 
  Exercise: xor [10 points].
   Define a function that computes the xor of two [bool] inputs.
   Do this by pattern matching on the inputs.
*)

Let xor (a:bool) (b:bool) :bool :=
match a,b with 
| false,false => false
| false,true => true
| true,false => true
| true,true => false
end.

(* What is the function's type?  *)
(* The type of the function is "bool->bool->bool"  *)
Print xor.
(*
  Output:
    xor = 
    fun a b : bool => if a then if b then false else true else if b then true else false
     : bool -> bool -> bool
*)

(* Compute all four possible combinations of inputs to test your function.  *)
Eval compute in xor false false.
(* Output: "false:bool" *)
Eval compute in xor false true.
(* Output: "true:bool" *)
Eval compute in xor true false.
(* Output: "true:bool" *)
Eval compute in xor true true.
(* Output: "false:bool" *)


(* 
  Exercise: is_none [20 points].
   Define a function that returns [true] if its input is [None], and [false] otherwise.
   Your function's type should be [forall A : Type, option A -> bool].
   That means the function will actually need to take two inputs:
     the first has type [Type], and the second is an option.
   Hint:  model your solution on [is_empty] in the notes for this lecture.
*)

Let is_none (A:Type) (b:option A) :bool :=
match b with 
| None => true
| Some _=> false
end.

Print is_none.
(* The type: "forall A : Type, option A -> bool" *)

(* Verification of definition *)
(* Eval compute in is_none nat None. *)
(* Output: = true : bool *)
(* Eval compute in is_none nat (Some 2). *)
(* Output: = false : bool *)


Require Import List.
Import ListNotations.

(*
   Exercise: double_all [20 points].
   There is a function [map] that was imported by the [Require Import List] command above.
   First, check its type with [Check map].  Explain that type in your own words.
   Second, print it with [Print map].  Note at the end of that which arguments are _implicit_.
   For a discussion of what implicit means, see the notes for this lecture.
   Third, use map to write your own function, which should double (i.e., multiply by 2)
   every value of a list.
   For example, [double_all [0;2;10]] should be [[0;4;20]].
*)

Check map.
(* 
  Output: 
    map
     : forall A B : Type, (A -> B) -> list A -> list B 
*)

(* 
    Map function takes in a function f:A->B and list l1 of type A and returns another list l2 of type B 
  and this is achieved for all types A and B. 
    Thus, for all types A and B, map takes in a function f:A->B and a list of type A  as inputs and outputs a list of type B.
*)

Print map.

(* 
  Output: 
    map = 
      fun (A B : Type) (f : A -> B) =>
        fix map (l : list A) : list B := match l with
                                 | [] => []
                                 | a :: t => f a :: map t
                                 end
     : forall A B : Type, (A -> B) -> list A -> list B 
*)

(*
Arguments A and B are implicit(they are enclosed within square braces). They can be inferred from the types of the arguments to the function.
The first argument f is of type A->B and the second arugment l is of type A.
*)

Definition double_all (a:list nat) :=  ((map mult2) a).

(*Verification of the Definition*)

(* Eval compute in double_all [0;2;10]. *)

(*
  Output:
     = [0; 4; 20]
      : list nat
*)

(* Exercise: sum [20 points]
   Write a function that sums all the natural numbers in a list.
   Implement this two different ways:
   - as a recursive function, using the [Fixpoint] syntax.
   - as a nonrecursive function, using [Definition] and an application of [fold_left].
*)

(* This is the recursive function using [Fixpoint] syntax *)

Fixpoint sum (lst: list nat) :nat :=
match lst with
| [] => 0
| h::t => h+(sum t)
end.

(* This is the non-recursive definition using [fold_left]*)

(* Kindly comment the previous definition of sum and uncomment the following definition if the following definition is to be used *)
(* Definition sum (lst: list nat): nat := fold_left (fun x y => x+y) lst 0. *)

(* Verification of the definition *)
(*
  Eval compute in sum [1;5;7].
  Eval compute in sum [20;40;12;89].
  Eval compute in sum [].
  Eval compute in sum [0].
*)
(* 
  Outputs:
     = 13
     : nat
     = 0
     : nat
     = 0
     : nat
*)

Inductive day : Type :=
  | sun : day
  | mon : day
  | tue : day
  | wed : day
  | thu : day
  | fri : day
  | sat : day.

Definition next_day d :=
  match d with
  | sun => mon
  | mon => tue
  | tue => wed
  | wed => thu
  | thu => fri
  | fri => sat
  | sat => sun
  end.

(* Exercise: thu after wed [20 points].
   State a theorem that says [thu] is the [next_day] after [wed].
   Write down in natural language how you would informally explain
   to a human why this theorem is true.
   ---> Don't skip this "natural language" part of the exercise;
        it's crucial to develop intuition before proceeding.
   Prove the theorem in Coq.
*)
Theorem thu_after_wed: next_day wed = thu.
Proof.
  simpl. trivial.
Qed.
(* 
  Natural language Explanation:
  We have next_day function which provides the case-wise value for each of the 7 days defined in [Inductive day].
  For proving that [next_day] of [wed] is [thu]:
    1.We will find [next_day] of [wed] by applying the function [next_day] to [wed]. // Simpl tactic helps us do this 
    2.We will check/verify that this is [thu] and thus [next_day] of [wed] is thu.  // trivial tactic helps us do this.
*)


(* Exercise: wed before thu [30 points].
   Below is a theorem that says if the day after [d] is [thu], then
   [d] must be [wed].
   Write down in natural language how you would informally explain
   to a human why this theorem is true.
   ---> Don't skip this "natural language" part of the exercise;
        it's crucial to develop intuition before proceeding.
   Prove the theorem in Coq.  To do that, delete the [Abort]
   command, which tells Coq to discard the theorem,
   then fill in your own proof.
*)

Theorem wed_proceeds_thu : forall d : day, next_day d = thu -> d = wed.

(*
  Natural Language Explanation:
  To prove that if [next_day] [d] is [thu], then [d] must be wed:
    1. We will compute the [next_day] [d] for all the days defined in [Inductive day] 
        // introd d.destruct d helps us in verifying the theorem for each of the days by creating a subgoal for each day
    2. We will verify that either 
        [next_day] [d] is either not thu //tactic discriminate helps us with this.
      or [next_day] [d] is thu and [d] is wed. //tactic trivial helps us with this.
 // Note that the simplification of function application([next_day] [d]) is done by discriminate or trivial tactic.

*)
Proof.
intros d. destruct d
; discriminate || trivial. 
Qed.

(*.
  simpl. discriminate.
  simpl. discriminate.
  simpl. discriminate.
  simpl. trivial.
  simpl. discriminate.
  simpl. discriminate.
  simpl. discriminate.
*)

(* Exercise: tl_opt [20 points].
   Define a function [tl_opt] such that [tl_opt lst] return [Some t] if [t] is the tail of [lst],
   or [None] if [lst] is empty.
   We have gotten you started by providing an obviously incorrect definition, below; you should
   replace the body of the function with a correct definition.
*)

Definition tl_opt {A : Type} (lst : list A) : option (list A) := 
 match lst with
| []   => None
| h::t => Some t
end.

(* Verification of Definition: *)
(* Eval compute in tl_opt [1;2;3]. *)
(* Output:  = Some [2; 3] : option (list nat) *)
(* Eval compute in tl_opt []. *)
(* Output: = None : option (list ?A) *)

(* Here is a new tactic: [rewrite x].  If [H: x = e] is an assumption in the
   proof state, then [rewrite H] replaces [x] with [e] in the subgoal being proved.  For example,
   here is a proof that incrementing 1 produces 2: *)

Theorem inc1_is_2 : forall n, n=1 -> (fun x => x+1) n = 2.
Proof.
  intros n n_is_1. rewrite n_is_1. trivial.
Qed.

(* Exercise: tl_opt correct [20 points].
   Using [rewrite], prove the following theorems. For both, first explain in natural language
   why the theorem should hold, before moving on to prove it with Coq. *)

Theorem nil_implies_tlopt_none :
  forall A : Type, forall lst : list A,
  lst = nil -> tl_opt lst = None.

Proof.
intros A lst lst_is_null.
rewrite lst_is_null. simpl. trivial.
Qed.
(*
   Natural Language Explanation:
    Proving "forall A : Type, forall lst : list A,  lst = nil -> tl_opt lst = None" is a straightforward problem:
    We will assume lst=nil(where lst is a list of type A where A is a type)  // the intros helps us in achieving this.
    and will prove tl_opt lst = None
    To prove tl_opt lst = None, we will apply the function tl_opt to the list lst. From the definition of function,
    lst will match with empty list and returns None. // simpl tactics helps in this
    We will check/verify that the output is actually None by comparing it with expected output. // trivial tactic helps in this 
*)
Theorem cons_implies_tlopt_some :
  forall {A : Type} (h:A) (t : list A) (lst : list A),
  lst = h::t -> tl_opt lst = Some t.
Proof.
intros A h t lst lst_is_ht.
rewrite lst_is_ht. simpl. trivial.
Qed.

(* 
  Natural Language Explanation: 
  Proving "forall {A : Type} (h:A) (t : list A) (lst : list A), lst = h::t -> tl_opt lst = Some t." is a straightforward problem:
    We will assume lst=h:t(given that h is of type A and t is a list of type A and A is a type)  // Intros helps us with this.
    and will prove tl_opt lst = Some t.
    We will apply the function tl_opt to the list lst. 
    From the definition of function,
    lst will not match with empty list and will match with h::t and returns Some t . // simpl tactics helps in this
    We will check/verify that the output is actually None by comparing it with expected output. // trivial tactic helps in this 
*)


(*
  Ignore the below statements:

  Let a := simpl mult2 0.
  Print a.
  Let b:= mult2 3110.
  Print b.
  
  Theorem a: mult2 0 = 0.
  Proof.
  auto.
  Qed.

  Print a.

  Theorem b: mult2 3110 = 6220.
  Proof.
  auto.
  Qed.

  Print b.
*)

