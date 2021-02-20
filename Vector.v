Require Import Ring.
Require Import Coq.Array.PArray.
Require Import Coq.Numbers.Cyclic.Int63.Int63.

Print Ring.
(*
Inductive Vector {A : Type} : A -> Int63.int -> Type :=
| Hello (ar : array A) : (array A) -> Vector A (length ar).
*)                               

Inductive NatHolder : Type :=
| Hello : NatHolder
| Hold (x : nat) : NatHolder.

Inductive Vector (A : Type) : int -> Type :=
| vect (arr : array A) : Vector A (length arr).

Definition example_vector : Vector nat 3 :=
  vect _ (make 3 3).

Print example_vector.

Definition test : nat :=
  match example_vector with
  | vect _ ar => get ar 0
  end.

Theorem t1 :  test = 3.
Proof.
  unfold test.
  unfold example_vector.
  unfold make.
  unfold get.
  reflexivity.
Qed.


Definition example_vector2 : Vector nat 3 :=
  vect _ ([| 1 ; 2 ; 3 | 4 : nat |]).

Definition length {A : Type} {n : int} : Vector A n -> int :=
  fun v => n.

Theorem t2 : (length example_vector) = 3.

Show (length example_vector2).

Search array.
Print array.
