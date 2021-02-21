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

Theorem t2 : (length example_vector) = (3%int63).
Proof.
  unfold length.
  reflexivity.
Qed.


Fixpoint fold_vec {A B: Type} {n: int} (v1: Vector A n) (f: A -> B -> B) (acc: B) (idx : int) :=
  match v1 with
  | (vect _ a) => if eqb idx 0%int63 then f a.[idx] acc
                 else fold_vec v1 f (f a.[idx] acc) (idx - 1%int63)
  end.


 

Fixpoint zip_with_vec {A B: Type} {n: int} (v1 v2: Vector A n) (f: A -> A -> B) (tgt: Vector B n) (idx: int) : Vector B n :=
  match (v1, v2, tgt) with
    | (vect _ a1, vect _ a2, vect _ t) =>
      let el := f (a1.[idx]) (a2.[idx]) in
      if eqb idx 0%int63
      then vect _ t.[idx <- el] (* Figure out how to use length_set axiom here *)
      else  zipWithRec v1 v2 (vect _ t.[idx <- el]) (idx - 1%int63)
  end.



Search array.
Print array.
