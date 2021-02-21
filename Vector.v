Require Import Ring.
Require Import Coq.Array.PArray.
Require Import Coq.Numbers.Cyclic.Int63.Int63.
Require ZArith.

Print Ring.
(*
Inductive Vector {A : Type} : A -> Int63.int -> Type :=
| Hello (ar : array A) : (array A) -> Vector A (length ar).
*)                               

Inductive NatHolder : Type :=
| Hello : NatHolder
| Hold (x : nat) : NatHolder.


                                  

Inductive Vector (A : Type) : nat -> Type :=
| vect (arr : array A) : Vector A (BinInt.Z.to_nat(to_Z(length arr))).


Lemma vect_length_set : forall (A : Type) (arr : array A) (i : int) (a : A), BinInt.Z.to_nat(to_Z(length arr)) = BinInt.Z.to_nat(to_Z(length (arr.[i <- a]))).
Proof.
  intros.
  rewrite length_set.
  reflexivity.
Qed.

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

Definition length {A : Type} {n : nat} : Vector A n -> nat :=
  fun v => n.

Theorem t2 : (length example_vector) = (3).
Proof.
  unfold length.
  reflexivity.
Qed.


Definition vec_get {A : Type} {n : nat} (v : Vector A n) (idx : int) : A :=
  match v with
  | vect _ arr => arr.[idx]
  end.


Definition vec_set {A : Type} {n : nat} (v : Vector A n) (idx : int) (a : A) : Vector A n :=
  match v with
  | vect _ arr =>
    match length_set A arr idx a with
    | _ =>
      match vect_length_set A arr idx a with
      | _ => vect _ arr.[idx <- a]
      end
    end
  end.
                          

Fixpoint fold_vec_helper {A B : Type} (v1 : Vector A n) (f : A -> B -> B) (acc : B) (idx : nat) :=
  match idx with
  | S k => fold_vec_helper v1 f (f 
  | O   => 
  end.
  


Fixpoint fold_vec {A B: Type} {n: nat} (v1: Vector A n) (f: A -> B -> B) (acc: B) (idx : nat) :=
  match v1 with
  | (vect _ a) => if eqb idx 0%int63 then f a.[idx%int63] acc
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
