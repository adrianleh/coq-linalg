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
| vect (arr : array A) {n : nat} {prf : n = BinInt.Z.to_nat(to_Z(length arr))}  :
    Vector A n.

Definition make_vect {A : Type} (arr : array A) : Vector A (BinInt.Z.to_nat(to_Z(length arr))) :=
  @vect _ arr (BinInt.Z.to_nat((to_Z(length arr)))) (eq_refl).


Lemma vect_length_set : forall (A : Type) (arr : array A) (i : int) (a : A), BinInt.Z.to_nat(to_Z(length arr)) = BinInt.Z.to_nat(to_Z(length (arr.[i <- a]))).
Proof.
  intros.
  rewrite length_set.
  reflexivity.
Qed.

Definition example_vector : Vector nat 3 :=
  @vect _ (make 3 3) 3 (eq_refl) .

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
  @vect _ ([| 1 ; 2 ; 3 | 4 : nat |]) 3 eq_refl.

Definition vect_length {A : Type} {n : nat} : Vector A n -> nat :=
  fun v => n.

Theorem t2 : (vect_length example_vector) = (3).
Proof.
  unfold length.
  reflexivity.
Qed.


Definition vec_get {A : Type} {n : nat} (v : Vector A n) (idx : int) : A :=
  match v with
  | vect _ arr => arr.[idx]
  end.


Definition set_lemma (A : Type) (n : nat) (arr: array A) (idx : int) (a : A) :
  BinInt.Z.to_nat(to_Z(length arr)) = BinInt.Z.to_nat(to_Z(length (arr.[idx <- a]))) :=
  match length_set A arr idx a with
  | eq_refl => eq_refl
  end.

Definition set_lemma2 (A : Type) (n : nat) (arr : array A) (idx : int) (a : A) :
  n = BinInt.Z.to_nat(to_Z(length arr)) ->
                      n = BinInt.Z.to_nat(to_Z(length (arr.[idx <- a]))) :=
                                                 match length_set A arr idx a with
                                                 | eq_refl => fun x => x
                                                 end.

Definition vec_set {A : Type} {n : nat} (v : Vector A n) (idx : int) (a : A) : Vector A n :=
  match v with
  | @vect _ arr n prf => @vect _ (arr.[idx<-a]) n (set_lemma2 A n arr idx a prf)
  end.             

Notation "t .[ i ]" := (vec_get t i)
  (at level 2, left associativity, format "t .[ i ]").
Notation "t .[ i <- a ]" := (vec_set t i a)
  (at level 2, left associativity, format "t .[ i <- a ]").

Definition test3 : nat :=
  vec_get( vec_set (example_vector) 0 1 ) 0.

Lemma t3 : test3 = 1.
Proof.
  unfold test3.
  unfold vec_set.
  unfold example_vector.
  simpl.
  unfold set.
  reflexivity.
Qed.


Fixpoint fold_vect_helper {A B : Type} {n: nat} (v : Vector A n) (f : A -> B -> B) (acc : B) (cnt : nat) (idx:int) : B :=
  match cnt with
  | S k => fold_vect_helper v f (f v.[idx] acc) k (idx+1%int63) 
  | O   => acc
  end.
Search "to_int".

Definition fold_vect {A B: Type} {n: nat} (v: Vector A n) (f: A -> B -> B) (base: B) := fold_vect_helper v f base n (0%int63).


Fixpoint zip_with_vect_helper {A B C: Type} {n: nat} (v1: Vector A n) (v2: Vector B n) (f: A -> B -> C) (tgt: Vector C n) (cnt: nat) (idx: int) : Vector C n :=
  match cnt with
  |  0 => tgt
  | S k =>
      let el := f (v1.[idx]) (v2.[idx]) in
      zip_with_vect_helper v1 v2 f (tgt.[idx <- el]) k (idx + 1%int63)
  end.

Definition zip_with_vect {A B C: Type} {n: nat} (v1: Vector A n) (v2: Vector B n) (f: A -> B -> C) (tgt: Vector C n) :=
  zip_with_vect_helper v1 v2 f tgt n (0%int63).

Lemma fold_vect0 : fold_vect (make_vect (make 3 3)) (plus) 0 = 9.
Proof.
reflexivity.
Qed.

Lemma fold_vect1 : fold_vect (make_vect [| 3; 18; 27 | 3: nat |]) (plus) 5 = (18+3+27+5).
Proof.
reflexivity.
Qed.


Search array.
Print array.
