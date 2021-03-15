Require Import Coq.Array.PArray.
Require Import Coq.Numbers.Cyclic.Int63.Int63.
Require ZArith.
From LinAlg Require Export Vector.


Definition Matrix (A: Type) (n m : nat) := Vector (Vector A m) n.
(* TODO: Matrix transpose and matrix mult *)

Definition matrix_get {A : Type} {n m : nat} (mat : Matrix A n m) (i j : int) : A :=
  mat.[i].[j].

Definition matrix_set {A : Type} {n m : nat} (mat: Matrix A n m)  (i j : int) (a : A) : (Matrix A n m)
  := mat.[i <- (mat.[i].[j <- a])].

Notation "t .[ i , j ]" := (matrix_get t i j)
  (at level 2, left associativity, format "t .[ i , j ]").
Notation "t .[ i , j <- a ]" := (matrix_set t i j a)
  (at level 2, left associativity, format "t .[ i , j <- a ]").
