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


Definition matrix_transpose_el_on {A : Type} {n m : nat} (i j : int) (mat: Matrix A n m) (tgt: Matrix A m n) : Matrix A m n :=
  tgt.[j,i <- mat.[i,j]].

Fixpoint matrix_transpose_col_on {A : Type} {n m : nat} (ni : nat) (i j : int) (mat : Matrix A n m) (tgt : Matrix A m n) : Matrix A m n :=
  match ni with
  | 0 => matrix_transpose_el_on i j mat tgt
  | S ni' => matrix_transpose_col_on ni' (i - 1%int63) j mat (matrix_transpose_el_on i j mat tgt)
  end.

Fixpoint matrix_transpose_on_helper {A : Type} {n m: nat} (nj : nat) (i j : int) (mat : Matrix A n m) (tgt : Matrix A m n) : Matrix A m n :=
  match nj with
  | 0 => matrix_transpose_col_on (n - 1) i j mat tgt
  | S nj' => matrix_transpose_on_helper nj' i (j - 1%int63) mat (matrix_transpose_col_on (n - 1) i j mat tgt)
  end.

Definition matrix_transpose_on {A : Type} {n m : nat} (mat : Matrix A n m) (tgt : Matrix A m n) :=
  matrix_transpose_on_helper (m - 1) ((vect_length_int mat) - 1%int63) ((vect_length_int (mat.[0%int63] (* Maybe replace with ))) - 1%int63) 





Fixpoint matrix_transpose_on_helper {A : Type} {n m : nat} (ni nj : nat) (i j : int) (mat : Matrix A n m) (tgt : Matrix A m n) : Matrix A m n :=
  match ni,nj  with
  |  0,0 => tgt
  |  0, S nj' => matrix_transpose_on_helper (ni - 1) nj' ((vect_length_int mat) - 1%int63) (j - 1%int63) mat (matrix_transpose_el_on i j mat tgt)
  |  S ni', 0 => matrix_transpose_on_helper (ni') 0 (i - 1%int63) 0 mat (matrix_transpose_el_on i j mat tgt)
  |  S ni', S nj' => matrix_transpose_on_helper ni' nj' (i - 1%int63) (j - 1%int63) mat (matrix_transpose_el_on i j mat tgt)
  end.




  