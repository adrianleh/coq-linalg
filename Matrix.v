Require Import Coq.Array.PArray.
Require Import Coq.Numbers.Cyclic.Int63.Int63.
Require ZArith.
From LinAlg Require Export Vector.


Definition Matrix (A: Type) (n m : nat) := Vector (Vector A m) n.



Theorem matrix_on_init : forall {A B C : Type} {n m : nat}
                           (f : A -> B -> C)
                           (m1 : Matrix A n m)
                           (m2 : Matrix B n m), Matrix C n m.
Proof.
  intros.
  destruct m1 eqn:E.
  apply vect with (make
                     (vect_length_int m1)
                     (zip_with_vect_init
                        (vect_default m1)
                        (vect_default m2)
                        f)).
  rewrite length_make.
  rewrite vect_leb_length.
  rewrite E.
  simpl.
  apply prf.
Qed.

Definition matrix_get {A : Type} {n m : nat} (mat : Matrix A n m) (i j : int) : A :=
  mat.[i].[j].

Definition matrix_set {A : Type} {n m : nat} (mat: Matrix A n m)  (i j : int) (a : A) : (Matrix A n m)
  := mat.[i <- (mat.[i].[j <- a])].

Notation "t .[ i , j ]" := (matrix_get t i j)
  (at level 2, left associativity, format "t .[ i , j ]").
Notation "t .[ i , j <- a ]" := (matrix_set t i j a)
  (at level 2, left associativity, format "t .[ i , j <- a ]").

Definition matrix_get_row {A : Type} {n m : nat} (i : int) (mat : Matrix A n m) : Vector A m :=
  mat.[i].


Notation "t .[ i , '_' ]" := (matrix_get_row t i)
                             (at level 2, left associativity, format "t .[ i , '_' ]").

(*Definition matrix_get_col {A : Type} {n m : nat} (i : int) (mat : Matrix A n m) : Vector A n :=
  matrix_get_row (matrix_transpose mat) i.
Notation "t .[ '_' , i ]" := (matrix_get_col t i)
                             (at level 2, left associativity, format "t .[ '_' , i ]"). *)


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
  matrix_transpose_on_helper (m - 1) ((vect_length_int mat) - 1%int63) ((vect_length_int (mat.[0%int63] (* Maybe replace with default *))) - 1%int63) mat tgt.

Fixpoint matrix_mult_single_rc_helper {A : Type} `{F : Field A} {n m l : nat} (ni : nat) (i c1 c2: int) (acc : A) (mat1 : Matrix A n m) (mat2 : Matrix A m l) : A :=
  match ni with
  | 0 => plus acc (mult mat1.[c1, i] mat2.[i, c2])
  | S ni' => matrix_mult_single_rc_helper ni' (i-1%int63) c1 c2 (plus acc (mult mat1.[c1,i] mat2.[i,c2])) mat1 mat2
  end.

Definition matrix_mult_single_rc {A : Type} `{F : Field A} {n m l : nat} (c1 c2 : int) (mat1 : Matrix A n m) (mat2 : Matrix A m l) : A :=
  matrix_mult_single_rc_helper (m-1) ((vect_length_int mat2) - 1%int63) c1 c2 zero mat1 mat2.

Fixpoint matrix_mult_col_on { A : Type} `{F : Field A} {n m l : nat} (ni : nat) (i j :  int) (mat1 : Matrix A n m) (mat2 : Matrix A m l) (tgt : Matrix A n l) : Matrix A n l :=
  match ni with
  | 0 => tgt.[i,j <- (matrix_mult_single_rc i j mat1 mat2)]
  | S ni' => matrix_mult_col_on (ni') (i - 1%int63) j mat1 mat2 (tgt.[i,j <- (matrix_mult_single_rc i j mat1 mat2)])
  end.

Fixpoint matrix_mult_on_helper {A : Type} `{F : Field A} {n m l: nat} (nj : nat) (i j : int) (mat1 : Matrix A n m) (mat2 : Matrix A m l) (tgt : Matrix A n l) : Matrix A n l :=
  match nj with
  | 0 => matrix_mult_col_on (n-1) i j mat1 mat2 tgt
  | S nj' => matrix_mult_on_helper nj' (i-1%int63) j mat1 mat2 (matrix_mult_col_on (n-1) i j mat1 mat2 tgt)
  end.

Definition matrix_mult_on {A : Type} `{F : Field  A} {n m l : nat} (mat1 : Matrix A n m) (mat2 : Matrix A m l) (tgt : Matrix A n l) : Matrix A n l :=
  matrix_mult_on_helper (l - 1) (vect_length_int mat1) (vect_length_int (mat2.[0%int63])) mat1 mat2 tgt.

Fixpoint matrix_add_on_helper {A : Type} `{F : Field A} {n m : nat} (ni : nat) (i : int)
         (mat1 : Matrix A n m) (mat2 : Matrix A n m) (tgt : Matrix A n m) : Matrix A n m :=
  match ni with
  | 0 => tgt.[i <- (mat1.[i] +@ mat2.[i])]
  | S ni' => matrix_add_on_helper ni' (i - 1%int63) mat1 mat2 (tgt.[i <- mat1.[i] +@ mat2.[i]])
  end.

Definition matrix_add_on {A : Type} `{F : Field A} {n m : nat} (mat1 : Matrix A n m) (mat2: Matrix A n m) (tgt: Matrix A n m) : Matrix A n m :=
  matrix_add_on_helper (vect_length mat1 - 1) ((vect_length_int mat1) - 1%int63) mat1 mat2 tgt.

Definition matrix_add {A : Type} `{F : Field A} {n m : nat} (mat1 : Matrix A n m) (mat2: Matrix A n m): Matrix A n m :=
  matrix_add_on mat1 mat2 (matrix_on_init (fun x y => zero) mat1 mat2).


Fixpoint matrix_add_inv_on_helper {A : Type} `{F : Field A} {n m : nat} (ni : nat) (i : int) (mat : Matrix A n m) (tgt : Matrix A n m) : Matrix A n m :=
  match ni with
  | 0 => tgt.[i <- (-@ mat.[i])]
  | S ni' => matrix_add_inv_on_helper ni' (i - 1%int63) mat (tgt.[i <- -@ mat.[i]])
  end.

Definition matrix_add_inv_on {A : Type} `{F : Field A} {n m : nat} (mat : Matrix A n m) (tgt: Matrix A n m) : Matrix A n m :=
  matrix_add_inv_on_helper (vect_length mat - 1) ((vect_length_int mat) - 1%int63) mat tgt.

Definition matrix_sub_on {A : Type} `{F : Field A} {n m : nat} (mat1 : Matrix A n m) (mat2: Matrix A n m) (tgt: Matrix A n m) : Matrix A n m :=
  matrix_add_on mat1 (matrix_add_inv_on mat2 tgt) tgt.

Definition matrix_sub {A : Type} `{F : Field A} {n m : nat} (mat1 : Matrix A n m) (mat2: Matrix A n m) : Matrix A n m :=
  matrix_sub_on mat1 mat2 (matrix_on_init (fun x y => zero) mat1 mat2).

Fixpoint shave_vector_on_helper {A : Type} {n : nat} (v : Vector A (n+1)) (tgt : Vector A n) (ni : nat) (i : int) : Vector A n :=
  let new_tgt := tgt.[i <- v.[i + 1%int63]] in
  match ni with
  | 0 => new_tgt
  | S ni' => shave_vector_on_helper v new_tgt ni' (i-1%int63)
  end.

Definition shave_vector_on {A : Type} {n : nat} (v : Vector A (n+1)) (tgt : Vector A n) : Vector A n := shave_vector_on_helper v tgt (n-1) (vect_length_int v - 1%int63).


Fixpoint grow_vector_on_helper  {A : Type} {n : nat}
                                         (v : Vector A n)
                                         (tgt : Vector A (n + 1))
                                         (ni : nat) (i : int) : Vector A (n+1) :=
  match ni with
  | 0   => tgt.[1%int63 <- v.[0%int63]]
  | S k => grow_vector_on_helper v (tgt.[i+1%int63 <- v.[i]]) (k) (i-1%int63)
  end.


Definition grow_vector_on {A : Type} {n : nat} (v : Vector A n) (a : A) (tgt : Vector A (n + 1)) :=
  grow_vector_on_helper v (tgt.[0%int63 <- a]) n (vect_length_int v - 1%int63).

Fixpoint grow_matrix_on_helper {A : Type} {n m : nat} (ni : nat) (i : int) (top_vec : Vector A (n+1)) (mat : Matrix A (n+1) m) (tgt : Matrix A (n+1) (m+1)) :=
  let new_tgt := tgt.[i <- grow_vector_on (mat.[i]) (top_vec.[i]) (vect_copy (tgt.[0%int63]))] in
    match ni with
    | 0 => new_tgt
    | S ni' => grow_matrix_on_helper ni' (i - 1%int63) top_vec mat new_tgt
    end.

Definition grow_matrix_on {A : Type} {n m : nat} (mat : Matrix A n m)
           (top_vec : Vector A n) (left_vec : Vector A m) (corner_el : A)
           (tgt : Matrix A (n+1) (m+1)) : Matrix A (n + 1) (m + 1) :=
  grow_matrix_on_helper ((n + 1) - 1) ((vect_length_int tgt) - 1%int63)  (grow_vector_on top_vec corner_el _) (grow_vector_on mat left_vec _) tgt.

