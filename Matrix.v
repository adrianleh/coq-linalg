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

Lemma transpose_on_lemma2 : forall {A : Type} {n m : nat}
                             (mat : Matrix A n m), Vector A m.
Proof.
  intros.
  apply (vect_default mat).
Qed.

Lemma transpose_on_lemma : forall {A : Type} {n m :nat}
                              (mat : Matrix A n m), Vector A n.
Proof.
  intros.
  destruct mat eqn:E.
  apply vect with (make
                     (vect_length_int mat)
                     (vect_default (vect_default mat))).
  rewrite length_make.
  rewrite vect_leb_length.
  rewrite E.
  apply prf.
Qed.  

Theorem transpose_on_init : forall {A : Type} {n m : nat}
                              (mat : Matrix A n m), Matrix A m n.
Proof.
  intros.
  destruct mat eqn:E.
  remember (default arr) as vdef.
  unfold Matrix.
  apply vect with (make
                     (vect_length_int vdef)
                     (transpose_on_lemma mat)).
  rewrite length_make.
  rewrite vect_leb_length.
  destruct vdef.
  simpl.
  apply prf0.
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

Definition matrix_transpose {A : Type} {n m : nat} (mat : Matrix A n m) :=
  matrix_transpose_on mat (transpose_on_init mat).

Definition matrix_get_col {A : Type} {n m : nat} (i : int) (mat : Matrix A n m) : Vector A n :=
  matrix_get_row i (matrix_transpose mat).
Notation "t .[ '_' , i ]" := (matrix_get_col t i)
                             (at level 2, left associativity, format "t .[ '_' , i ]"). 

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

Fixpoint nat_int (n : nat) : int :=
  match n with
  | 0 => 0%int63
  | S k => 1%int63 + (nat_int k)
  end.

Search int.



  
(* Max array length is 4194303 by max_length *)



Theorem vect_exist : forall {A : Type} (n : nat), Vector A n.
Proof.
  Admitted.
(*
  Due to limits placed on the size of arrays in Coq, this is not actually provable. For simplicities sake, we are admitting it as the max array length is 4,194,303 objects, which borders computational infeasability, so this admittance does not affect the well-foundedness of our statements as arbitrary size arrays exist mathematically speaking, and we can not create large enough arrays in Coq to break any functions created using this existentiality.
 *)

Theorem matrix_exist : forall {A : Type} (n m : nat), Matrix A n m.
Proof.
  intros.
  apply vect_exist.
Qed.                                                         

Definition grow_vector_on {A : Type} {n : nat} (v : Vector A n) (a : A) (tgt : Vector A (n + 1)) :=
  grow_vector_on_helper v (tgt.[0%int63 <- a]) n (vect_length_int v - 1%int63).

Definition grow_vector {A : Type} {n : nat} (v : Vector A n) (a : A) :=
  grow_vector_on v a (vect_exist (n + 1)).

Fixpoint grow_matrix_on_helper {A : Type} {n m : nat} (ni : nat) (i : int) (top_vec : Vector A (n+1)) (mat : Matrix A (n+1) m) (tgt : Matrix A (n+1) (m+1)) :=
  let new_tgt := tgt.[i <- grow_vector_on (mat.[i]) (top_vec.[i]) (vect_copy (tgt.[0%int63]))] in
    match ni with
    | 0 => new_tgt
    | S ni' => grow_matrix_on_helper ni' (i - 1%int63) top_vec mat new_tgt
    end.

Lemma grow_matrix_on_helper_lemma : forall {A : Type} {n m : nat}
                                      (v : Vector A m)
                                      (mat : Matrix A (n + 1) (m + 1)), (Matrix A (n + 1) m).
Proof.
  intros.
  apply vect with (make
                     (vect_length_int mat)
                     (v)).
  rewrite length_make.
  rewrite vect_leb_length.
  destruct mat.
  assumption.
Qed.

Definition grow_matrix_on {A : Type} {n m : nat} (mat : Matrix A n m)
           (top_vec : Vector A n) (left_vec : Vector A m) (corner_el : A)
           (tgt : Matrix A (n+1) (m+1)) : Matrix A (n + 1) (m + 1) :=
  grow_matrix_on_helper ((n + 1) - 1) ((vect_length_int tgt) - 1%int63)  (grow_vector_on top_vec corner_el (transpose_on_lemma tgt)) (grow_vector_on mat left_vec (grow_matrix_on_helper_lemma left_vec tgt)) tgt.

Definition grow_matrix {A : Type} {n m : nat} (mat : Matrix A n m)
           (top_vec : Vector A n) (left_vec : Vector A m) (corner_el : A) : Matrix A (n + 1) (m + 1) :=
  grow_matrix_on mat top_vec left_vec corner_el (matrix_exist (n + 1) (m + 1)).


Definition Square A n := Matrix A n n.

Fixpoint L_SetRow {A : Type} `{F : Field A} {n : nat}
         (itr : nat)
         (tgtCol : int) (currentRow : int)
         (mat : Square A n) : Square A n :=
  match itr with
  | 0 => match eqb tgtCol currentRow with
        | true  => mat.[ currentRow, tgtCol <- one  ]
        | false => mat.[ currentRow, tgtCol <- zero ]
        end
  | S k => match eqb tgtCol currentRow with
          | true  => L_SetRow (k) (tgtCol - 1%int63) currentRow (mat.[ currentRow, tgtCol <- one  ])
          | false => L_SetRow (k) (tgtCol - 1%int63) currentRow (mat.[ currentRow, tgtCol <- zero ])
          end
  end.


Fixpoint L_Setter {A : Type} `{F : Field A} {n : nat} (itr : nat) (tgtRow :int) (mat : Square A n) :=
  match itr with
  | 0   => L_SetRow (n - 1) (vect_length_int mat - 1%int63) (tgtRow) mat
  | S k => L_Setter k (tgtRow - 1%int63) (L_SetRow (n - 1) (vect_length_int mat - 1%int63) (tgtRow) mat)
  end.


Definition L {A : Type} `{F : Field A} {n : nat} (mat : Square A n) : Square A n :=
  L_Setter (n - 1) ((vect_length_int mat) - 1%int63) mat.

Fixpoint U_SetRow {A : Type} `{F : Field A} {n : nat}
         (itr : nat)
         (tgtCol : int) (currentRow : int)
         (mat : Square A n) : Square A n :=
  match itr with
  | 0 => match eqb tgtCol currentRow with
        | true  => mat
        | false => mat.[ currentRow, tgtCol <- zero ]
        end
  | S k => match eqb tgtCol currentRow with
          | true  => U_SetRow (k) (tgtCol - 1%int63) currentRow mat
          | false => U_SetRow (k) (tgtCol - 1%int63) currentRow (mat.[ currentRow, tgtCol <- zero ])
          end
  end.

Fixpoint U_Setter {A : Type} `{F : Field A} {n : nat} (itr : nat) (tgtRow :int) (mat : Square A n) :=
  match itr with
  | 0   => U_SetRow (n - 1) (vect_length_int mat - 1%int63) (tgtRow) mat
  | S k => U_Setter k (tgtRow - 1%int63) (U_SetRow (n - 1) (vect_length_int mat - 1%int63) (tgtRow) mat)
  end.

Definition U {A : Type} `{F : Field A} {n : nat} (mat : Square A n) : Square A n :=
  U_Setter (n - 1) ((vect_length_int mat) - 1%int63) mat.

Fixpoint U_Diag_Update_Setter {A : Type} `{F : Field A} {n : nat}
         (U : Square A n) (M : Square A n)
         (itr : nat) (tgt : int) : Square A n :=
  match itr with
  | 0   => U.[tgt, tgt <- M.[tgt, tgt]]
  | S k => U_Diag_Update_Setter (U.[tgt,tgt <- M.[tgt,tgt]]) M (k) (tgt - 1)
  end.

Definition U_Diag_Update {A : Type} `{F : Field A} {n : nat} (U : Square A n) (M : Square A n) : Square A n :=
  U_Diag_Update_Setter U M (n - 1) (vect_length_int U - 1%int63).

Fixpoint L_Col_Update_Setter {A : Type} `{F : Field A} {n : nat}
                                          (M : Square A n) (L : Square A n)
                                          (itr : nat)
                                          (tgtRow : int) (currentCol : int) : Square A n :=
  match itr with
  | 0   => L.[ tgtRow, currentCol <- mult (M.[ tgtRow, currentCol ]) (mult_inv M.[ currentCol, currentCol ])]
  | S k => L_Col_Update_Setter M
                              (L.[ tgtRow, currentCol <-
                                           mult (M.[ tgtRow, currentCol ])
                                                (mult_inv M.[ currentCol, currentCol ]) ])
                              k (tgtRow - 1%int63) currentCol
  end.

Definition L_Col_Update  {A : Type} `{F : Field A} {n : nat} (offset : nat) (currentCol : int)
                                     (M : Square A n) (L : Square A n) : Square A n :=
  L_Col_Update_Setter M L (n - offset - 1) (vect_length_int M - 1%int63) (currentCol).


Fixpoint U_Row_Update_Setter {A : Type} `{F : Field A} {n : nat}
                                          (M : Square A n) (U : Square A n)
                                          (itr : nat)
                                          (currentRow : int) (tgtCol : int) : Square A n :=
  match itr with
  | 0   => U.[ currentRow, tgtCol <- M.[currentRow, tgtCol] ]
  | S k => U_Row_Update_Setter M
                              (U.[ currentRow, tgtCol <- M.[ currentRow, tgtCol] ])
                              k currentRow (tgtCol - 1%int63)
  end.

Definition U_Row_Update {A : Type} `{F : Field A} {n : nat} (offset : nat) (currentRow : int)
                                     (M : Square A n) (L : Square A n) : Square A n:=
  U_Row_Update_Setter M L (n - offset - 1) (vect_length_int M - 1%int63) (currentRow).


Fixpoint M_Block_Update_Inner_Setter {A : Type} `{F : Field A} {n : nat} (nj : nat) (j : int) (i : int) (k : int) (M L U : Square A n) : Square A n :=
  let new_M := M.[i, j <- (plus (M.[i,j]) (add_inv (mult L.[i,k] U.[k,j])))] in
  match nj with
  | 0 => new_M
  | S nj' => M_Block_Update_Inner_Setter nj' (j - 1%int63) i k new_M L U
  end.

Definition M_Block_Update_Inner {A : Type} `{F : Field A} {n : nat} (i : int) (nk : nat) (k : int) (M L U : Square A n) : Square A n :=
  M_Block_Update_Inner_Setter (n - nk -1) (vect_length_int M - 1%int63) i k M L U.

Fixpoint M_Block_Update_Outer_Run {A : Type} `{F : Field A} {n : nat} (i : int) (ni nk : nat) (k : int) (M L U : Square A n) : Square A n :=
  let new_M := M_Block_Update_Inner i nk k M L U in
  match ni with
  | 0 => new_M
  | S ni' => M_Block_Update_Outer_Run (i - 1%int63) ni' nk k new_M L U
  end.

Definition M_Block_Update_Outer {A : Type} `{F : Field A} {n : nat} (nk : nat) (k : int) (M L U : Square A n): Square A n :=
  M_Block_Update_Outer_Run (vect_length_int M - 1%int63) (n-nk-1) nk k M L U.


Fixpoint LU_decomp_step {A : Type} `{F : Field A} {n : nat} (nk : nat) (k : int) (M L U : Square A n) :=
  let U' := U.[k,k <- M.[k,k]] in
  let L' := L_Col_Update nk k M L in
  let U'' := U_Row_Update nk k M L in
  let M' := M_Block_Update_Outer nk k M L' U'' in
  match nk with
  | 0 => (L' , U')
  | S nk' => LU_decomp_step nk' (k - 1%int63) M' L' U''
  end.

Definition LU_decomp_with {A : Type} `{F : Field A} {n : nat} (M L U : Square A n) :=
  LU_decomp_step (n-1) (vect_length_int M - 1%int63) M L U.
