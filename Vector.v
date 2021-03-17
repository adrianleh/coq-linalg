Require Import Coq.Array.PArray.
Require Import Coq.Numbers.Cyclic.Int63.Int63.
Require ZArith.

Class Field A : Type :=
  {
  plus : A -> A -> A;
  zero : A;
  add_inv: A -> A;
  add_0 : forall (a : A), plus zero a = a;
  add_comm : forall (a b : A), plus a b = plus b a;
  add_add_inv : forall (a : A), plus a (add_inv a) = zero;
  add_assoc : forall (a b c : A), plus a (plus b c) = plus (plus a b) c;
  mult : A -> A -> A;
  one : A;
  mult_inv: A -> A;
  mult_1 : forall (a : A), mult one a = a;
  mult_comm : forall (a b : A), mult a b = mult b a;
  mult_mult_inv : forall (a : A), mult a (mult_inv a) = one;
  mult_distr : forall (a b c : A), mult a (plus b c) = plus (mult a b) (mult b c);
  mult_assoc : forall (a b c : A), mult a (mult b c) = mult (mult a b) c
  }.


Inductive Vector (A : Type) : nat -> Type :=
| vect (arr : array A) {n : nat} {prf : n = BinInt.Z.to_nat((to_Z(length arr)))}  :
    Vector A n.


Definition vect_make {A : Type} (arr : array A) : Vector A (BinInt.Z.to_nat(to_Z(length arr))) :=
  @vect _ arr (BinInt.Z.to_nat((to_Z(length arr)))) (eq_refl).

Definition vect_default {A : Type} {n : nat} (v : Vector A n) :=
  match v with
  | vect _ arr => default arr
  end.

Definition vect_get {A : Type} {n : nat} (v : Vector A n) (idx : int) : A :=
  match v with
  | vect _ arr => arr.[idx]
  end.

Definition vect_set_lem (A : Type) (n : nat) (arr : array A) (idx : int) (a : A) :
  n = BinInt.Z.to_nat(to_Z(length arr)) ->
                      n = BinInt.Z.to_nat(to_Z(length (arr.[idx <- a]))) :=
                                                 match length_set A arr idx a with
                                                 | eq_refl => fun x => x
                                                 end.

Definition vect_set {A : Type} {n : nat} (v : Vector A n) (idx : int) (a : A) : Vector A n :=
  match v with
  | @vect _ arr n prf => @vect _ (arr.[idx<-a]) n (vect_set_lem A n arr idx a prf)
  end.

Notation "t .[ i ]" := (vect_get t i)
  (at level 2, left associativity, format "t .[ i ]").
Notation "t .[ i <- a ]" := (vect_set t i a)
  (at level 2, left associativity, format "t .[ i <- a ]").

Lemma vect_copy_lemma (A : Type) (n : nat) (arr : array A) : n = BinInt.Z.to_nat (to_Z(length arr)) ->
                       n = BinInt.Z.to_nat (to_Z(length (copy arr))).
Proof.
  intro.
  rewrite (length_copy A arr).
  apply H.
Qed.

Definition vect_copy {A : Type} {n : nat} (v : Vector A n) : Vector A n :=
  match v with
  | @vect _ arr n prf => match length_copy A arr with
                        | eq_refl => @vect _ (copy arr) n (vect_copy_lemma A n arr prf)
                        end
  end.

Definition vect_length {A : Type} {n : nat} : Vector A n -> nat :=
  fun v => n.

Definition vect_length_int {A : Type} {n : nat} (v : Vector A n) : int :=
  match v with
  | vect _ arr => length arr
  end.


Local Open Scope int63_scope.

Lemma vect_get_out_of_bounds : forall A (n : nat) (v : Vector A n) (i : int),
    (i <? vect_length_int v) = false -> v.[i] = vect_default v.
Proof.
  intros.
  destruct v.
  simpl.
  unfold vect_length_int in H.
  apply get_out_of_bounds.
  apply H.
Qed.

Lemma vect_default_set : forall A (n : nat) (v : Vector A n) (i : int) (a : A) ,
    vect_default v.[i <- a] = vect_default v.
Proof.
  intros.
  destruct v.
  simpl.
  apply default_set.
Qed.

Lemma vect_get_copy : forall A n (v : Vector A n) i,
    (vect_copy v).[i] = v.[i].
Proof.
  intros.
  destruct v.
  simpl.
  destruct (length_copy A arr).
  apply get_copy.
Qed.

Lemma vect_length_copy : forall A n (v : Vector A n),
    vect_length (vect_copy v) = vect_length v.
Proof.
  reflexivity.
Qed.

Lemma vect_length_copy_int : forall A n (v : Vector A n),
    vect_length_int (vect_copy v) = vect_length_int v.
Proof.
  intros.
  destruct v.
  simpl.
  destruct (length_copy A arr).
  reflexivity.
Qed.

Axiom vect_ext: forall A n (v1 v2: Vector A n),
    (forall i, i <? vect_length_int v1 = true -> v1.[i] = v2.[i]) ->
    v1 = v2.

Lemma vect_ext_default: forall A n (v1 v2 : Vector A n),
    vect_length_int v1 = vect_length_int v2 ->
    (forall i, i <? vect_length_int v1 = true -> v1.[i] = v2.[i]) ->
    vect_default v1 = vect_default v2 ->
    v1 = v2.
Proof.
  intros.
  destruct v1 as [t1 n prf1].
  destruct v2 as [t2 n prf2].
  simpl in H.
  simpl in H0.
  assert (t1 = t2).
  - apply array_ext.
    apply H.
    apply H0.
    apply H1.
  - subst.
    replace prf2 with (@eq_refl nat (BinInt.Z.to_nat(to_Z(length t2)))).
    reflexivity.
    symmetry.
    apply Eqdep_dec.UIP_refl_nat.
Qed.


Lemma vect_default_copy : forall A n (v : Vector A n),  vect_default (vect_copy v) = vect_default v.
Proof.
  intros.
  destruct v.
  simpl.
  destruct (length_copy A arr).
  simpl.
  apply default_copy.
Qed.

Lemma vect_default_make : forall A (t : array A), vect_default (vect_make t) = default t.
Proof.
  intros.
  reflexivity.
Qed.

Lemma vect_get_set_same_default : forall A n (v : Vector A n) (i : int),
    v.[i <- vect_default v].[i] = vect_default v.
Proof.
  intros.
  destruct v.
  apply get_set_same_default.
Qed.

Lemma vect_get_not_default_lt : forall A n (v : Vector A n) (i : int),
    v.[i] <> vect_default v -> (i <? vect_length_int v = true).
Proof.
  intros A n v.
  destruct v.
  simpl.
  apply get_not_default_lt.
Qed.


Lemma vect_get_set_same: forall (A : Type) (n : nat) (vect : Vector A n) (i : int) (a : A), (i <? (vect_length_int vect)) = true -> vect.[i <- a].[i] = a.
Proof.
  intros.
  unfold vect_set, vect_get.
  destruct vect0.
  apply get_set_same.
  simpl in H.
  assumption.
Qed.

Lemma vect_get_set_other: forall A n (vect: Vector A n) i j (a:A), i <> j -> vect.[i<-a].[j] = vect.[j].
  intros.
  unfold vect_set, vect_get.
  destruct vect0.
  apply get_set_other.
  assumption.
Qed.

Lemma vect_get_make: forall A (a : A) size i, (vect_make (make size a)).[i] = a.
Proof.
  intros.
  unfold vect_make, vect_get.
  apply get_make.
Qed.

Lemma vect_leb_length:  forall A n (vect: Vector A n), vect_length_int vect <=? max_length = true.
Proof.
  intros.
  unfold vect_length_int.
  destruct vect0.
  apply leb_length.
Qed.

Lemma vect_make_length_arr: forall A (arr: array A), vect_length_int (vect_make arr) = length arr.
Proof.
  easy.
Qed.

Lemma vect_length_make: forall A (a: A) size, vect_length_int (vect_make (make size a)) = if size <=? max_length then size else max_length.
Proof.
  intros.
  unfold vect_length_int, vect_make.
  apply length_make.
Qed.

Lemma vect_length_set : forall (A : Type) n (vect : Vector A n) (i : int) (a : A), vect_length_int vect = vect_length_int (vect.[i <- a]).
Proof.
  intros.
  unfold vect_length_int.
  destruct vect0.
  destruct (vect A arr).[i <- a] eqn:H'.
  unfold vect_set in H'.
  injection H'.
  intros.
  rewrite <- H.
  rewrite length_set.
  reflexivity.
Qed.

Lemma make_length : forall (A : Type) (arr : array A) (a: A), length arr = length (make (length arr) a).
Proof.
  intros.
  rewrite length_make.
  rewrite leb_length.
  reflexivity.
Qed.

Lemma vect_make_length: forall A n (vect: Vector A n) (a : A), vect_length_int vect = vect_length_int (vect_make (make (vect_length_int vect) a)).
Proof.
  intros.
  rewrite vect_make_length_arr.
  unfold vect_length_int.
  destruct vect0.
  apply make_length.
Qed.

Lemma vect_length_int_vect_length: forall A B n m (v1: Vector A n) (v2: Vector B m), vect_length_int v1 = vect_length_int v2 -> vect_length v1 = vect_length v2.
Proof.
  intros;
  destruct v1, v2.
  unfold vect_length, vect_length_int in *; subst.
  rewrite H.
  reflexivity.
Qed. 

Lemma vect_length_vect_length_type: forall A B n m (v1: Vector A n) (v2: Vector B m), vect_length v1 = vect_length v2 -> n = m.
Proof.
  intros.
  destruct v1, v2; subst.
  assumption.
Qed.

Axiom arr_length_positive: forall A (arr: array A), 0 <=? length arr = true.

Lemma vect_length_type_vect_length_int: forall A B n m (v1: Vector A n) (v2: Vector B m), n = m -> vect_length_int v1 = vect_length_int v2.
Proof.
  intros.
  destruct v1, v2.
  subst.
  simpl.
  apply Znat.Z2Nat.inj in H.
  apply to_Z_inj in H.
  assumption.
  replace BinNums.Z0 with (to_Z 0).
  apply leb_spec.
  apply arr_length_positive.
  reflexivity.
  replace BinNums.Z0 with (to_Z 0).
  apply leb_spec.
  apply arr_length_positive.
  reflexivity.
Qed.

Lemma vect_length_vect_length_int: forall A B n m (v1 : Vector A n) (v2 : Vector B m), vect_length v1 = vect_length v2 -> vect_length_int v1 = vect_length_int v2.
Proof.
  intros.
  apply vect_length_vect_length_type in H.
  apply vect_length_type_vect_length_int.
  exact H.
Qed.

Lemma vect_length_type_vect_length: forall A B n m (v1: Vector A n) (v2: Vector B m), n = m -> vect_length v1 = vect_length v2.
Proof.
  intros.
  unfold vect_length.
  assumption.
Qed.

Local Close Scope int63_scope.


Fixpoint fold_vect_helper {A B : Type} {n: nat} (v : Vector A n) (f : A -> B -> B) (acc : B) (cnt : nat) (idx:int) : B :=
  match cnt with
  | S k => fold_vect_helper v f (f v.[idx] acc) k (idx+1%int63) 
  | O   => acc
  end.

Definition fold_vect {A B: Type} {n: nat} (v: Vector A n) (f: A -> B -> B) (base: B) :=
  fold_vect_helper v f base n (0%int63).


Fixpoint zip_with_vect_helper {A B C: Type} {n: nat} (v1: Vector A n) (v2: Vector B n) (f: A -> B -> C) (tgt: Vector C n) (cnt: nat) (idx: int) : Vector C n :=
  match cnt with
  |  0 => tgt
  | S k =>
      let el := f (v1.[idx]) (v2.[idx]) in
      zip_with_vect_helper v1 v2 f (tgt.[idx <- el]) k (idx + 1%int63)
  end.

Fixpoint map_vect_helper {A B: Type} {n: nat} (v: Vector A n) (f: A -> B ) (tgt: Vector B n) (cnt: nat) (idx: int) : Vector B n :=
  match cnt with
  |  0 => tgt
  | S k =>
      let el := f (v.[idx]) in
      map_vect_helper v f (tgt.[idx <- el]) k (idx + 1%int63)
  end.

Definition zip_with_vect_on {A B C: Type} {n: nat} (v1: Vector A n) (v2: Vector B n) (f: A -> B -> C) (tgt: Vector C n) :=
  zip_with_vect_helper v1 v2 f tgt n (0%int63).

Definition map_vect_on {A B: Type} {n: nat} (v: Vector A n) (f: A -> B) (tgt: Vector B n) :=
  map_vect_helper v f tgt n (0%int63).




Theorem nRect : forall (A : Type) (n n0 : nat) (v : Vector A n), n0 = BinInt.Z.to_nat(to_Z(vect_length_int v)) ->
                                                          n = BinInt.Z.to_nat(to_Z(vect_length_int v)) ->
                                                          n0 = n.
Proof.
  intros.
  destruct v.
  rewrite H0.
  easy.
Qed.

Theorem zip_with_vect_init : forall {A B C : Type} {n : nat}
          (v1 : Vector A n)
          (v2 : Vector B n)
          (f : A -> B -> C),
          Vector C n.
Proof.
  intros.
  destruct v1 eqn:E.
  eapply (@vect C
              (make (vect_length_int v1)
                    (f (vect_default v1) (vect_default v2)))).
  rewrite length_make.
  rewrite vect_leb_length.
  rewrite E.
  simpl.
  apply prf.
Qed.

Theorem map_vect_init : forall {A B : Type} {n : nat}
          (v : Vector A n)
          (f : A -> B),
          Vector B n.
Proof.
  intros.
  destruct v eqn:E.
  eapply (@vect B
              (make (vect_length_int v)
                    (f (vect_default v)))).
  rewrite length_make.
  rewrite vect_leb_length.
  rewrite E.
  simpl.
  apply prf.
Qed.



Definition zip_with_vect {A B C : Type} {n : nat} (v1 : Vector A n) (v2 : Vector B n) (f : A -> B -> C) : Vector C n :=
  zip_with_vect_on v1 v2 f (zip_with_vect_init v1 v2 f).

Definition map_vect {A B : Type} {n : nat} (v: Vector A n) ( f: A -> B) : Vector B n :=
  map_vect_on v f (map_vect_init v f).

Definition vect_plus {n : nat} {A: Type} `{F: Field A} (v1 : Vector A n) (v2 : Vector A n) : Vector A n :=
  zip_with_vect v1 v2 plus.

Definition vect_elem_mult {n : nat} {A : Type} `{F: Field A} (v1 : Vector A n) (v2 : Vector A n) : Vector A n :=
  zip_with_vect v1 v2 mult.

Definition vect_dot_product {n : nat} {A : Type} `{F : Field A} (v1 : Vector A n) (v2 : Vector A n) : A :=
  fold_vect (zip_with_vect v1 v2 mult) plus zero.

Definition vect_add_inv {n : nat} {A : Type} `{F : Field A} (v : Vector A n) : Vector A n :=
  map_vect v add_inv.

Definition vect_mult_inv {n : nat} {A : Type} `{F : Field A} (v : Vector A n) : Vector A n :=
  map_vect v mult_inv.

Definition vect_sub {n : nat} {A : Type} `{F : Field A} (v1 : Vector A n) (v2: Vector A n) : Vector A n :=
  vect_plus v1 (vect_add_inv v2).


Notation "< A , B >" := (vect_dot_product A B) (at level 70, no associativity).
Notation "A +@ B" := (vect_plus A B) (at level 50, left associativity).
Notation "A -@ B" := (vect_sub A B) (at level 50, left associativity).
Notation "A *@ B" := (vect_elem_mult A B) (at level 40, left associativity).
Notation "-@ A" := (vect_add_inv A) (at level 35, right associativity).

Local Open Scope int63_scope.
Lemma vect_make_make_length: forall A n i (i_bnd: i <=? max_length = true) (prf: n = BinInt.Z.to_nat(to_Z(i))) (a : A), vect_length(vect_make (make i a)) = n.
Proof.
  intros.
  rewrite prf.
  unfold vect_length. 
  rewrite length_make.
  rewrite i_bnd.
  easy.
Qed.

Lemma leb_trans: forall (a b c : int), (a <=? b = true) /\ (b <=? c =true) -> (a <=? c = true).
Proof.
  intros.
  destruct H as [Hab Hbc].
  Search "lebP".
  assert (Bool.reflect (BinInt.Z.le (to_Z a) (to_Z b)) true) as Hab'.
  rewrite <- Hab.
  apply lebP.
  assert (Bool.reflect (BinInt.Z.le (to_Z b) (to_Z c)) true) as Hbc'.
  rewrite <- Hbc.
  apply lebP.
  inversion Hab'.
  inversion Hbc'.
  assert (BinInt.Z.le (to_Z a) (to_Z c)).
  eapply BinInt.Z.le_trans.
  apply H.
  apply H0.
  assert (Bool.reflect (BinInt.Z.le (to_Z a) (to_Z c)) true).
  constructor.
  assumption.
  assert (Bool.reflect (BinInt.Z.le (to_Z a) (to_Z c)) (a <=? c)).
  apply lebP.
  inversion H3.
  reflexivity.
  inversion H2.
  auto.
Qed.

Local Close Scope int63_scope.



