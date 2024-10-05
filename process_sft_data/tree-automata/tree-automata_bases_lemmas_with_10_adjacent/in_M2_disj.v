Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma le_disj : forall n m : nat, n <= m -> n = m \/ S n <= m.
Proof.
intros.
cut (m <= n \/ n < m).
intro.
elim H0; intros.
left.
exact (le_antisym n m H H1).
right.
exact (lt_le_S n m H1).
Admitted.

Lemma le_mult_l : forall n m p : nat, n <= m -> n * p <= m * p.
Proof.
intro.
simple induction m.
intros.
cut (n = 0).
intro.
rewrite H0; trivial.
symmetry in |- *.
exact (le_n_O_eq n H).
induction n as [| n Hrecn].
intros.
simpl in |- *.
exact (le_O_n (p + n * p)).
intros.
simpl in |- *.
cut (n = n0 \/ S n <= n0).
intro.
cut (n * p <= n0 * p).
intro.
elim H1; intros.
cut (p <= p).
intros.
exact (plus_le_compat p p (n * p) (n0 * p) H4 H2).
exact (le_n_n p).
cut (n * p <= S n * p).
cut (S n * p <= n0 * p).
intros.
apply (le_trans (p + n * p) (p + S n * p) (p + n0 * p)).
exact (plus_le_compat p p (n * p) (S n * p) (le_n_n p) H5).
exact (plus_le_compat p p (S n * p) (n0 * p) (le_n_n p) H4).
exact (H p H3).
exact (le_mult_lS n p).
elim H1; intros.
rewrite H2.
exact (le_n_n (n0 * p)).
cut (n * p <= S n * p).
intro.
cut (S n * p <= n0 * p).
intro.
exact (le_trans (n * p) (S n * p) (n0 * p) H3 H4).
exact (H p H2).
exact (le_mult_lS n p).
cut (n <= n0).
intro.
exact (le_disj n n0 H1).
Admitted.

Lemma le_mult_r : forall n m p : nat, n <= m -> p * n <= p * m.
Proof.
intros.
cut (p * n = n * p).
intros.
cut (p * m = m * p).
intros.
rewrite H0.
rewrite H1.
exact (le_mult_l n m p H).
exact (mult_comm p m).
Admitted.

Lemma le_mult_mult : forall n m p q : nat, n <= m -> p <= q -> n * p <= m * q.
Proof.
intros.
cut (n * p <= n * q).
intro.
cut (n * q <= m * q).
intro.
exact (le_trans (n * p) (n * q) (m * q) H1 H2).
exact (le_mult_l n m q H).
Admitted.

Lemma Sn_eq_Sm_n_eq_m : forall n m : nat, S n = S m -> n = m.
Proof.
simple induction n.
simple induction m.
intros.
reflexivity.
intros.
inversion H0.
simple induction m.
intros.
inversion H0.
intros.
inversion H1.
Admitted.

Lemma bool_dec_eq : forall a b : bool, {a = b} + {a <> b}.
Proof.
intros.
case a.
case b.
left.
trivial.
right.
exact diff_true_false.
case b.
right.
exact diff_false_true.
left.
Admitted.

Lemma bool_is_false_or_true : forall a : bool, a = false \/ a = true.
Proof.
simple induction a.
right.
trivial.
left.
Admitted.

Lemma bool_is_true_or_false : forall a : bool, a = true \/ a = false.
Proof.
simple induction a.
left.
trivial.
right.
Admitted.

Lemma in_M0_false : forall (A : Set) (a : A), ~ (exists e : ad, MapGet A (M0 A) e = Some a).
Proof.
intros.
intro.
elim H.
intros.
Admitted.

Lemma in_M1_id : forall (A : Set) (a : A) (x : ad) (e : A), (exists c : ad, MapGet A (M1 A x e) c = Some a) -> a = e.
Proof.
intros.
elim H.
intros.
cut (x = x0).
intro.
rewrite H1 in H0.
cut (MapGet A (M1 A x0 e) x0 = Some e).
intros.
cut (Some e = Some a).
intro.
inversion H3.
trivial.
transitivity (MapGet A (M1 A x0 e) x0).
symmetry in |- *.
assumption.
assumption.
exact (M1_semantics_1 A x0 e).
cut (N.eqb x x0 = false \/ N.eqb x x0 = true).
intro.
elim H1; intros.
cut (MapGet A (M1 A x e) x0 = None).
intro.
cut (Some a = None).
intro.
inversion H4.
transitivity (MapGet A (M1 A x e) x0).
symmetry in |- *.
assumption.
assumption.
exact (M1_semantics_2 A x x0 e H2).
exact (Neqb_complete x x0 H2).
elim (bool_dec_eq (N.eqb x x0) true).
intros.
right.
assumption.
intro y.
left.
Admitted.

Lemma aux_Neqb_1_0 : forall p : positive, Pos.eqb p p = true.
Proof.
simple induction p.
simpl in |- *.
intros.
trivial.
simpl in |- *.
intros.
trivial.
Admitted.

Lemma aux_Neqb_1_1 : forall p p0 : positive, Pos.eqb p p0 = true -> p = p0.
Proof.
simple induction p.
intro.
intro.
simple induction p1.
intros.
simpl in H1.
cut (p0 = p2).
intro.
rewrite H2.
trivial.
exact (H p2 H1).
intros.
simpl in H1.
inversion H1.
intros.
inversion H0.
intro.
intro.
simple induction p1.
intros.
inversion H1.
intros.
cut (p0 = p2).
intros.
rewrite H2.
trivial.
simpl in H1.
exact (H p2 H1).
intros.
inversion H0.
simple induction p0.
intros.
inversion H0.
intros.
inversion H0.
intros.
Admitted.

Lemma aux_Neqb_trans : forall a b c : ad, N.eqb a b = true -> N.eqb b c = true -> N.eqb a c = true.
Proof.
intros.
rewrite <- (Neqb_complete b c H0).
Admitted.

Lemma indprinciple_nat_gen : forall P : nat -> Prop, (forall n : nat, (forall m : nat, m < n -> P m) -> P n) -> forall n m : nat, m <= n -> P m.
Proof.
intro.
intro.
simple induction n.
intros.
apply (H m).
intros.
elim (lt_n_O m0 (lt_le_trans m0 m 0 H1 H0)).
intros.
elim (le_lt_or_eq m (S n0) H1).
intros.
exact (H0 m (lt_n_Sm_le m n0 H2)).
intro.
rewrite H2.
apply (H (S n0)).
intros.
Admitted.

Lemma beq_nat_complete : forall n m : nat, beq_nat n m = true -> n = m.
Proof.
simple induction n.
simple induction m.
intros.
reflexivity.
intros.
inversion H0.
simple induction m.
intros.
inversion H0.
intros.
simpl in H1.
rewrite (H _ H1).
Admitted.

Lemma beq_nat_correct : forall n : nat, beq_nat n n = true.
Proof.
simple induction n.
reflexivity.
intros.
simpl in |- *.
Admitted.

Lemma in_M2_disj : forall (A : Set) (a : A) (m0 m1 : Map A), (exists c : ad, MapGet A (M2 A m0 m1) c = Some a) -> (exists c : ad, MapGet A m0 c = Some a) \/ (exists c : ad, MapGet A m1 c = Some a).
Proof.
intros.
elim H.
simple induction x.
simpl in |- *.
intro.
left.
split with N0.
assumption.
simple induction p.
intros.
right.
simpl in H1.
split with (Npos p0).
assumption.
intros.
left.
simpl in H1.
split with (Npos p0).
assumption.
intros.
right.
simpl in H0.
split with N0.
assumption.
