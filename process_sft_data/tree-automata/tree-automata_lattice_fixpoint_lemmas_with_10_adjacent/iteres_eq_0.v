Require Import Classical_Prop.
Require Import Bool.
Require Import Arith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import bases.
Fixpoint domain_equal (A B : Set) (m0 : Map A) (m1 : Map B) {struct m1} : Prop := match m0, m1 with | M0, M0 => True | M0, M1 _ _ => False | M0, M2 _ _ => False | M1 _ _, M0 => False | M1 a _, M1 b _ => a = b | M1 _ _, M2 _ _ => False | M2 _ _, M0 => False | M2 _ _, M1 _ _ => False | M2 a b, M2 c d => domain_equal A B a c /\ domain_equal A B b d end.
Definition mEnsemble (A : Set) := Map A -> Prop.
Definition mRelation (A : Set) := Map A -> Map A -> Prop.
Definition r_symmetric (A : Set) (r : mRelation A) := forall x y : Map A, r x y -> r y x.
Definition r_antisymmetric (A : Set) (r : mRelation A) := forall x y : Map A, r x y -> r y x -> x = y.
Definition r_transitive (A : Set) (r : mRelation A) := forall x y z : Map A, r x y -> r y z -> r x z.
Definition r_reflexive (A : Set) (r : mRelation A) := forall x : Map A, r x x.
Definition r_order (A : Set) (r : mRelation A) := r_reflexive A r /\ r_antisymmetric A r /\ r_transitive A r.
Definition mini (A : Set) (r : mRelation A) (T : mEnsemble A) (e : Map A) := T e /\ (forall x : Map A, T x -> r e x).
Definition maxi (A : Set) (r : mRelation A) (T : mEnsemble A) (e : Map A) := T e /\ (forall x : Map A, T x -> r x e).
Definition mLattice (A : Set) (r : mRelation A) (T : mEnsemble A) (e f : Map A) := r_order A r /\ mini A r T e /\ maxi A r T f.
Inductive prechain (A : Set) : Set := | single : Map A -> prechain A | concat : prechain A -> Map A -> prechain A.
Inductive prechain_dom_ok (A : Set) : mEnsemble A -> prechain A -> Prop := | domok_single : forall (x : Map A) (T : mEnsemble A), T x -> prechain_dom_ok A T (single A x) | domok_concat : forall (x : Map A) (T : mEnsemble A) (p : prechain A), T x -> prechain_dom_ok A T p -> prechain_dom_ok A T (concat A p x).
Fixpoint chain_length (A : Set) (p : prechain A) {struct p} : nat := match p with | single x => 1 | concat x y => S (chain_length A x) end.
Definition prechain_last (A : Set) (p : prechain A) : Map A := match p with | single x => x | concat z x => x end.
Inductive prechain_incr (A : Set) : mRelation A -> prechain A -> Prop := | incr_single : forall (x : Map A) (r : mRelation A), prechain_incr A r (single A x) | incr_concat : forall (x : Map A) (r : mRelation A) (p : prechain A), r (prechain_last A p) x -> prechain_incr A r p -> prechain_incr A r (concat A p x).
Inductive chain (A : Set) : mEnsemble A -> mRelation A -> prechain A -> Prop := | chain_single : forall (x : Map A) (T : mEnsemble A) (r : mRelation A), T x -> chain A T r (single A x) | chain_concat_s : forall (x y : Map A) (T : mEnsemble A) (r : mRelation A), T x -> T y -> r x y -> chain A T r (concat A (single A x) y) | chain_concat_m : forall (x y : Map A) (z : prechain A) (T : mEnsemble A) (r : mRelation A), T y -> r x y -> chain A T r (concat A z x) -> chain A T r (concat A (concat A z x) y).
Definition pre_domok_incr_chain_def (A : Set) (p : prechain A) := forall (T : mEnsemble A) (r : mRelation A), prechain_dom_ok A T p /\ prechain_incr A r p -> chain A T r p.
Inductive dist_chain (A : Set) : prechain A -> Prop := | dist_single : forall x : Map A, dist_chain A (single A x) | dist_concat_s : forall x y : Map A, x <> y -> dist_chain A (concat A (single A x) y) | dist_concat_m : forall (x y : Map A) (z : prechain A), x <> y -> dist_chain A (concat A z x) -> dist_chain A (concat A (concat A z x) y).
Inductive non_dist_chain (A : Set) : prechain A -> Prop := | non_dist_concat_s : forall x : Map A, non_dist_chain A (concat A (single A x) x) | non_dist_concat_m_hd : forall (x : Map A) (z : prechain A), non_dist_chain A (concat A (concat A z x) x) | non_dist_concat_m_tl : forall (x y : Map A) (z : prechain A), non_dist_chain A (concat A z x) -> non_dist_chain A (concat A (concat A z x) y).
Definition sas_chain (A : Set) (T : mEnsemble A) (r : mRelation A) (p : prechain A) : Prop := chain A T r p /\ dist_chain A p.
Definition dist_compl_def_0 (A : Set) (p : prechain A) : Prop := dist_chain A p \/ non_dist_chain A p.
Definition dist_compl_def_1 (A : Set) (p : prechain A) : Prop := dist_compl_def_0 A p -> forall m : Map A, dist_compl_def_0 A (concat A p m).
Definition bounded_sas_chain (A : Set) (T : mEnsemble A) (r : mRelation A) (n : nat) : Prop := forall p : prechain A, sas_chain A T r p -> chain_length A p <= n.
Definition def_ok_app (A : Set) (T : mEnsemble A) (f : Map A -> Map A) : Prop := forall x : Map A, T x -> T (f x).
Definition increasing_app (A : Set) (r : mRelation A) (f : Map A -> Map A) : Prop := forall x y : Map A, r x y -> r (f x) (f y).
Definition fix_point (A : Set) (T : mEnsemble A) (f : Map A -> Map A) (x : Map A) : Prop := T x /\ f x = x.
Definition inf_fix_points (A : Set) (T : mEnsemble A) (r : mRelation A) (f : Map A -> Map A) (x : Map A) : Prop := forall y : Map A, fix_point A T f y -> r x y.
Definition lower_fix_point (A : Set) (T : mEnsemble A) (r : mRelation A) (f : Map A -> Map A) (x : Map A) : Prop := fix_point A T f x /\ inf_fix_points A T r f x.
Fixpoint iteres (A : Set) (f : Map A -> Map A) (x : Map A) (n : nat) {struct n} : prechain A := match n with | O => single A x | S p => match iteres A f x p with | single y => concat A (single A y) (f y) | concat z y => concat A (concat A z y) (f y) end end.
Fixpoint power (A : Set) (f : A -> A) (x : A) (n : nat) {struct n} : A := match n with | O => x | S n => f (power A f x n) end.
Inductive MapFlag (A : Set) : Set := | flag_true : Map A -> MapFlag A | flag_false : Map A -> MapFlag A.
Fixpoint lazy_power_aux (A : Set) (egalite : Map A -> Map A -> bool) (f : Map A -> Map A) (x : Map A) (n : nat) {struct n} : MapFlag A := match n with | O => flag_false A x | S p => match lazy_power_aux A egalite f x p with | flag_true y => flag_true A y | flag_false y => match f y with | z => if egalite y z then flag_true A y else flag_false A z end end end.
Definition lazy_power (A : Set) (egalite : Map A -> Map A -> bool) (f : Map A -> Map A) (x : Map A) (n : nat) : Map A := match lazy_power_aux A egalite f x n with | flag_false z => z | flag_true z => z end.
Fixpoint iteres_0 (A : Set) (f : Map A -> Map A) (x : Map A) (n : nat) {struct n} : prechain A := match n with | O => single A x | S p => match iteres_0 A f x p with | single y => concat A (single A y) (power (Map A) f x (S p)) | concat z y => concat A (concat A z y) (power (Map A) f x (S p)) end end.
Definition iteres_ult_const_def_0 (A : Set) (p : prechain A) : Prop := forall (f : Map A -> Map A) (x : Map A) (n : nat), p = iteres A f x n -> non_dist_chain A p -> exists q : nat, S q <= n /\ power (Map A) f x q = power (Map A) f x (S q).
Definition leb (b0 b1 : bool) : Prop := match b0, b1 with | false, false => True | false, true => True | true, false => False | true, true => True end.
Fixpoint lem (m0 m1 : Map bool) {struct m1} : Prop := match m0, m1 with | M0, M0 => True | M0, M1 _ _ => False | M0, M2 _ _ => False | M1 _ _, M0 => False | M1 a b, M1 a' b' => if N.eqb a a' then leb b b' else False | M1 _ _, M2 _ _ => False | M2 _ _, M0 => False | M2 _ _, M1 _ _ => False | M2 a b, M2 c d => lem a c /\ lem b d end.
Definition ensemble_base (A : Set) (m : Map A) (x : Map bool) := domain_equal A bool m x.
Fixpoint map_fill (A : Set) (m : Map A) {struct m} : bool -> Map bool := fun b : bool => match m with | M0 => M0 bool | M1 a _ => M1 bool a b | M2 m0 m1 => M2 bool (map_fill A m0 b) (map_fill A m1 b) end.
Definition map_mini (A : Set) (m : Map A) : Map bool := map_fill A m false.
Definition map_maxi (A : Set) (m : Map A) : Map bool := map_fill A m true.
Definition lattice_bounded_def_0 (p : prechain bool) : Prop := forall (A : Set) (m0 m1 : Map A), sas_chain bool (ensemble_base A (M2 A m0 m1)) lem p -> exists p0 : prechain bool, (exists p1 : prechain bool, sas_chain bool (ensemble_base A m0) lem p0 /\ sas_chain bool (ensemble_base A m1) lem p1 /\ lem (M2 bool (prechain_last bool p0) (prechain_last bool p1)) (prechain_last bool p) /\ chain_length bool p0 + chain_length bool p1 = S (chain_length bool p)).
Definition lattice_bounded_def_1 (p : prechain bool) : Prop := lattice_bounded_def_0 p -> forall m : Map bool, lattice_bounded_def_0 (concat bool p m).
Definition lattice_bounded_def_2 (A : Set) (m : Map A) : Prop := forall p : prechain bool, sas_chain bool (ensemble_base A m) lem p -> chain_length bool p <= S (MapCard A m).
Definition eq_bool (b0 b1 : bool) : bool := match b0, b1 with | false, false => true | false, true => false | true, false => false | true, true => true end.
Fixpoint eqm_bool (x y : Map bool) {struct y} : bool := match x, y with | M0, M0 => true | M0, M1 _ _ => false | M0, M2 _ _ => false | M1 _ _, M0 => false | M1 a b, M1 c d => N.eqb a c && eq_bool b d | M1 _ _, M2 _ _ => false | M2 _ _, M0 => false | M2 _ _, M1 _ _ => false | M2 a b, M2 c d => eqm_bool a c && eqm_bool b d end.

Lemma dist_compl_3 : forall (A : Set) (p : prechain A), dist_compl_def_0 A p -> forall m : Map A, dist_compl_def_0 A (concat A p m).
Proof.
intro.
Admitted.

Lemma dist_compl_4 : forall (A : Set) (p : prechain A), dist_chain A p \/ non_dist_chain A p.
Proof.
intro.
Admitted.

Lemma dist_compl_5 : forall (A : Set) (x : Map A), ~ dist_chain A (concat A (single A x) x).
Proof.
intros.
intro.
inversion H.
Admitted.

Lemma dist_compl_6 : forall (A : Set) (x : Map A) (z : prechain A), ~ dist_chain A (concat A (concat A z x) x).
Proof.
intros.
intro.
inversion H.
Admitted.

Lemma dist_compl_7 : forall (A : Set) (x y : Map A) (z : prechain A), non_dist_chain A (concat A z x) -> ~ dist_chain A (concat A z x) -> ~ dist_chain A (concat A (concat A z x) y).
Proof.
intros.
intro.
inversion H1.
Admitted.

Lemma dist_compl_8 : forall (A : Set) (p : prechain A), non_dist_chain A p -> ~ dist_chain A p.
Proof.
Admitted.

Lemma dist_compl : forall (A : Set) (p : prechain A), ~ dist_chain A p <-> non_dist_chain A p.
Proof.
intros.
split.
intros.
elim (dist_compl_4 A p); intros.
elim (H H0).
exact H0.
Admitted.

Lemma MapFlag_sum : forall (A : Set) (f : MapFlag A), exists x : Map A, f = flag_true A x \/ f = flag_false A x.
Proof.
intros.
induction f as [m| m].
split with m.
left.
reflexivity.
split with m.
right.
Admitted.

Lemma lazy_power_eg_power_0 : forall (A : Set) (egalite : Map A -> Map A -> bool) (f : Map A -> Map A) (x : Map A) (n : nat), (forall a b : Map A, egalite a b = true <-> a = b) -> forall z : Map A, (lazy_power_aux A egalite f x n = flag_true A z -> z = power (Map A) f x n /\ z = f z) /\ (lazy_power_aux A egalite f x n = flag_false A z -> z = power (Map A) f x n).
Proof.
simple induction n.
intros.
simpl in |- *.
intros.
split; intros; inversion H0.
reflexivity.
intros.
simpl in |- *.
intros.
elim (MapFlag_sum A (lazy_power_aux A egalite f x n0)).
intros.
elim H1; intros; rewrite H2.
split; intros.
inversion H3.
rewrite <- H5.
elim (H H0 x0); intros.
elim (H4 H2); intros.
rewrite <- H7.
split; exact H8.
inversion H3.
elim (bool_is_true_or_false (egalite x0 (f x0))); intros.
rewrite H3.
split.
intros.
inversion H4.
rewrite <- H6.
elim (H H0 x0).
intros.
rewrite <- (H7 H2).
elim (H0 x0 (f x0)); intros.
split; exact (H8 H3).
intros.
inversion H4.
rewrite H3.
split; intros.
inversion H4.
inversion H4.
elim (H H0 x0).
intros.
rewrite <- (H7 H2).
Admitted.

Lemma lazy_power_eg_power : forall (A : Set) (egalite : Map A -> Map A -> bool) (f : Map A -> Map A) (x : Map A) (n : nat), (forall a b : Map A, egalite a b = true <-> a = b) -> lazy_power A egalite f x n = power (Map A) f x n.
Proof.
intros.
intros.
unfold lazy_power in |- *.
elim (MapFlag_sum A (lazy_power_aux A egalite f x n)).
intros.
elim H0; intros; rewrite H1.
elim (lazy_power_eg_power_0 A egalite f x n H x0).
intros.
elim (H2 H1).
intros.
exact H4.
elim (lazy_power_eg_power_0 A egalite f x n H x0).
intros.
Admitted.

Lemma iteres_eq : forall (A : Set) (f : Map A -> Map A) (x : Map A) (n : nat), iteres A f x n = iteres_0 A f x n.
Proof.
intros.
induction n as [| n Hrecn].
reflexivity.
simpl in |- *.
rewrite <- (iteres_eq_0 A f x n).
elim (prechain_sum A (iteres A f x n)); intros.
elim H.
intros.
rewrite H0.
rewrite H0 in Hrecn.
rewrite Hrecn.
rewrite <- Hrecn.
reflexivity.
elim H.
intros.
elim H0.
intros.
rewrite H1.
rewrite H1 in Hrecn.
rewrite <- Hrecn.
Admitted.

Lemma iteres_def_ok : forall (A : Set) (T : mEnsemble A) (f : Map A -> Map A) (x : Map A) (n k : nat), def_ok_app A T f -> T (power (Map A) f x n) -> T (power (Map A) f x (n + k)).
Proof.
intros.
induction k as [| k Hreck].
rewrite (plus_comm n 0).
simpl in |- *.
exact H0.
rewrite <- (plus_Snm_nSm n k).
simpl in |- *.
Admitted.

Lemma power_def_ok : forall (A : Set) (T : mEnsemble A) (f : Map A -> Map A) (x : Map A) (n : nat), def_ok_app A T f -> T x -> T (power (Map A) f x n).
Proof.
intros.
replace n with (0 + n).
apply (iteres_def_ok A T f x 0 n H).
simpl in |- *.
exact H0.
simpl in |- *.
Admitted.

Lemma iteres_ult_const_0 : forall (A : Set) (x : Map A), iteres_ult_const_def_0 A (concat A (single A x) x).
Proof.
unfold iteres_ult_const_def_0 in |- *.
intros.
elim (nat_sum n); intros.
rewrite H1 in H.
inversion H.
elim H1.
intros.
rewrite H2 in H.
elim (nat_sum x1); intros.
rewrite H3 in H.
simpl in H.
inversion H.
split with 0.
rewrite H2.
rewrite H3.
split.
exact (le_n_n _).
simpl in |- *.
rewrite <- H6.
exact H6.
elim H3.
intros.
rewrite H4 in H.
simpl in H.
elim (prechain_sum A (iteres A f x0 x2)); intros.
elim H5.
intros.
rewrite H6 in H.
inversion H.
elim H5.
intros.
elim H6.
intros.
rewrite H7 in H.
Admitted.

Lemma iteres_ult_const_1 : forall (A : Set) (x : Map A) (z : prechain A), iteres_ult_const_def_0 A (concat A (concat A z x) x).
Proof.
unfold iteres_ult_const_def_0 in |- *.
intros.
elim (nat_sum n); intros.
rewrite H1 in H.
inversion H.
elim H1.
intros.
elim (nat_sum x1); intros.
rewrite H3 in H2.
rewrite H2 in H.
simpl in H.
inversion H.
elim H3.
intros.
rewrite H4 in H2.
rewrite H2 in H.
rewrite (iteres_eq A f x0 (S (S x2))) in H.
simpl in H.
elim (prechain_sum A (iteres_0 A f x0 x2)); intros.
elim H5.
intros.
rewrite H6 in H.
inversion H.
split with (S x2).
rewrite H2.
split.
exact (le_n_n _).
simpl in |- *.
exact H10.
elim H5.
intros.
elim H6.
intros.
rewrite H7 in H.
inversion H.
split with (S x2).
rewrite H2.
split.
exact (le_n_n _).
simpl in |- *.
Admitted.

Lemma iteres_ult_const_2 : forall (A : Set) (x y : Map A) (z : prechain A), non_dist_chain A (concat A z x) -> iteres_ult_const_def_0 A (concat A z x) -> iteres_ult_const_def_0 A (concat A (concat A z x) y).
Proof.
unfold iteres_ult_const_def_0 in |- *.
intros.
elim (nat_sum n); intros.
rewrite H3 in H1.
inversion H1.
elim H3.
intros.
elim (nat_sum x1); intros.
rewrite H5 in H4.
rewrite H4 in H1.
inversion H1.
elim H5.
intros.
rewrite H6 in H4.
rewrite H4 in H1.
elim (H0 f x0 (S x2)).
intros.
elim H7.
intros.
split with x3.
split.
rewrite H4.
exact (le_trans (S x3) (S x2) (S (S x2)) H8 (le_n_Sn _)).
exact H9.
simpl in |- *.
simpl in H1.
elim (prechain_sum A (iteres A f x0 x2)); intros.
elim H7.
intros.
rewrite H8 in H1.
rewrite H8.
inversion H1.
reflexivity.
elim H7.
intros.
elim H8.
intros.
rewrite H9 in H1.
rewrite H9.
inversion H1.
reflexivity.
Admitted.

Lemma iteres_ult_const_3 : forall (A : Set) (p : prechain A), non_dist_chain A p -> iteres_ult_const_def_0 A p.
Proof.
intro.
Admitted.

Lemma iteres_ult_const_4 : forall (A : Set) (f : Map A -> Map A) (x : Map A) (n : nat), non_dist_chain A (iteres A f x n) -> exists p : nat, S p <= n /\ power (Map A) f x p = power (Map A) f x (S p).
Proof.
intros.
Admitted.

Lemma iteres_last : forall (A : Set) (f : Map A -> Map A) (x : Map A) (n : nat) (y : prechain A) (z : Map A), iteres A f x n = concat A y z -> z = f (prechain_last A y).
Proof.
intros.
elim (nat_sum n); intros.
rewrite H0 in H.
simpl in H.
inversion H.
elim H0.
intros.
rewrite H1 in H.
simpl in H.
elim (prechain_sum A (iteres A f x x0)).
intros.
elim H2.
intros.
rewrite H3 in H.
inversion H.
reflexivity.
intros.
elim H2.
intros.
elim H3.
intros.
rewrite H4 in H.
inversion H.
Admitted.

Lemma iteres_dom_ok : forall (A : Set) (T : mEnsemble A) (f : Map A -> Map A) (x : Map A) (n : nat), T x -> def_ok_app A T f -> prechain_dom_ok A T (iteres A f x n).
Proof.
intros.
induction n as [| n Hrecn].
simpl in |- *.
exact (domok_single A x T H).
simpl in |- *.
elim (prechain_sum A (iteres A f x n)); intro.
elim H1.
intros.
rewrite H2.
rewrite H2 in Hrecn.
inversion Hrecn.
exact (domok_concat A (f x0) T (single A x0) (H0 x0 H5) Hrecn).
elim H1.
intros.
elim H2.
intros.
rewrite H3.
rewrite H3 in Hrecn.
inversion Hrecn.
Admitted.

Lemma iteres_eq_0 : forall (A : Set) (f : Map A -> Map A) (x : Map A) (n : nat), prechain_last A (iteres A f x n) = power (Map A) f x n.
Proof.
intros.
induction n as [| n Hrecn].
reflexivity.
elim (prechain_sum A (iteres A f x n)); intros.
elim H.
intros.
rewrite H0 in Hrecn.
simpl in |- *.
rewrite H0.
simpl in |- *.
simpl in Hrecn.
rewrite Hrecn.
reflexivity.
elim H.
intros.
elim H0.
intros.
simpl in |- *.
rewrite H1.
rewrite H1 in Hrecn.
simpl in |- *.
simpl in Hrecn.
rewrite Hrecn.
reflexivity.
