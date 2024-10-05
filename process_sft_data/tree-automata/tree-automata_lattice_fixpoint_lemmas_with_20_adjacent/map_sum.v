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

Lemma domain_equal_mapget : forall (A B : Set) (m0 : Map A) (m1 : Map B) (a : ad) (x : A), domain_equal A B m0 m1 -> MapGet A m0 a = Some x -> exists y : B, MapGet B m1 a = Some y.
Proof.
simple induction m0.
intros.
inversion H0.
intros.
induction m1 as [| a2 a3| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
inversion H.
simpl in H0.
simpl in H.
elim (bool_is_true_or_false (N.eqb a a1)); intros; rewrite H1 in H0.
inversion H0.
simpl in |- *.
rewrite <- H.
rewrite H1.
split with a3.
reflexivity.
inversion H0.
inversion H.
simple induction m2.
intros.
inversion H1.
intros.
inversion H1.
intros.
elim H3.
intros.
induction a as [| p].
simpl in |- *.
exact (H _ _ _ H5 H4).
induction p as [p Hrecp| p Hrecp| ].
simpl in |- *.
simpl in H4.
exact (H0 _ _ _ H6 H4).
simpl in H4.
simpl in |- *.
exact (H _ _ _ H5 H4).
simpl in |- *.
simpl in H4.
Admitted.

Lemma domain_equal_reflexive : forall (A : Set) (m : Map A), domain_equal A A m m.
Proof.
intros.
induction m as [| a a0| m1 Hrecm1 m0 Hrecm0].
exact I.
simpl in |- *.
reflexivity.
split.
exact Hrecm1.
Admitted.

Lemma domain_equal_symmetric : forall (A B : Set) (m0 : Map A) (m1 : Map B), domain_equal A B m0 m1 -> domain_equal B A m1 m0.
Proof.
simple induction m0.
simple induction m1.
intros.
exact I.
intros.
inversion H.
intros.
inversion H1.
simple induction m1; intros.
inversion H.
simpl in H.
simpl in |- *.
exact (sym_eq H).
inversion H1.
simple induction m2; intros.
inversion H1.
inversion H1.
simpl in |- *.
elim H3; intros.
split.
exact (H _ H4).
Admitted.

Lemma domain_equal_transitive : forall (A0 A1 A2 : Set) (m0 : Map A0) (m1 : Map A1) (m2 : Map A2), domain_equal A0 A1 m0 m1 -> domain_equal A1 A2 m1 m2 -> domain_equal A0 A2 m0 m2.
Proof.
intro.
intro.
intro.
simple induction m0.
simple induction m1.
simple induction m2.
intros.
exact I.
intros.
inversion H0.
intros.
inversion H2.
intros.
inversion H.
intros.
inversion H1.
intro.
intro.
simple induction m1.
intros.
inversion H.
simple induction m2.
intros.
inversion H0.
intros.
simpl in H.
simpl in H0.
rewrite H.
rewrite H0.
simpl in |- *.
reflexivity.
intros.
inversion H2.
intros.
inversion H1.
simple induction m2.
intros.
inversion H1.
intros.
inversion H1.
simple induction m5.
intros.
inversion H4.
intros.
inversion H4.
intros.
simpl in |- *.
simpl in H5.
simpl in H6.
elim H5.
elim H6.
intros.
split.
exact (H _ _ H9 H7).
Admitted.

Lemma prechain_sum : forall (A : Set) (p : prechain A), (exists x : Map A, p = single A x) \/ (exists x : Map A, (exists y : prechain A, p = concat A y x)).
Proof.
intros.
induction p as [m| p Hrecp m].
left.
split with m.
reflexivity.
right.
split with m.
split with p.
Admitted.

Lemma chain_def_ok : forall (A : Set) (T : mEnsemble A) (r : mRelation A) (p : prechain A), chain A T r p -> prechain_dom_ok A T p.
Proof.
intros.
induction p as [m| p Hrecp m].
inversion H.
exact (domok_single A m T H3).
inversion H.
exact (domok_concat A m T (single A x) H5 (domok_single A x T H2)).
rewrite <- H0 in Hrecp.
Admitted.

Lemma chain_incr : forall (A : Set) (T : mEnsemble A) (r : mRelation A) (p : prechain A), chain A T r p -> prechain_incr A r p.
Proof.
intros.
induction p as [m| p Hrecp m].
inversion H.
exact (incr_single A m r).
inversion H.
apply (incr_concat A m r (single A x)).
simpl in |- *.
exact H6.
exact (incr_single A x r).
rewrite <- H0 in Hrecp.
apply (incr_concat A m r (concat A z x)).
simpl in |- *.
exact H5.
Admitted.

Lemma pre_domok_incr_chain_0 : forall (A : Set) (m : Map A), pre_domok_incr_chain_def A (single A m).
Proof.
unfold pre_domok_incr_chain_def in |- *.
intros.
elim H.
intros.
inversion H0.
inversion H1.
Admitted.

Lemma pre_domok_incr_chain_1 : forall (A : Set) (p : prechain A), pre_domok_incr_chain_def A p -> forall m : Map A, pre_domok_incr_chain_def A (concat A p m).
Proof.
unfold pre_domok_incr_chain_def in |- *.
intros.
induction p as [m0| p Hrecp m0].
elim H0.
intros.
inversion H1.
inversion H2.
inversion H7.
simpl in H11.
exact (chain_concat_s A m0 m T r H15 H6 H11).
elim H0.
intros.
inversion H1.
inversion H2.
simpl in H11.
apply (chain_concat_m A m0 m p T r H6 H11).
apply (H T r).
Admitted.

Lemma pre_domok_incr_chain_2 : forall (A : Set) (p : prechain A), pre_domok_incr_chain_def A p.
Proof.
intro.
Admitted.

Lemma pre_domok_incr_chain : forall (A : Set) (p : prechain A) (T : mEnsemble A) (r : mRelation A), prechain_dom_ok A T p /\ prechain_incr A r p -> chain A T r p.
Proof.
intro.
Admitted.

Lemma dist_compl_0 : forall (A : Set) (m : Map A), dist_compl_def_0 A (single A m).
Proof.
unfold dist_compl_def_0 in |- *.
intros.
left.
Admitted.

Lemma dist_compl_1 : forall (A : Set) (m : Map A), dist_compl_def_1 A (single A m).
Proof.
unfold dist_compl_def_1 in |- *.
intros.
unfold dist_compl_def_0 in |- *.
intros.
elim (classic (m = m0)).
intros.
right.
rewrite <- H0.
exact (non_dist_concat_s A m).
intros.
left.
Admitted.

Lemma dist_compl_2 : forall (A : Set) (p : prechain A), dist_compl_def_1 A p -> forall m : Map A, dist_compl_def_1 A (concat A p m).
Proof.
unfold dist_compl_def_1 in |- *.
unfold dist_compl_def_0 in |- *.
intros.
elim H0.
intros.
elim (classic (m = m0)).
intro.
right.
rewrite H2.
exact (non_dist_concat_m_hd A m0 p).
intro.
left.
exact (dist_concat_m A m m0 p H2 H1).
intros.
right.
Admitted.

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

Lemma map_sum : forall (A : Set) (m : Map A), m = M0 A \/ (exists a : ad, (exists x : A, m = M1 A a x)) \/ (exists x : Map A, (exists y : Map A, m = M2 A x y)).
Proof.
intros.
induction m as [| a a0| m1 Hrecm1 m0 Hrecm0].
left.
reflexivity.
right.
left.
split with a.
split with a0.
reflexivity.
right.
right.
split with m1.
split with m0.
reflexivity.
