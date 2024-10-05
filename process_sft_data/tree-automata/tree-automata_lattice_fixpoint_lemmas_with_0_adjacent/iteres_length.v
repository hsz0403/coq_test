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

Lemma iteres_length : forall (A : Set) (f : Map A -> Map A) (x : Map A) (n : nat), chain_length A (iteres A f x n) = S n.
Proof.
intros.
induction n as [| n Hrecn].
simpl in |- *.
reflexivity.
simpl in Hrecn.
elim (prechain_sum A (iteres A f x n)).
intro.
elim H.
intros.
simpl in |- *.
rewrite H0.
simpl in |- *.
rewrite H0 in Hrecn.
simpl in Hrecn.
rewrite <- Hrecn.
reflexivity.
intros.
elim H.
intros.
elim H0.
intros.
simpl in |- *.
rewrite H1.
simpl in |- *.
rewrite H1 in Hrecn.
simpl in Hrecn.
rewrite <- Hrecn.
reflexivity.
