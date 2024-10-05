Require Import Bool.
Require Import Arith.
Require Import NArith Ndec.
Require Import ZArith.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import refcorrect.
Require Import lattice_fixpoint.
Inductive coacc : preDTA -> ad -> ad -> Prop := | coacc_id : forall (d : preDTA) (a : ad) (s : state), MapGet state d a = Some s -> coacc d a a | coacc_nxt : forall (d : preDTA) (a0 a1 a2 : ad) (s1 s2 : state) (pl : prec_list) (c : ad), MapGet state d a2 = Some s2 -> MapGet state d a1 = Some s1 -> MapGet prec_list s1 c = Some pl -> prec_occur pl a2 -> coacc d a0 a1 -> coacc d a0 a2.
Definition coacc_transitive_def (d : preDTA) (a0 a1 : ad) : Prop := forall a2 : ad, coacc d a0 a1 -> coacc d a2 a0 -> coacc d a2 a1.
Fixpoint map_replace (A : Set) (m : Map A) {struct m} : ad -> A -> Map A := fun (a : ad) (x : A) => match m with | M0 => M0 A | M1 b y => if N.eqb a b then M1 A b x else M1 A b y | M2 m n => match a with | N0 => M2 A (map_replace A m N0 x) n | Npos q => match q with | xH => M2 A m (map_replace A n N0 x) | xO p => M2 A (map_replace A m (Npos p) x) n | xI p => M2 A m (map_replace A n (Npos p) x) end end end.
Fixpoint map_or (m0 m1 : Map bool) {struct m1} : Map bool := match m0, m1 with | M0, _ => M0 bool | _, M0 => M0 bool | M1 a0 b0, M1 a1 b1 => if N.eqb a0 a1 then M1 bool a0 (b0 || b1) else M0 bool | M1 _ _, M2 _ _ => M0 bool | M2 _ _, M1 _ _ => M0 bool | M2 x0 y0, M2 x1 y1 => M2 bool (map_or x0 x1) (map_or y0 y1) end.
Fixpoint pl_coacc (d : preDTA) (pl : prec_list) {struct pl} : Map bool := match pl with | prec_empty => map_mini state d | prec_cons a la ls => map_replace bool (map_or (pl_coacc d la) (pl_coacc d ls)) a true end.
Fixpoint st_coacc (d : preDTA) (s : state) {struct s} : Map bool := match s with | M0 => map_mini state d | M1 a pl => pl_coacc d pl | M2 x y => map_or (st_coacc d x) (st_coacc d y) end.
Fixpoint predta_coacc_0 (d d' : preDTA) {struct d'} : Map bool -> Map bool := fun m : Map bool => match d', m with | M0, M0 => map_mini state d | M1 a s, M1 a' b => if N.eqb a a' && b then st_coacc d s else map_mini state d | M2 x y, M2 z t => map_or (predta_coacc_0 d x z) (predta_coacc_0 d y t) | _, _ => map_mini state d end.
Definition predta_coacc (d : preDTA) (a : ad) (m : Map bool) : Map bool := map_replace bool (predta_coacc_0 d d m) a true.
Definition predta_coacc_states (d : preDTA) (a : ad) : Map bool := power (Map bool) (predta_coacc d a) (map_mini state d) (S (MapCard state d)).
Definition predta_coacc_states_0 (d : preDTA) (a : ad) : Map bool := lazy_power bool eqm_bool (predta_coacc d a) (map_mini state d) (S (MapCard state d)).
Definition lemd (d : preDTA) : mRelation bool := fun m0 m1 : Map bool => ensemble_base state d m0 /\ ensemble_base state d m1 /\ lem m0 m1.
Definition lattice_lemd_bounded_0_def (p : prechain bool) : Prop := forall d : preDTA, chain bool (ensemble_base state d) (lemd d) p -> chain bool (ensemble_base state d) lem p.
Definition lattice_lemd_bounded_1_def (p : prechain bool) : Prop := lattice_lemd_bounded_0_def p -> forall m : Map bool, lattice_lemd_bounded_0_def (concat bool p m).
Definition predta_coacc_contain_coacc_ads_def_0 (d : preDTA) (a0 a1 : ad) : Prop := coacc d a0 a1 -> preDTA_ref_ok d -> exists n : nat, MapGet bool (power (Map bool) (predta_coacc d a0) (map_mini state d) n) a1 = Some true.

Lemma predta_coacc_0_rev : forall (d d' : preDTA) (b : ad) (m : Map bool), MapGet bool (predta_coacc_0 d d' m) b = Some true -> ensemble_base state d' m -> exists a : ad, (exists s : state, (exists c : ad, (exists p : prec_list, MapGet state d' a = Some s /\ MapGet prec_list s c = Some p /\ prec_occur p b /\ MapGet bool m a = Some true))).
Proof.
simple induction d'; intros.
induction m as [| a a0| m1 Hrecm1 m0 Hrecm0].
simpl in H.
elim (map_mini_mapget_true _ _ _ H).
inversion H0.
inversion H0.
induction m as [| a1 a2| m1 Hrecm1 m0 Hrecm0].
inversion H0.
unfold ensemble_base in H0.
simpl in H0.
rewrite <- H0 in H.
rewrite <- H0.
simpl in H.
rewrite (Neqb_correct a) in H.
elim (bool_is_true_or_false a2); intros; rewrite H1 in H.
simpl in H.
split with a.
split with a0.
elim (st_coacc_rev _ _ _ H).
intros.
elim H2.
intros.
split with x.
split with x0.
simpl in |- *.
rewrite (Neqb_correct a).
rewrite H1.
elim H3.
intros.
split.
reflexivity.
split.
assumption.
split.
assumption.
reflexivity.
simpl in H.
elim (map_mini_mapget_true _ _ _ H).
inversion H0.
induction m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
inversion H2.
inversion H2.
clear Hrecm1_0 Hrecm1_1.
unfold ensemble_base in H2.
elim H2.
intros.
simpl in H1.
elim (map_or_mapget_true_inv _ _ _ H1).
intros.
elim (H _ _ H5 H3).
intros.
elim H6.
intros.
elim H7.
intros.
elim H8.
intros.
decompose [and] H9.
split with (N.double x).
split with x0.
split with x1.
split with x2.
split.
induction x as [| p]; simpl in |- *; exact H10.
split.
exact H12.
split.
exact H11.
induction x as [| p]; simpl in |- *; exact H14.
intros.
elim (H0 _ _ H5 H4).
intros.
elim H6.
intros.
elim H7.
intros.
elim H8.
intros.
decompose [and] H9.
split with (Ndouble_plus_one x).
split with x0.
split with x1.
split with x2.
induction x as [| p]; simpl in |- *; exact H9.
