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

Lemma predta_coacc_0_contain_coacc_ads : forall (d d' : preDTA) (a : ad) (s : state) (c : ad) (p : prec_list) (b : ad) (m : Map bool), preDTA_ref_ok_distinct d' d -> MapGet state d' a = Some s -> MapGet prec_list s c = Some p -> prec_occur p b -> ensemble_base state d' m -> MapGet bool m a = Some true -> MapGet bool (predta_coacc_0 d d' m) b = Some true.
Proof.
simple induction d'.
intros.
inversion H0.
simpl in |- *.
intros.
induction m as [| a2 a3| m1 Hrecm1 m0 Hrecm0].
inversion H3.
unfold ensemble_base in H3.
simpl in H3.
rewrite <- H3.
rewrite (Neqb_correct a).
simpl in H4.
elim (bool_is_true_or_false (N.eqb a2 a1)); intros; rewrite H5 in H4; inversion H4.
simpl in |- *.
apply (st_coacc_contain_coacc_ads d a0 c p b).
elim (bool_is_true_or_false (N.eqb a a1)); intros; rewrite H6 in H0; inversion H0.
rewrite H9 in H.
apply (H a s).
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
elim (bool_is_true_or_false (N.eqb a a1)); intros; rewrite H6 in H0.
inversion H0.
exact H1.
inversion H0.
exact H2.
inversion H3.
intros.
induction m1 as [| a0 a1| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
inversion H5.
inversion H5.
elim H5.
intros.
elim (preDTA_ref_ok_distinct_dest _ _ _ H1).
intros.
simpl in |- *.
induction a as [| p0].
simpl in H6.
simpl in H2.
apply (map_or_mapget_true_ld _ _ _ b (predta_coacc_0_def_ok d m m1_1) (predta_coacc_0_def_ok d m0 m1_0)).
exact (H _ _ _ _ _ _ H9 H2 H3 H4 H7 H6).
induction p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in H2; simpl in H6.
apply (map_or_mapget_true_rd _ _ _ b (predta_coacc_0_def_ok d m m1_1) (predta_coacc_0_def_ok d m0 m1_0)).
exact (H0 _ _ _ _ _ _ H10 H2 H3 H4 H8 H6).
exact (map_or_mapget_true_ld _ _ _ b (predta_coacc_0_def_ok d m m1_1) (predta_coacc_0_def_ok d m0 m1_0) (H _ _ _ _ _ _ H9 H2 H3 H4 H7 H6)).
exact (map_or_mapget_true_rd _ _ _ b (predta_coacc_0_def_ok d m m1_1) (predta_coacc_0_def_ok d m0 m1_0) (H0 _ _ _ _ _ _ H10 H2 H3 H4 H8 H6)).
