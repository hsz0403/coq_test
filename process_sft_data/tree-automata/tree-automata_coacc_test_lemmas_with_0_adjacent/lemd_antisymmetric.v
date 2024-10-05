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

Lemma lemd_antisymmetric : forall (d : preDTA) (m0 m1 : Map bool), lemd d m0 m1 -> lemd d m1 m0 -> m0 = m1.
Proof.
unfold lemd in |- *.
unfold ensemble_base in |- *.
simple induction d.
simple induction m0.
intros.
elim H.
intros.
elim H0.
intros.
elim H4.
intros.
induction m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
reflexivity.
inversion H6.
inversion H6.
intros.
elim H0.
intros.
elim H2.
intros.
decompose [and] H.
induction m1 as [| a1 a2| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
inversion H8.
inversion H5.
inversion H8.
intros.
decompose [and] H1.
inversion H3.
intros.
decompose [and] H.
decompose [and] H0.
induction m0 as [| a1 a2| m0_1 Hrecm0_1 m0_0 Hrecm0_0].
inversion H1.
induction m1 as [| a3 a4| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
inversion H3.
simpl in H1.
simpl in H2.
rewrite <- H1.
rewrite <- H2.
simpl in H4.
simpl in H7.
rewrite <- H2 in H4.
rewrite <- H1 in H4.
rewrite (Neqb_correct a) in H4.
rewrite <- H1 in H7.
rewrite <- H2 in H7.
rewrite (Neqb_correct a) in H7.
rewrite (leb_antisymmetric _ _ H4 H7).
reflexivity.
inversion H2.
inversion H1.
intros.
decompose [and] H1.
decompose [and] H2.
induction m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
inversion H3.
inversion H3.
induction m2 as [| a a0| m2_1 Hrecm2_1 m2_0 Hrecm2_0].
inversion H4.
inversion H9.
elim H4.
elim H3.
elim H6.
intros.
rewrite (H m1_1 m2_1).
rewrite (H0 m1_0 m2_0).
reflexivity.
split.
exact H12.
split.
exact H14.
exact H10.
split.
exact H14.
split.
exact H12.
elim H9.
intros.
exact H16.
elim H9.
intros.
split.
exact H11.
split.
exact H13.
exact H7.
elim H9.
intros.
split.
exact H13.
split.
exact H11.
exact H15.
