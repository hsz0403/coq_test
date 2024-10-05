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

Lemma map_or_mapget_true_r : forall (m0 m1 : Map bool) (a : ad), domain_equal bool bool m0 m1 -> MapGet bool m0 a = Some true -> MapGet bool (map_or m1 m0) a = Some true.
Proof.
simple induction m0.
intros.
inversion H0.
simple induction m1; intros.
inversion H.
simpl in H.
simpl in H0.
rewrite <- H.
elim (bool_is_true_or_false (N.eqb a a3)); intros; rewrite H1 in H0; inversion H0.
rewrite <- (Neqb_complete _ _ H1).
simpl in |- *.
rewrite (Neqb_correct a).
simpl in |- *.
rewrite (Neqb_correct a).
elim (bool_is_true_or_false a2); intros; rewrite H2; reflexivity.
inversion H1.
intros.
induction m2 as [| a0 a1| m2_1 Hrecm2_1 m2_0 Hrecm2_0].
inversion H1.
inversion H1.
simpl in |- *.
elim H1; intros.
induction a as [| p].
exact (H _ _ H3 H2).
induction p as [p Hrecp| p Hrecp| ].
exact (H0 _ _ H4 H2).
exact (H _ _ H3 H2).
Admitted.

Lemma map_or_mapget_true_rd : forall (d : preDTA) (m0 m1 : Map bool) (a : ad), ensemble_base state d m0 -> ensemble_base state d m1 -> MapGet bool m1 a = Some true -> MapGet bool (map_or m0 m1) a = Some true.
Proof.
intros.
Admitted.

Lemma map_or_mapget_true_inv : forall (m0 m1 : Map bool) (a : ad), MapGet bool (map_or m0 m1) a = Some true -> MapGet bool m0 a = Some true \/ MapGet bool m1 a = Some true.
Proof.
simple induction m0; intros.
induction m1 as [| a0 a1| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
simpl in H.
inversion H.
simpl in H.
inversion H.
simpl in H.
inversion H.
induction m1 as [| a2 a3| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
simpl in H.
inversion H.
simpl in H.
elim (bool_is_true_or_false (N.eqb a a2)); intros; rewrite H0 in H.
simpl in H.
elim (bool_is_true_or_false (N.eqb a a1)); intros; rewrite H1 in H; inversion H.
rewrite H3.
elim (bool_is_true_or_false a0); intros; rewrite H2 in H3; rewrite H2.
left.
rewrite <- (Neqb_complete _ _ H1).
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
elim (bool_is_true_or_false a3); intros; rewrite H4 in H3; rewrite H4.
right.
rewrite <- (Neqb_complete _ _ H0).
rewrite <- (Neqb_complete _ _ H1).
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
inversion H3.
inversion H.
inversion H.
induction m2 as [| a0 a1| m2_1 Hrecm2_1 m2_0 Hrecm2_0].
inversion H1.
inversion H1.
simpl in H1.
induction a as [| p].
elim (H _ _ H1).
intros.
left.
simpl in |- *.
assumption.
intros.
right.
simpl in |- *.
assumption.
induction p as [p Hrecp| p Hrecp| ].
elim (H0 _ _ H1); intros; simpl in |- *.
left.
assumption.
right.
assumption.
elim (H _ _ H1); intros; simpl in |- *.
left.
assumption.
right.
assumption.
elim (H0 _ _ H1); intros; simpl in |- *.
left.
assumption.
right.
Admitted.

Lemma map_replace_mapget_ins_true_0 : forall (m : Map bool) (a : ad) (b : bool), MapGet bool m a = Some b -> MapGet bool (map_replace bool m a true) a = Some true.
Proof.
simple induction m.
intros.
inversion H.
intros.
simpl in H.
elim (bool_is_true_or_false (N.eqb a a1)); intros; rewrite H0 in H; inversion H.
simpl in |- *.
rewrite <- (Neqb_complete _ _ H0).
rewrite (Neqb_correct a).
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
intros.
induction a as [| p]; simpl in H1.
simpl in |- *.
exact (H _ _ H1).
induction p as [p Hrecp| p Hrecp| ]; simpl in |- *.
exact (H0 _ _ H1).
exact (H _ _ H1).
Admitted.

Lemma map_replace_mapget_ins_true_1 : forall (m : Map bool) (a a' : ad), MapGet bool m a = Some true -> MapGet bool (map_replace bool m a' true) a = Some true.
Proof.
simple induction m.
intros.
inversion H.
intros.
simpl in H.
elim (bool_is_true_or_false (N.eqb a a1)); intros; rewrite H0 in H.
inversion H.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb a' a)); intros; rewrite H1.
simpl in |- *.
rewrite H0.
reflexivity.
simpl in |- *.
rewrite H0.
reflexivity.
inversion H.
intros.
induction a as [| p]; simpl in H1; simpl in |- *.
induction a' as [| p].
simpl in |- *.
exact (H _ _ H1).
induction p as [p Hrecp| p Hrecp| ].
simpl in |- *.
exact H1.
exact (H _ _ H1).
exact H1.
induction p as [p Hrecp| p Hrecp| ].
induction a' as [| p0]; simpl in |- *.
exact H1.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in |- *.
exact (H0 _ _ H1).
exact H1.
exact (H0 _ _ H1).
induction a' as [| p0]; simpl in |- *.
exact (H _ _ H1).
induction p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in |- *.
exact H1.
exact (H _ _ H1).
exact H1.
induction a' as [| p]; simpl in |- *.
exact H1.
induction p as [p Hrecp| p Hrecp| ]; simpl in |- *.
exact (H0 _ _ H1).
exact H1.
Admitted.

Lemma map_replace_mapget_true_inv : forall (m : Map bool) (a b : ad), MapGet bool (map_replace bool m a true) b = Some true -> b = a \/ MapGet bool m b = Some true.
Proof.
simple induction m.
intros.
inversion H.
simpl in |- *.
intros.
elim (bool_is_true_or_false (N.eqb a1 a)); intros; rewrite H0 in H.
simpl in H.
elim (bool_is_true_or_false (N.eqb a b)); intros; rewrite H1 in H.
rewrite H1.
left.
rewrite (Neqb_complete _ _ H0).
rewrite <- (Neqb_complete _ _ H1).
reflexivity.
inversion H.
simpl in H.
elim (bool_is_true_or_false (N.eqb a b)); intros; rewrite H1 in H; inversion H.
rewrite H1.
right.
reflexivity.
intros.
simpl in H1.
induction a as [| p]; simpl in H1.
induction b as [| p]; simpl in |- *; simpl in H1.
exact (H _ _ H1).
induction p as [p Hrecp| p Hrecp| ].
right.
exact H1.
elim (H _ _ H1).
intros.
inversion H2.
intros.
right.
exact H2.
right.
exact H1.
induction p as [p Hrecp| p Hrecp| ].
induction b as [| p0].
simpl in |- *.
simpl in H1.
right.
exact H1.
simpl in H1.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
elim (H0 _ _ H1).
intros.
inversion H2.
left.
reflexivity.
intros.
simpl in |- *.
right.
exact H2.
simpl in |- *.
right.
exact H1.
elim (H0 _ _ H1).
intros.
inversion H2.
intros.
simpl in |- *.
right.
exact H2.
induction b as [| p0]; simpl in |- *; simpl in H1.
elim (H _ _ H1).
intros.
inversion H2.
right.
exact H2.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
right.
exact H1.
elim (H _ _ H1).
intros.
inversion H2.
left.
reflexivity.
intros.
right.
exact H2.
right.
exact H1.
induction b as [| p].
simpl in H1.
simpl in |- *.
right.
exact H1.
induction p as [p Hrecp| p Hrecp| ]; simpl in |- *; simpl in H1.
elim (H0 _ _ H1).
intros.
inversion H2.
intros.
right.
exact H2.
right.
exact H1.
left.
Admitted.

Lemma map_or_def_ok : forall m0 m1 : Map bool, domain_equal bool bool m0 m1 -> domain_equal bool bool m0 (map_or m0 m1).
Proof.
simple induction m0.
simple induction m1.
intros.
exact I.
intros.
inversion H.
intros.
inversion H1.
simple induction m1.
intros.
inversion H.
intros.
simpl in H.
simpl in |- *.
rewrite H.
rewrite (Neqb_correct a1).
simpl in |- *.
reflexivity.
intros.
inversion H1.
simple induction m2.
intros.
inversion H1.
intros.
inversion H1.
intros.
elim H3.
intros.
simpl in |- *.
split.
exact (H _ H4).
Admitted.

Lemma map_or_def_ok_d : forall (d : preDTA) (m0 m1 : Map bool), ensemble_base state d m0 -> ensemble_base state d m1 -> ensemble_base state d (map_or m0 m1).
Proof.
unfold ensemble_base in |- *.
intros.
apply (domain_equal_transitive state bool bool d m0 (map_or m0 m1)).
exact H.
apply (map_or_def_ok m0 m1).
apply (domain_equal_transitive bool state bool m0 d m1).
exact (domain_equal_symmetric state bool d m0 H).
Admitted.

Lemma map_replace_def_ok : forall (A : Set) (m : Map A) (a : ad) (x : A), domain_equal A A m (map_replace A m a x).
Proof.
intro.
simple induction m.
intros.
exact I.
intros.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb a1 a)); intros; rewrite H.
simpl in |- *.
reflexivity.
simpl in |- *.
reflexivity.
intros.
simpl in |- *.
induction a as [| p].
simpl in |- *.
split.
exact (H N0 x).
exact (domain_equal_reflexive A m1).
induction p as [p Hrecp| p Hrecp| ].
split.
exact (domain_equal_reflexive A m0).
exact (H0 (Npos p) x).
split.
exact (H (Npos p) x).
exact (domain_equal_reflexive A m1).
split.
exact (domain_equal_reflexive A m0).
Admitted.

Lemma map_replace_def_ok_d : forall (d : preDTA) (m : Map bool) (a : ad) (x : bool), ensemble_base state d m -> ensemble_base state d (map_replace bool m a x).
Proof.
unfold ensemble_base in |- *.
intros.
apply (domain_equal_transitive state bool bool d m (map_replace bool m a x) H).
Admitted.

Lemma st_coacc_def_ok : forall (d : preDTA) (s : state), ensemble_base state d (st_coacc d s).
Proof.
simple induction s.
simpl in |- *.
exact (map_mini_appartient state d).
simpl in |- *.
intros.
exact (pl_coacc_def_ok d a0).
intros.
simpl in |- *.
Admitted.

Lemma predta_coacc_0_def_ok : forall (d d' : preDTA) (m : Map bool), ensemble_base state d (predta_coacc_0 d d' m).
Proof.
simple induction d'.
simpl in |- *.
intros.
induction m as [| a a0| m1 Hrecm1 m0 Hrecm0]; exact (map_mini_appartient state d).
simpl in |- *.
intros.
induction m as [| a1 a2| m1 Hrecm1 m0 Hrecm0].
exact (map_mini_appartient state d).
elim (bool_is_true_or_false (N.eqb a a1 && a2)); intros; rewrite H.
exact (st_coacc_def_ok d a0).
exact (map_mini_appartient state d).
exact (map_mini_appartient state d).
intros.
induction m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
simpl in |- *.
exact (map_mini_appartient state d).
simpl in |- *.
exact (map_mini_appartient state d).
simpl in |- *.
Admitted.

Lemma predta_coacc_def_ok : forall (d : preDTA) (a : ad) (m : Map bool), ensemble_base state d (predta_coacc d a m).
Proof.
unfold predta_coacc in |- *.
intros.
Admitted.

Lemma lemd_reflexive : forall (d : preDTA) (m : Map bool), ensemble_base state d m -> lemd d m m.
Proof.
unfold ensemble_base in |- *.
simple induction d.
intros.
unfold lemd in |- *.
unfold ensemble_base in |- *.
induction m as [| a a0| m1 Hrecm1 m0 Hrecm0].
split.
exact I.
split; exact I.
inversion H.
inversion H.
intros.
unfold lemd in |- *.
unfold ensemble_base in |- *.
induction m as [| a1 a2| m1 Hrecm1 m0 Hrecm0].
inversion H.
simpl in H.
rewrite H.
simpl in |- *.
split.
reflexivity.
split.
reflexivity.
rewrite (Neqb_correct a1).
exact (leb_reflexive a2).
inversion H.
unfold lemd in |- *.
unfold ensemble_base in |- *.
simple induction m1.
intros.
inversion H1.
intros.
inversion H1.
intros.
elim H3.
intros.
elim (H _ H4).
elim (H0 _ H5).
intros.
split; split.
exact H4.
exact H5.
split.
exact H4.
exact H5.
split.
elim H9.
intros.
exact H11.
elim H7.
intros.
Admitted.

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
Admitted.

Lemma lemd_transitive : forall (d : preDTA) (m0 m1 m2 : Map bool), lemd d m0 m1 -> lemd d m1 m2 -> lemd d m0 m2.
Proof.
simple induction d.
unfold lemd in |- *.
unfold ensemble_base in |- *.
intros.
decompose [and] H.
decompose [and] H0.
induction m0 as [| a a0| m0_1 Hrecm0_1 m0_0 Hrecm0_0].
induction m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
induction m2 as [| a a0| m2_1 Hrecm2_1 m2_0 Hrecm2_0].
split.
exact I.
split; exact I.
inversion H6.
inversion H7.
inversion H2.
inversion H2.
inversion H1.
inversion H1.
unfold lemd in |- *.
unfold ensemble_base in |- *.
intros.
decompose [and] H.
decompose [and] H0.
induction m0 as [| a1 a2| m0_1 Hrecm0_1 m0_0 Hrecm0_0].
inversion H1.
induction m1 as [| a3 a4| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
inversion H2.
induction m2 as [| a5 a6| m2_1 Hrecm2_1 m2_0 Hrecm2_0].
inversion H6.
simpl in H2.
simpl in H1.
simpl in H6.
simpl in H4.
rewrite <- H2 in H4.
rewrite <- H1 in H4.
rewrite (Neqb_correct a) in H4.
simpl in H7.
rewrite <- H3 in H7.
rewrite <- H6 in H7.
rewrite (Neqb_correct a) in H7.
rewrite <- H1.
rewrite <- H6.
split.
simpl in |- *.
reflexivity.
simpl in |- *.
split.
reflexivity.
rewrite (Neqb_correct a).
exact (leb_transitive _ _ _ H4 H7).
inversion H6.
inversion H3.
inversion H1.
unfold lemd in |- *.
unfold ensemble_base in |- *.
intros.
decompose [and] H1.
decompose [and] H2.
induction m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
inversion H3.
inversion H3.
clear Hrecm1_1 Hrecm1_0.
induction m2 as [| a a0| m2_1 Hrecm2_1 m2_0 Hrecm2_0].
inversion H5.
inversion H5.
clear Hrecm2_1.
clear Hrecm2_0.
intros.
induction m3 as [| a a0| m3_1 Hrecm3_1 m3_0 Hrecm3_0].
inversion H8.
inversion H8.
clear Hrecm3_1.
clear Hrecm3_0.
simpl in |- *.
elim H3.
elim H8.
elim H6.
elim H5.
elim H9.
intros.
split.
split.
exact H17.
exact H18.
split.
split.
exact H15.
exact H16.
split.
exact (lem_transitive _ _ _ H13 H7).
Admitted.

Lemma map_or_inc_ld : forall (d : preDTA) (m m0 m1 : Map bool), ensemble_base state d m -> lemd d m0 m1 -> lemd d (map_or m0 m) (map_or m1 m).
Proof.
unfold lemd in |- *.
unfold ensemble_base in |- *.
simple induction d.
intros.
decompose [and] H0.
induction m as [| a a0| m2 Hrecm1 m3 Hrecm0].
induction m0 as [| a a0| m0_1 Hrecm0_1 m0_0 Hrecm0_0].
induction m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
simpl in |- *.
split.
exact I.
split; exact I.
inversion H3.
inversion H3.
inversion H1.
inversion H1.
inversion H.
inversion H.
intros.
decompose [and] H0.
induction m as [| a1 a2| m2 Hrecm1 m3 Hrecm0].
inversion H.
induction m0 as [| a3 a4| m0_1 Hrecm0_1 m0_0 Hrecm0_0].
inversion H1.
induction m1 as [| a5 a6| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
inversion H3.
simpl in |- *.
simpl in H1.
simpl in H3.
simpl in H4.
simpl in H.
rewrite <- H.
rewrite <- H3.
rewrite <- H1.
rewrite (Neqb_correct a).
simpl in |- *.
rewrite (Neqb_correct a).
split.
reflexivity.
split.
reflexivity.
rewrite <- H3 in H4.
rewrite <- H1 in H4.
rewrite (Neqb_correct a) in H4.
exact (orb_inc_l a2 _ _ H4).
inversion H4.
inversion H1.
inversion H.
intros.
decompose [and] H2.
induction m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
inversion H1.
inversion H1.
induction m2 as [| a a0| m2_1 Hrecm2_1 m2_0 Hrecm2_0].
inversion H3.
inversion H3.
induction m3 as [| a a0| m3_1 Hrecm3_1 m3_0 Hrecm3_0].
inversion H5.
inversion H5.
clear Hrecm3_1 Hrecm3_0 Hrecm2_1 Hrecm2_0 Hrecm1_1 Hrecm1_0.
simpl in |- *.
elim H5.
elim H3.
elim H6.
intros.
elim H1.
intros.
elim (H m1_1 m2_1 m3_1).
elim (H0 m1_0 m2_0 m3_0).
intros.
split.
split; assumption.
split.
split.
elim H17; intros.
assumption.
elim H15; intros; assumption.
elim H15.
intros.
elim H17.
intros.
split; assumption.
assumption.
split.
assumption.
split; assumption.
assumption.
split.
assumption.
Admitted.

Lemma map_or_inc_rd : forall (d : preDTA) (m m0 m1 : Map bool), ensemble_base state d m -> lemd d m0 m1 -> lemd d (map_or m m0) (map_or m m1).
Proof.
unfold lemd in |- *.
unfold ensemble_base in |- *.
simple induction d.
intros.
decompose [and] H0.
induction m as [| a a0| m2 Hrecm1 m3 Hrecm0].
induction m0 as [| a a0| m0_1 Hrecm0_1 m0_0 Hrecm0_0].
induction m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
simpl in |- *.
split.
exact I.
split; exact I.
inversion H3.
inversion H3.
inversion H1.
inversion H1.
inversion H.
inversion H.
intros.
decompose [and] H0.
induction m as [| a1 a2| m2 Hrecm1 m3 Hrecm0].
inversion H.
induction m0 as [| a3 a4| m0_1 Hrecm0_1 m0_0 Hrecm0_0].
inversion H1.
induction m1 as [| a5 a6| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
inversion H3.
simpl in |- *.
simpl in H1.
simpl in H3.
simpl in H4.
simpl in H.
rewrite <- H.
rewrite <- H3.
rewrite <- H1.
rewrite (Neqb_correct a).
simpl in |- *.
rewrite (Neqb_correct a).
split.
reflexivity.
split.
reflexivity.
rewrite <- H3 in H4.
rewrite <- H1 in H4.
rewrite (Neqb_correct a) in H4.
exact (orb_inc_r a2 _ _ H4).
inversion H4.
inversion H1.
inversion H.
intros.
decompose [and] H2.
induction m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
inversion H1.
inversion H1.
induction m2 as [| a a0| m2_1 Hrecm2_1 m2_0 Hrecm2_0].
inversion H3.
inversion H3.
induction m3 as [| a a0| m3_1 Hrecm3_1 m3_0 Hrecm3_0].
inversion H5.
inversion H5.
clear Hrecm3_1 Hrecm3_0 Hrecm2_1 Hrecm2_0 Hrecm1_1 Hrecm1_0.
simpl in |- *.
elim H5.
elim H3.
elim H6.
intros.
elim H1.
intros.
elim (H m1_1 m2_1 m3_1).
elim (H0 m1_0 m2_0 m3_0).
intros.
split.
split; assumption.
split.
split.
elim H17; intros.
assumption.
elim H15; intros; assumption.
elim H15.
intros.
elim H17.
intros.
split; assumption.
assumption.
split.
assumption.
split; assumption.
assumption.
split.
assumption.
Admitted.

Lemma map_or_inc_d : forall (d : preDTA) (m0 m1 m2 m3 : Map bool), lemd d m0 m1 -> lemd d m2 m3 -> lemd d (map_or m0 m2) (map_or m1 m3).
Proof.
intros.
apply (lemd_transitive d (map_or m0 m2) (map_or m1 m2) (map_or m1 m3)).
apply (map_or_inc_ld d m2 m0 m1).
unfold lemd in H0.
decompose [and] H0.
exact H1.
exact H.
apply (map_or_inc_rd d m1 m2 m3).
unfold lemd in H.
decompose [and] H.
exact H3.
Admitted.

Lemma predta_coacc_0_incr : forall (d d' : preDTA) (m0 m1 : Map bool), lemd d' m0 m1 -> lemd d (predta_coacc_0 d d' m0) (predta_coacc_0 d d' m1).
Proof.
unfold lemd in |- *.
unfold ensemble_base in |- *.
simple induction d'.
intros.
decompose [and] H.
induction m0 as [| a a0| m0_1 Hrecm0_1 m0_0 Hrecm0_0].
induction m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
simpl in |- *.
split.
exact (map_mini_appartient state d).
split.
exact (map_mini_appartient state d).
exact (lem_reflexive (map_mini state d)).
inversion H2.
inversion H2.
induction m1 as [| a1 a2| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
inversion H0.
simpl in H3.
simpl in |- *.
apply (lemd_reflexive d (map_mini state d)).
exact (map_mini_appartient state d).
inversion H2.
simpl in |- *.
induction m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0]; exact (lemd_reflexive d (map_mini state d) (map_mini_appartient state d)).
intros.
decompose [and] H.
induction m0 as [| a1 a2| m0_1 Hrecm0_1 m0_0 Hrecm0_0].
induction m1 as [| a1 a2| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
simpl in |- *.
exact (lemd_reflexive d (map_mini state d) (map_mini_appartient state d)).
inversion H0.
inversion H0.
induction m1 as [| a3 a4| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
inversion H2.
simpl in |- *.
simpl in H0.
simpl in H2.
simpl in H3.
rewrite <- H0; rewrite <- H2; rewrite <- H0 in H3; rewrite <- H2 in H3.
rewrite (Neqb_correct a); simpl in |- *.
rewrite (Neqb_correct a) in H3.
elim (bool_is_true_or_false a2); intros; rewrite H1; elim (bool_is_true_or_false a4); intros; rewrite H4.
exact (lemd_reflexive d (st_coacc d a0) (st_coacc_def_ok d a0)).
rewrite H4 in H3.
rewrite H1 in H3.
inversion H3.
split.
exact (map_mini_appartient state d).
split.
exact (st_coacc_def_ok d a0).
elim (map_mini_mini state d).
intros.
exact (H6 (st_coacc d a0) (st_coacc_def_ok d a0)).
exact (lemd_reflexive d (map_mini state d) (map_mini_appartient state d)).
inversion H3.
inversion H0.
intros.
decompose [and] H1.
induction m1 as [| a a0| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
inversion H2.
inversion H2.
induction m2 as [| a a0| m2_1 Hrecm2_1 m2_0 Hrecm2_0].
inversion H4.
inversion H4.
clear Hrecm2_0 Hrecm2_1 Hrecm1_0 Hrecm1_1.
elim H5.
intros.
elim H4.
elim H2.
intros.
simpl in |- *.
elim (H m1_1 m2_1).
intros.
elim H12.
intros.
elim (H0 m1_0 m2_0).
intros.
elim H16.
intros.
split.
exact (map_or_def_ok_d d _ _ H11 H15).
split.
exact (map_or_def_ok_d _ _ _ H13 H17).
elim (map_or_inc_d d (predta_coacc_0 d m m1_1) (predta_coacc_0 d m m2_1) (predta_coacc_0 d m0 m1_0) (predta_coacc_0 d m0 m2_0)).
intros.
elim H20.
intros.
exact H22.
unfold lemd in |- *.
split.
assumption.
split; assumption.
unfold lemd in |- *.
split.
assumption.
split; assumption.
split.
assumption.
split; assumption.
split.
assumption.
Admitted.

Lemma pl_coacc_def_ok : forall (d : preDTA) (pl : prec_list), ensemble_base state d (pl_coacc d pl).
Proof.
simple induction pl.
simpl in |- *.
intros.
exact (map_replace_def_ok_d d (map_or (pl_coacc d p) (pl_coacc d p0)) a true (map_or_def_ok_d _ _ _ H H0)).
simpl in |- *.
exact (map_mini_appartient state d).
