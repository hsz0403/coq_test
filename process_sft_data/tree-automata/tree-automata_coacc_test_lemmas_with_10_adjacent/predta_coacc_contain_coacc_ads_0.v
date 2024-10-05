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

Lemma predta_coacc_increasing : forall (d : preDTA) (a : ad), increasing_app bool (lemd d) (predta_coacc d a).
Proof.
unfold increasing_app in |- *.
unfold predta_coacc in |- *.
intros.
Admitted.

Lemma lattice_lemd_bounded_0 : forall m : Map bool, lattice_lemd_bounded_0_def (single bool m).
Proof.
unfold lattice_lemd_bounded_0_def in |- *.
intros.
inversion H.
Admitted.

Lemma lattice_lemd_bounded_1 : forall m : Map bool, lattice_lemd_bounded_1_def (single bool m).
Proof.
unfold lattice_lemd_bounded_1_def in |- *.
unfold lattice_lemd_bounded_0_def in |- *.
intros.
inversion H0.
inversion H7.
inversion H9.
Admitted.

Lemma lattice_lemd_bounded_2 : forall p : prechain bool, lattice_lemd_bounded_1_def p -> forall m : Map bool, lattice_lemd_bounded_1_def (concat bool p m).
Proof.
unfold lattice_lemd_bounded_1_def in |- *.
unfold lattice_lemd_bounded_0_def in |- *.
intros.
inversion H1.
inversion H8.
inversion H11.
Admitted.

Lemma lattice_lemd_bounded_3 : forall (p : prechain bool) (d : preDTA), chain bool (ensemble_base state d) (lemd d) p -> chain bool (ensemble_base state d) lem p.
Proof.
Admitted.

Lemma lattice_lemd_bounded : forall (p : prechain bool) (d : preDTA), sas_chain bool (ensemble_base state d) (lemd d) p -> sas_chain bool (ensemble_base state d) lem p.
Proof.
intros.
inversion H.
split.
exact (lattice_lemd_bounded_3 p d H0).
Admitted.

Lemma lattice_bounded : forall d : preDTA, bounded_sas_chain bool (ensemble_base state d) (lemd d) (S (MapCard state d)).
Proof.
unfold bounded_sas_chain in |- *.
intros.
Admitted.

Lemma pl_coacc_contain_coacc_ads : forall (d : preDTA) (p : prec_list) (a : ad), prec_occur p a -> prec_list_ref_ok p d -> MapGet bool (pl_coacc d p) a = Some true.
Proof.
simple induction p.
intros.
inversion H1.
simpl in |- *.
elim (H2 _ H1).
intros.
elim (domain_equal_mapget state bool d (map_or (pl_coacc d p0) (pl_coacc d p1)) a0 x (map_or_def_ok_d _ _ _ (pl_coacc_def_ok d p0) (pl_coacc_def_ok d p1)) H7).
intros.
exact (map_replace_mapget_ins_true_0 _ _ _ H8).
simpl in |- *.
apply (map_replace_mapget_ins_true_1 (map_or (pl_coacc d p0) (pl_coacc d p1)) a0 a).
apply (map_or_mapget_true_ld _ _ _ a0 (pl_coacc_def_ok d p0) (pl_coacc_def_ok d p1)).
elim (prec_list_ref_ok_destr _ _ _ _ H2).
intros.
exact (H _ H7 H8).
simpl in |- *.
apply (map_replace_mapget_ins_true_1 (map_or (pl_coacc d p0) (pl_coacc d p1)) a0 a).
apply (map_or_mapget_true_rd _ _ _ a0 (pl_coacc_def_ok d p0) (pl_coacc_def_ok d p1)).
elim (prec_list_ref_ok_destr _ _ _ _ H2).
intros.
exact (H0 _ H7 H9).
simpl in |- *.
intros.
Admitted.

Lemma st_coacc_contain_coacc_ads : forall (d : preDTA) (s : state) (c : ad) (p : prec_list) (a : ad), state_ref_ok s d -> MapGet prec_list s c = Some p -> prec_occur p a -> MapGet bool (st_coacc d s) a = Some true.
Proof.
simple induction s.
intros.
inversion H0.
intros.
simpl in H0.
elim (bool_is_true_or_false (N.eqb a c)); intros; rewrite H2 in H0.
simpl in |- *.
apply (pl_coacc_contain_coacc_ads d a0 a1).
inversion H0.
exact H1.
apply (H a a0).
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
inversion H0.
intros.
elim (state_ref_ok_M2_destr _ _ _ H1); intros.
simpl in |- *.
induction c as [| p0].
simpl in H2.
apply (map_or_mapget_true_ld _ _ _ a (st_coacc_def_ok d m) (st_coacc_def_ok d m0)).
apply (H _ _ _ H4 H2 H3).
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
apply (map_or_mapget_true_rd _ _ _ a (st_coacc_def_ok d m) (st_coacc_def_ok d m0)).
exact (H0 _ _ _ H5 H2 H3).
apply (map_or_mapget_true_ld _ _ _ a (st_coacc_def_ok d m) (st_coacc_def_ok d m0)).
apply (H _ _ _ H4 H2 H3).
apply (map_or_mapget_true_rd _ _ _ a (st_coacc_def_ok d m) (st_coacc_def_ok d m0)).
Admitted.

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
Admitted.

Lemma predta_coacc_contain_coacc_ads_1 : forall (d : preDTA) (a : ad) (s : state), MapGet state d a = Some s -> predta_coacc_contain_coacc_ads_def_0 d a a.
Proof.
unfold predta_coacc_contain_coacc_ads_def_0 in |- *.
intros.
split with 1.
simpl in |- *.
unfold predta_coacc in |- *.
elim (domain_equal_mapget state bool d (predta_coacc_0 d d (map_mini state d)) a s (predta_coacc_0_def_ok d d (map_mini state d)) H).
intros.
Admitted.

Lemma predta_coacc_contain_coacc_ads_2 : forall (d : preDTA) (a0 a1 a2 : ad) (s1 s2 : state) (pl : prec_list) (c : ad), MapGet state d a2 = Some s2 -> MapGet state d a1 = Some s1 -> MapGet prec_list s1 c = Some pl -> prec_occur pl a2 -> coacc d a0 a1 -> predta_coacc_contain_coacc_ads_def_0 d a0 a1 -> predta_coacc_contain_coacc_ads_def_0 d a0 a2.
Proof.
unfold predta_coacc_contain_coacc_ads_def_0 in |- *.
intros.
elim (H4 H3 H6).
intros.
split with (S x).
simpl in |- *.
apply (predta_coacc_contain_coacc_ads_0 d a0 a1 s1 c pl a2 (power (Map bool) (predta_coacc d a0) (map_mini state d) x) H6 H0 H1 H2).
apply (power_def_ok bool (ensemble_base state d) (predta_coacc d a0) (map_mini state d) x).
unfold def_ok_app in |- *.
intros.
exact (predta_coacc_def_ok d a0 x0).
exact (map_mini_appartient state d).
Admitted.

Lemma predta_coacc_contain_coacc_ads_3 : forall (d : preDTA) (a0 a1 : ad), coacc d a0 a1 -> preDTA_ref_ok d -> exists n : nat, MapGet bool (power (Map bool) (predta_coacc d a0) (map_mini state d) n) a1 = Some true.
Proof.
intros.
Admitted.

Lemma pl_coacc_rev : forall (d : preDTA) (pl : prec_list) (a : ad), MapGet bool (pl_coacc d pl) a = Some true -> prec_occur pl a.
Proof.
simple induction pl.
simpl in |- *.
intros.
elim (map_replace_mapget_true_inv (map_or (pl_coacc d p) (pl_coacc d p0)) _ _ H1).
intros.
rewrite <- H2.
exact (prec_hd a0 p p0).
intros.
elim (map_or_mapget_true_inv (pl_coacc d p) (pl_coacc d p0) a0 H2).
intros.
exact (prec_int0 a a0 p p0 (H _ H3)).
intros.
exact (prec_int1 a a0 p p0 (H0 _ H3)).
intros.
simpl in H.
cut (true <> false).
intro.
elim (H0 (map_mini_mapget_false _ _ _ _ H)).
intro.
Admitted.

Lemma st_coacc_rev : forall (d : preDTA) (s : state) (a : ad), MapGet bool (st_coacc d s) a = Some true -> exists c : ad, (exists p : prec_list, MapGet prec_list s c = Some p /\ prec_occur p a).
Proof.
simple induction s.
intros.
simpl in H.
elim (map_mini_mapget_true _ _ _ H).
intros.
simpl in H.
split with a.
split with a0.
simpl in |- *.
rewrite (Neqb_correct a).
split.
reflexivity.
exact (pl_coacc_rev _ _ _ H).
intros.
simpl in H1.
elim (map_or_mapget_true_inv (st_coacc d m) (st_coacc d m0) a H1).
intros.
elim (H _ H2).
intros.
elim H3.
intros.
split with (N.double x).
split with x0.
induction x as [| p]; simpl in |- *; exact H4.
intros.
elim (H0 _ H2).
intros.
elim H3.
intros.
split with (Ndouble_plus_one x).
split with x0.
Admitted.

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
Admitted.

Lemma predta_coacc_rev : forall (d : preDTA) (a : ad) (m : Map bool) (b : ad), MapGet bool (predta_coacc d a m) b = Some true -> ensemble_base state d m -> (exists a0 : ad, (exists s : state, (exists c : ad, (exists p : prec_list, MapGet state d a0 = Some s /\ MapGet prec_list s c = Some p /\ prec_occur p b /\ MapGet bool m a0 = Some true)))) \/ a = b.
Proof.
unfold predta_coacc in |- *.
intros.
elim (map_replace_mapget_true_inv _ _ _ H).
intros.
right.
symmetry in |- *.
exact H1.
intros.
left.
elim (predta_coacc_0_rev d d b m H1 H0).
elim (predta_coacc_0_rev d d b m H1 H0).
intros.
elim H3.
intros.
elim H4.
intros.
elim H5.
intros.
decompose [and] H6.
split with x0.
split with x1.
Admitted.

Lemma predta_coacc_reverse : forall (n : nat) (d : preDTA) (a b : ad), MapGet bool (power (Map bool) (predta_coacc d a) (map_mini state d) n) b = Some true -> coacc d a b.
Proof.
simple induction n.
simpl in |- *.
intros.
elim (map_mini_mapget_true _ _ _ H).
intros.
simpl in H0.
elim (predta_coacc_rev d a _ _ H0).
intros.
elim H1.
intros.
elim H2.
intros.
elim H3.
intros.
elim H4.
intros.
decompose [and] H5.
elim (domain_equal_mapget bool state (predta_coacc d a (power (Map bool) (predta_coacc d a) (map_mini state d) n0)) d b true).
intros.
apply (coacc_nxt d a x b x0 x3 x2 x1 H9 H6 H8 H7).
exact (H d a x H10).
exact (domain_equal_symmetric state bool _ _ (predta_coacc_def_ok d a (power (Map bool) (predta_coacc d a) (map_mini state d) n0))).
exact H0.
intros.
rewrite H1.
elim (domain_equal_mapget bool state (predta_coacc d a (power (Map bool) (predta_coacc d a) (map_mini state d) n0)) d b true).
intros.
exact (coacc_id d b x H2).
apply (domain_equal_symmetric state bool d (predta_coacc d a (power (Map bool) (predta_coacc d a) (map_mini state d) n0))).
exact (predta_coacc_def_ok d a (power (Map bool) (predta_coacc d a) (map_mini state d) n0)).
exact H0.
apply (power_def_ok bool (ensemble_base state d) (predta_coacc d a) (map_mini state d) n0).
unfold def_ok_app in |- *.
intros.
exact (predta_coacc_def_ok d a x).
Admitted.

Lemma predta_coacc_fix_0 : forall (d : preDTA) (a : ad), lower_fix_point bool (ensemble_base state d) (lemd d) (predta_coacc d a) (predta_coacc_states d a).
Proof.
intros.
unfold predta_coacc_states in |- *.
apply (iteres_lower_fix_point bool (ensemble_base state d) (lemd d) (predta_coacc d a) (map_mini state d) (S (MapCard state d)) (S (MapCard state d))).
unfold mini in |- *.
split.
exact (map_mini_appartient state d).
intros.
split.
exact (map_mini_appartient state d).
split.
exact H.
elim (map_mini_mini state d).
intros.
exact (H1 x H).
unfold def_ok_app in |- *.
intros.
exact (predta_coacc_def_ok d a x).
exact (predta_coacc_increasing d a).
exact (lattice_bounded d).
Admitted.

Lemma predta_coacc_fix_1 : forall (d : preDTA) (a a0 : ad) (n : nat), MapGet bool (power (Map bool) (predta_coacc d a) (map_mini state d) n) a0 = Some true -> MapGet bool (predta_coacc_states d a) a0 = Some true.
Proof.
intros.
elim (domain_equal_mapget bool bool (power (Map bool) (predta_coacc d a) (map_mini state d) n) (predta_coacc_states d a) a0 true).
intros.
elim (bool_is_true_or_false x); intros; rewrite H1 in H0.
exact H0.
elim (predta_coacc_fix_0 d a); intros.
unfold inf_fix_points in H3.
elim (lem_get_leb (power (Map bool) (predta_coacc d a) (map_mini state d) n) (predta_coacc_states d a) a0 true false).
elim (iteres_inf_fps bool (ensemble_base state d) (lemd d) (predta_coacc d a) (map_mini state d) (predta_coacc_states d a) n).
intros.
elim H5.
intros.
exact H7.
unfold mini in |- *.
split.
exact (map_mini_appartient state d).
intros.
split.
exact (map_mini_appartient state d).
split.
exact H4.
elim (map_mini_mini state d).
intros.
exact (H6 x0 H4).
exact H2.
exact (predta_coacc_increasing d a).
exact H.
exact H0.
apply (domain_equal_transitive bool state bool (power (Map bool) (predta_coacc d a) (map_mini state d) n) d (predta_coacc_states d a)).
apply (domain_equal_symmetric state bool d (power (Map bool) (predta_coacc d a) (map_mini state d) n)).
apply (power_def_ok bool (ensemble_base state d) (predta_coacc d a) (map_mini state d) n).
unfold def_ok_app in |- *.
intros.
exact (predta_coacc_def_ok d a x).
exact (map_mini_appartient state d).
unfold predta_coacc_states in |- *.
apply (power_def_ok bool (ensemble_base state d) (predta_coacc d a) (map_mini state d) (S (MapCard state d))).
unfold def_ok_app in |- *.
intros.
exact (predta_coacc_def_ok d a x).
exact (map_mini_appartient state d).
Admitted.

Lemma predta_coacc_contain_coacc_ads_0 : forall (d : preDTA) (a0 a : ad) (s : state) (c : ad) (p : prec_list) (b : ad) (m : Map bool), preDTA_ref_ok d -> MapGet state d a = Some s -> MapGet prec_list s c = Some p -> prec_occur p b -> ensemble_base state d m -> MapGet bool m a = Some true -> MapGet bool (predta_coacc d a0 m) b = Some true.
Proof.
unfold predta_coacc in |- *.
intros.
apply (map_replace_mapget_ins_true_1 (predta_coacc_0 d d m) b a0).
apply (fun hyp : preDTA_ref_ok_distinct d d => predta_coacc_0_contain_coacc_ads d d a s c p b m hyp H0 H1 H2 H3 H4).
elim (preDTA_ref_ok_def d).
intros.
exact (H5 H).
