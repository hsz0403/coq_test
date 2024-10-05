Require Import Bool.
Require Import Arith.
Require Import NArith.
Require Import Ndec.
Require Import ZArith.
Require Import Classical_Prop.
From IntMap Require Import Allmaps.
Require Import lattice_fixpoint.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import pl_path.
Fixpoint pl_non_empty (m : Map bool) (p : prec_list) {struct p} : bool := match p with | prec_empty => true | prec_cons a la ls => match ls with | prec_empty => match MapGet bool m a with | Some b => b && pl_non_empty m la | None => false end | prec_cons _ _ _ => match MapGet bool m a with | Some b => pl_non_empty m ls || b && pl_non_empty m la | None => pl_non_empty m ls end end end.
Fixpoint st_non_empty (m : Map bool) (s : state) {struct s} : bool := match s with | M0 => false | M1 _ p => pl_non_empty m p | M2 a b => st_non_empty m a || st_non_empty m b end.
Fixpoint dta_app_ne_aux (d : preDTA) (m r : Map bool) {struct r} : Map bool := match d, r with | M0, _ => M0 bool | M1 a s, M0 => M0 bool | M1 a s, M1 a' b => if N.eqb a a' then M1 bool a (b || st_non_empty m s) else M0 bool | M1 a s, M2 _ _ => M0 bool | M2 d0 d1, M0 => M0 bool | M2 d0 d1, M1 _ _ => M0 bool | M2 d0 d1, M2 r0 r1 => M2 bool (dta_app_ne_aux d0 m r0) (dta_app_ne_aux d1 m r1) end.
Definition dta_app_ne (d : preDTA) (m : Map bool) : Map bool := dta_app_ne_aux d m m.
Definition dta_non_empty_states (d : preDTA) : Map bool := power (Map bool) (dta_app_ne d) (map_mini state d) (S (MapCard state d)).
Definition dta_states_non_empty (d : DTA) : Map bool := match d with | dta p a => dta_non_empty_states p end.
Definition dta_non_empty_states_lazy (d : preDTA) : Map bool := lazy_power bool eqm_bool (dta_app_ne d) (map_mini state d) (S (MapCard state d)).
Definition dta_states_non_empty_lazy (d : DTA) : Map bool := match d with | dta p a => dta_non_empty_states_lazy p end.
Inductive pl_path_true : pl_path -> Map bool -> Prop := | plp_true_nil : forall m : Map bool, pl_path_true pl_path_nil m | plp_true_cons : forall (m : Map bool) (a : ad) (pl : pl_path), pl_path_true pl m -> MapGet bool m a = Some true -> pl_path_true (pl_path_cons a pl) m.
Definition pl_non_empty_path_true_def_0 (pl : pl_path) (p : prec_list) : Prop := forall m : Map bool, pl_path_incl pl p -> pl_path_true pl m -> pl_non_empty m p = true.
Definition dt_non_empty_def_0 (d : preDTA) (a : ad) (t : term) (pr : reconnaissance d a t) := forall n : nat, term_high t <= n -> MapGet bool (power (Map bool) (dta_app_ne d) (map_mini state d) n) a = Some true.
Definition dt_non_empty_def_1 (d : preDTA) (s : state) (t : term) (pr : state_reconnait d s t) := forall n : nat, term_high t <= S n -> st_non_empty (power (Map bool) (dta_app_ne d) (map_mini state d) n) s = true.
Definition dt_non_empty_def_2 (d : preDTA) (p : prec_list) (t : term_list) (pr : liste_reconnait d p t) := forall n : nat, term_high_0 t <= n -> pl_non_empty (power (Map bool) (dta_app_ne d) (map_mini state d) n) p = true.
Definition dt_non_empty_r_def_0 (n : nat) : Prop := forall (d : preDTA) (a : ad), MapGet bool (power (Map bool) (dta_app_ne d) (map_mini state d) n) a = Some true -> exists t : term, reconnaissance d a t.

Lemma dt_non_empty_r_0 : forall (d : preDTA) (m r : Map bool) (a : ad) (l : state), MapGet state d a = Some l -> domain_equal state bool d r -> MapGet bool (dta_app_ne_aux d m r) a = Some true -> MapGet bool r a = Some true \/ st_non_empty m l = true.
Proof.
simple induction d.
intros.
inversion H.
intros.
induction r as [| a2 a3| r1 Hrecr1 r0 Hrecr0].
inversion H0.
simpl in H0.
rewrite H0 in H.
rewrite H0 in H1.
simpl in H.
elim (bool_is_true_or_false (N.eqb a2 a1)); intro; rewrite H2 in H.
inversion H.
simpl in H1.
rewrite (Neqb_correct a2) in H1.
simpl in H1.
rewrite H2 in H1.
inversion H1.
rewrite H5.
simpl in |- *.
rewrite H2.
elim (bool_is_true_or_false a3); intros; rewrite H3.
left.
reflexivity.
rewrite H3 in H5.
simpl in H5.
rewrite H4 in H5.
right.
exact H5.
inversion H.
inversion H0.
intros.
induction r as [| a0 a1| r1 Hrecr1 r0 Hrecr0].
inversion H2.
inversion H2.
induction a as [| p].
simpl in H1.
simpl in |- *.
simpl in H3.
simpl in H2.
elim H2.
intros.
exact (H _ _ _ _ H1 H4 H3).
elim H2.
intros.
induction p as [p Hrecp| p Hrecp| ]; simpl in |- *; simpl in H1; simpl in H3.
exact (H0 _ _ _ _ H1 H5 H3).
exact (H _ _ _ _ H1 H4 H3).
Admitted.

Lemma dt_non_empty_r_1 : forall (s : state) (m : Map bool), st_non_empty m s = true -> exists c : ad, (exists p : prec_list, MapGet prec_list s c = Some p /\ pl_non_empty m p = true).
Proof.
simple induction s; intros.
simpl in H.
inversion H.
simpl in H.
split with a.
split with a0.
split.
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
exact H.
simpl in H1.
elim (bool_is_true_or_false (st_non_empty m1 m)); intros.
elim (H m1 H2).
intros.
elim H3.
intros.
elim H4.
intros.
induction x as [| p].
split with N0.
split with x0.
simpl in |- *.
split; assumption.
split with (Npos (xO p)).
split with x0.
simpl in |- *.
split; assumption.
rewrite H2 in H1.
simpl in H1.
elim (H0 _ H1).
intros.
elim H3.
intros.
elim H4.
intros.
induction x as [| p].
split with (Npos 1).
simpl in |- *.
split with x0.
split; assumption.
split with (Npos (xI p)).
split with x0.
simpl in |- *.
Admitted.

Lemma dt_non_empty_r_2 : forall (p : prec_list) (m : Map bool), pl_non_empty m p = true -> exists pl : pl_path, pl_path_true pl m /\ pl_path_incl pl p.
Proof.
simple induction p.
intros.
simpl in H1.
elim (pl_sum p1).
intros.
rewrite H2 in H1.
elim (option_sum bool (MapGet bool m a)).
intro y.
elim y.
intros x y0.
rewrite y0 in H1.
elim (bool_is_true_or_false x); intros; rewrite H3 in H1; simpl in H1.
elim (H m H1).
intros.
elim H4.
intros.
rewrite H3 in y0.
split with (pl_path_cons a x0).
split.
exact (plp_true_cons m a x0 H5 y0).
exact (pl_path_incl_cons x0 a p0 p1 H6).
inversion H1.
intro y.
rewrite y in H1.
inversion H1.
intros.
elim H2.
intros.
elim H3.
intros.
elim H4.
intros.
rewrite H5 in H1.
elim (option_sum bool (MapGet bool m a)); intro y.
elim y.
intros x2 y0.
rewrite y0 in H1.
rewrite <- H5 in H1.
elim (bool_is_true_or_false (pl_non_empty m p1)); intros.
elim (H0 _ H6).
intros.
elim H7.
intros.
split with x3.
split.
exact H8.
apply (pl_path_incl_next x3 a p0 p1 H9).
intro.
rewrite H10 in H9.
inversion H9.
rewrite <- H12 in H5.
inversion H5.
elim (H12 (refl_equal _)).
rewrite H6 in H1.
simpl in H1.
elim (bool_is_true_or_false x2); intro.
rewrite H7 in y0.
elim (bool_is_true_or_false (pl_non_empty m p0)); intro.
elim (H _ H8).
intros.
elim H9.
intros.
split with (pl_path_cons a x3).
split.
exact (plp_true_cons _ _ _ H10 y0).
exact (pl_path_incl_cons x3 a p0 p1 H11).
rewrite H8 in H1.
rewrite H7 in H1.
inversion H1.
rewrite H7 in H1.
inversion H1.
rewrite y in H1.
rewrite <- H5 in H1.
elim (H0 _ H1).
intros.
elim H6.
intros.
split with x2.
split.
exact H7.
apply (pl_path_incl_next x2 a p0 p1 H8).
intro.
rewrite H9 in H8.
inversion H8.
rewrite <- H11 in H5.
inversion H5.
elim H11.
reflexivity.
intros.
split with pl_path_nil.
split.
exact (plp_true_nil m).
Admitted.

Lemma dt_non_empty_r_3 : dt_non_empty_r_def_0 0.
Proof.
unfold dt_non_empty_r_def_0 in |- *.
simpl in |- *.
intros.
cut (true <> false).
intro.
elim (H0 (map_mini_mapget_false state d a true H)).
intro.
Admitted.

Lemma dt_non_empty_r_4 : forall (p : prec_list) (n : nat) (d : preDTA) (pl : pl_path), dt_non_empty_r_def_0 n -> pl_path_true pl (power (Map bool) (dta_app_ne d) (map_mini state d) n) -> pl_path_incl pl p -> exists tl : term_list, liste_reconnait d p tl.
Proof.
unfold dt_non_empty_r_def_0 in |- *.
simple induction p.
intros.
inversion H2.
inversion H3.
rewrite <- H4 in H7.
inversion H7.
elim H11; auto.
elim (H1 _ _ H5).
intros.
inversion H3.
rewrite <- H10 in H6.
inversion H6.
rewrite <- H10 in H2.
inversion H2.
elim (H n d plp H1 H18 H11).
intros.
split with (tcons x x0).
rewrite H15 in H8.
rewrite H9 in H8.
exact (rec_consi d a p0 p1 x x0 H8 H21).
elim (H0 n d pl H1 H2 H12).
intros.
induction x0 as [| t x0 Hrecx0].
inversion H15.
rewrite <- H17 in H12.
inversion H12.
elim H14; auto.
split with (tcons t x0).
exact (rec_consn d a p0 p1 t x0 H15).
intros.
inversion H1.
split with tnil.
Admitted.

Lemma dt_non_empty_r_5 : forall n : nat, dt_non_empty_r_def_0 n -> dt_non_empty_r_def_0 (S n).
Proof.
unfold dt_non_empty_r_def_0 in |- *.
intros.
elim (domain_equal_mapget bool state (power (Map bool) (dta_app_ne d) (map_mini state d) (S n)) d a true).
intros.
unfold dta_app_ne in H0.
simpl in H0.
elim (dt_non_empty_r_0 d (power (Map bool) (fun m : Map bool => dta_app_ne_aux d m m) (map_mini state d) n) (power (Map bool) (fun m : Map bool => dta_app_ne_aux d m m) (map_mini state d) n) a x H1); intros.
exact (H d a H2).
elim (dt_non_empty_r_1 _ _ H2).
intros.
elim H3.
intros.
elim H4.
intros.
elim (dt_non_empty_r_2 _ _ H6).
intros.
elim H7.
intros.
elim (dt_non_empty_r_4 x1 n d x2 H H8 H9).
intros.
split with (app x0 x3).
exact (rec_dta d a (app x0 x3) x H1 (rec_st d x x0 x3 x1 H5 H10)).
apply (power_def_ok bool (ensemble_base state d) (dta_app_ne d) (map_mini state d) n).
exact (dta_app_ne_def_ok d).
exact (map_mini_appartient state d).
exact H0.
apply (domain_equal_symmetric state bool d (power (Map bool) (dta_app_ne d) (map_mini state d) (S n))).
exact (power_def_ok bool (ensemble_base state d) (dta_app_ne d) (map_mini state d) (S n) (dta_app_ne_def_ok d) (map_mini_appartient state d)).
Admitted.

Lemma dt_non_empty_r : forall (n : nat) (d : preDTA) (a : ad), MapGet bool (power (Map bool) (dta_app_ne d) (map_mini state d) n) a = Some true -> exists t : term, reconnaissance d a t.
Proof.
Admitted.

Lemma dt_non_empty_fix_0 : forall d : preDTA, lower_fix_point bool (ensemble_base state d) lem (dta_app_ne d) (dta_non_empty_states d).
Proof.
unfold dta_non_empty_states in |- *.
intros.
Admitted.

Lemma dt_non_empty_fix_1 : forall (d : preDTA) (a : ad) (n : nat), MapGet bool (power (Map bool) (dta_app_ne d) (map_mini state d) n) a = Some true -> MapGet bool (dta_non_empty_states d) a = Some true.
Proof.
intros.
elim (domain_equal_mapget bool bool (power (Map bool) (dta_app_ne d) (map_mini state d) n) (dta_non_empty_states d) a true).
intros.
elim (bool_is_true_or_false x); intro; rewrite H1 in H0.
exact H0.
elim (dt_non_empty_fix_0 d).
intros.
unfold inf_fix_points in H3.
elim (lem_get_leb _ _ _ _ _ (iteres_inf_fps bool (ensemble_base state d) lem (dta_app_ne d) (map_mini state d) (dta_non_empty_states d) n (map_mini_mini state d) H2 (dta_app_ne_inc d)) H H0).
apply (domain_equal_transitive bool state bool (power (Map bool) (dta_app_ne d) (map_mini state d) n) d (dta_non_empty_states d)).
exact (domain_equal_symmetric state bool _ _ (power_def_ok bool (ensemble_base state d) (dta_app_ne d) (map_mini state d) n (dta_app_ne_def_ok d) (map_mini_appartient state d))).
unfold dta_non_empty_states in |- *.
exact (power_def_ok bool (ensemble_base state d) (dta_app_ne d) (map_mini state d) (S (MapCard state d)) (dta_app_ne_def_ok d) (map_mini_appartient state d)).
Admitted.

Lemma dt_non_empty_fix_2 : forall (d : preDTA) (a : ad), MapGet bool (dta_non_empty_states d) a = Some true -> exists n : nat, MapGet bool (power (Map bool) (dta_app_ne d) (map_mini state d) n) a = Some true.
Proof.
unfold dta_non_empty_states in |- *.
intros.
split with (S (MapCard state d)).
Admitted.

Lemma dt_non_empty_lazy_fix : forall (d : preDTA) (a : ad), MapGet bool (dta_non_empty_states_lazy d) a = Some true <-> (exists t : term, reconnaissance d a t).
Proof.
intro.
unfold dta_non_empty_states_lazy in |- *.
rewrite (lazy_power_eg_power bool eqm_bool (dta_app_ne d) (map_mini state d) (S (MapCard state d))).
exact (dt_non_empty_fix d).
split.
exact (eqm_bool_equal a b).
intro.
rewrite H.
Admitted.

Lemma dt_non_empty_fix : forall (d : preDTA) (a : ad), MapGet bool (dta_non_empty_states d) a = Some true <-> (exists t : term, reconnaissance d a t).
Proof.
intros.
split.
intros.
elim (dt_non_empty_fix_2 d a H).
intros.
exact (dt_non_empty_r _ _ _ H0).
intros.
elim H.
intros.
elim (dt_non_empty_d d a x H0).
intros.
exact (dt_non_empty_fix_1 _ _ _ H1).
