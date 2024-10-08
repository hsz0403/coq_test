Require Import Bool.
Require Import ZArith.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import signature.
Require Import pl_path.
Require Import refcorrect.
Require Import states_kill_empty.
Require Import lattice_fixpoint.
Require Import empty_test.

Lemma prec_list_kill_correct_wrt_sign_invar : forall (m : Map bool) (p p' : prec_list) (n : nat), pl_tl_length p n -> prec_list_kill m p = Some p' -> pl_tl_length p' n.
Proof.
intros.
apply (forall_incl_length p' n).
intros.
elim (pl_kill_1 p p' m p0 H0 H1).
intros.
Admitted.

Lemma states_kill_aux_correct_wrt_sign_invar : forall (s : state) (m : Map bool) (sigma : signature), state_correct_wrt_sign s sigma -> state_correct_wrt_sign (states_kill_aux m s) sigma.
Proof.
unfold state_correct_wrt_sign in |- *.
intros.
elim (st_kill_2 _ _ _ _ H0).
intros.
elim H1.
intros.
elim (H _ _ H2).
intros.
split with x0.
elim H4.
intros.
split.
exact H5.
Admitted.

Lemma states_kill_correct_wrt_sign_invar : forall (s s' : state) (m : Map bool) (sigma : signature), state_correct_wrt_sign s sigma -> states_kill m s = Some s' -> state_correct_wrt_sign s' sigma.
Proof.
unfold states_kill in |- *.
intros.
elim (map_sum prec_list (states_kill_aux m s)); intros.
rewrite H1 in H0.
inversion H0.
elim H1; intros; elim H2; intros; elim H3; intros; rewrite H4 in H0.
inversion H0.
rewrite <- H4.
exact (states_kill_aux_correct_wrt_sign_invar _ _ _ H).
inversion H0.
rewrite <- H4.
Admitted.

Lemma preDTA_kill_correct_wrt_sign_invar : forall (d : preDTA) (m : Map bool) (sigma : signature), predta_correct_wrt_sign d sigma -> predta_correct_wrt_sign (preDTA_kill m d) sigma.
Proof.
unfold predta_correct_wrt_sign in |- *.
intros.
elim (dt_kill_1 _ _ _ _ H0).
intros.
elim H1.
intros.
Admitted.

Lemma DTA_kill_correct_wrt_sign_invar : forall (d : DTA) (m : Map bool) (sigma : signature), dta_correct_wrt_sign d sigma -> dta_correct_wrt_sign (DTA_kill m d) sigma.
Proof.
simple induction d.
simpl in |- *.
intros.
elim (option_sum state (MapGet state (preDTA_kill m p) a)).
intros y.
elim y.
intros x y0.
rewrite y0.
exact (preDTA_kill_correct_wrt_sign_invar _ _ _ H).
intros y.
rewrite y.
unfold dta_correct_wrt_sign in |- *.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H0.
elim (N.discr a0); intros y0.
elim y0.
intros x y1.
rewrite y1 in H0.
inversion H0.
rewrite y0 in H0.
inversion H0.
unfold state_correct_wrt_sign in |- *.
intros.
Admitted.

Lemma DTA_kill_empty_states_lazy_correct_wrt_sign_invar : forall (d : DTA) (sigma : signature), dta_correct_wrt_sign d sigma -> dta_correct_wrt_sign (DTA_kill_empty_states_lazy d) sigma.
Proof.
intro.
rewrite (kill_empty_states_lazy_eg_kill_empty_states d).
unfold DTA_kill_empty_states in |- *.
Admitted.

Lemma kill_empty_lazy_correct_wrt_sign_invar : forall (d : DTA) (sigma : signature), dta_correct_wrt_sign d sigma -> dta_correct_wrt_sign (DTA_kill_empty_states_lazy d) sigma.
Proof.
intro.
rewrite (kill_empty_states_lazy_eg_kill_empty_states d).
Admitted.

Lemma prec_list_kill_occur : forall (p p' : prec_list) (b : ad) (m : Map bool), prec_list_kill m p = Some p' -> prec_occur p' b -> MapGet bool m b = Some true.
Proof.
simple induction p.
intros.
simpl in H1.
elim (pl_sum p1); intros.
rewrite H3 in H1.
elim (option_sum bool (MapGet bool m a)); intros y.
elim y.
intros x y0.
rewrite y0 in H1.
elim (bool_is_true_or_false x); intros; rewrite H4 in H1.
elim (option_sum prec_list (prec_list_kill m p0)); intros y1.
elim y1.
intros x0 y2.
rewrite y2 in H1.
inversion H1.
rewrite <- H6 in H2.
inversion H2.
rewrite <- H5.
rewrite H4 in y0.
exact y0.
exact (H _ _ _ y2 H10).
inversion H10.
rewrite y1 in H1.
inversion H1.
inversion H1.
rewrite y in H1.
inversion H1.
elim H3.
intros.
elim H4.
intros.
elim H5.
intros.
rewrite H6 in H1.
elim (option_sum bool (MapGet bool m a)); intros y.
elim y.
intros x2 y0.
rewrite y0 in H1.
elim (bool_is_true_or_false x2); intros; rewrite H7 in H1.
elim (option_sum prec_list (prec_list_kill m p0)); intros y1.
elim y1.
intros x3 y2.
rewrite y2 in H1.
elim (option_sum prec_list (prec_list_kill m (prec_cons x x0 x1))); intros y3.
elim y3.
intros x4 y4.
rewrite y4 in H1.
inversion H1.
rewrite <- H9 in H2.
inversion H2.
rewrite <- H8.
rewrite H7 in y0.
exact y0.
exact (H _ _ _ y2 H13).
rewrite <- H6 in y4.
exact (H0 _ _ _ y4 H13).
rewrite y3 in H1.
inversion H1.
rewrite <- H9 in H2.
inversion H2.
rewrite <- H8.
rewrite H7 in y0.
exact y0.
exact (H _ _ _ y2 H13).
inversion H13.
rewrite y1 in H1.
elim (option_sum prec_list (prec_list_kill m (prec_cons x x0 x1))); intros y2.
elim y2.
intros x3 y3.
rewrite y3 in H1.
inversion H1.
rewrite <- H9 in H2.
rewrite <- H6 in y3.
exact (H0 _ _ _ y3 H2).
rewrite y2 in H1.
inversion H1.
rewrite <- H6 in H1.
exact (H0 _ _ _ H1 H2).
rewrite y in H1.
rewrite <- H6 in H1.
exact (H0 _ _ _ H1 H2).
intros.
simpl in H.
inversion H.
rewrite <- H2 in H0.
Admitted.

Lemma prec_list_kill_ref_ok_invar : forall (d : preDTA) (p p' : prec_list) (sigma : signature), prec_list_ref_ok p d -> predta_correct_wrt_sign d sigma -> prec_list_kill (dta_non_empty_states d) p = Some p' -> prec_list_ref_ok p' (preDTA_kill (dta_non_empty_states d) d).
Proof.
intros.
unfold prec_list_ref_ok in |- *.
intros.
elim (dt_non_empty_fix d a).
intros.
elim (H3 (prec_list_kill_occur _ _ _ _ H1 H2)).
intros.
elim (dt_kill_empty_kill_empty d a sigma H0).
intros.
apply H7.
split with x.
Admitted.

Lemma states_kill_aux_ref_ok_invar : forall (d : preDTA) (s : state) (sigma : signature), state_ref_ok s d -> predta_correct_wrt_sign d sigma -> state_ref_ok (states_kill_aux (dta_non_empty_states d) s) (preDTA_kill (dta_non_empty_states d) d).
Proof.
unfold state_ref_ok in |- *.
intros.
elim (st_kill_2 _ _ _ _ H1).
intros.
elim H2.
intros.
Admitted.

Lemma states_kill_ref_ok_invar : forall (d : preDTA) (s s' : state) (sigma : signature), state_ref_ok s d -> predta_correct_wrt_sign d sigma -> states_kill (dta_non_empty_states d) s = Some s' -> state_ref_ok s' (preDTA_kill (dta_non_empty_states d) d).
Proof.
intros.
unfold states_kill in H1.
elim (map_sum prec_list (states_kill_aux (dta_non_empty_states d) s)); intros.
rewrite H2 in H1.
inversion H1.
elim H2; intros; elim H3; intros; elim H4; intros; rewrite H5 in H1.
inversion H1.
rewrite <- H5.
exact (states_kill_aux_ref_ok_invar _ _ _ H H0).
inversion H1.
rewrite <- H5.
Admitted.

Lemma preDTA_kill_ref_ok_distinct_invar : forall (d : preDTA) (sigma : signature), preDTA_ref_ok_distinct d d -> predta_correct_wrt_sign d sigma -> preDTA_ref_ok_distinct (preDTA_kill (dta_non_empty_states d) d) (preDTA_kill (dta_non_empty_states d) d).
Proof.
unfold preDTA_ref_ok_distinct in |- *.
intros.
elim (dt_kill_1 _ _ _ _ H1).
intros.
elim H2.
intros.
Admitted.

Lemma preDTA_kill_ref_ok_invar : forall (d : preDTA) (sigma : signature), preDTA_ref_ok d -> predta_correct_wrt_sign d sigma -> preDTA_ref_ok (preDTA_kill (dta_non_empty_states d) d).
Proof.
intros.
elim (preDTA_ref_ok_def (preDTA_kill (dta_non_empty_states d) d)).
intros.
apply H2.
elim (preDTA_ref_ok_def d).
intro.
intro.
Admitted.

Lemma DTA_kill_ref_ok_invar : forall (d : DTA) (sigma : signature), DTA_ref_ok d -> dta_correct_wrt_sign d sigma -> DTA_ref_ok (DTA_kill (dta_states_non_empty d) d).
Proof.
simple induction d.
simpl in |- *.
intros.
elim (option_sum state (MapGet state (preDTA_kill (dta_non_empty_states p) p) a)); intros y.
elim y.
intros x y0.
rewrite y0.
exact (preDTA_kill_ref_ok_invar _ _ H H0).
rewrite y.
simpl in |- *.
unfold preDTA_ref_ok in |- *.
intros.
simpl in H1.
elim (N.discr a0); intros y0.
elim y0.
intros x y1.
rewrite y1 in H1.
inversion H1.
rewrite y0 in H1.
inversion H1.
rewrite <- H5 in H2.
Admitted.

Lemma DTA_kill_ref_ok_invar_lazy : forall (d : DTA) (sigma : signature), DTA_ref_ok d -> dta_correct_wrt_sign d sigma -> DTA_ref_ok (DTA_kill_empty_states_lazy d).
Proof.
intro.
rewrite (kill_empty_states_lazy_eg_kill_empty_states d).
Admitted.

Lemma inter_DTA_main_state_correct_invar : forall d : DTA, DTA_main_state_correct d -> DTA_main_state_correct (DTA_kill (dta_states_non_empty d) d).
Proof.
simple induction d.
simpl in |- *.
intros.
elim (option_sum state (MapGet state (preDTA_kill (dta_non_empty_states p) p) a)); intros y.
elim y.
intros x y0.
rewrite y0.
simpl in |- *.
unfold addr_in_preDTA in |- *.
unfold addr_in_preDTA in H.
split with x.
exact y0.
rewrite y.
simpl in |- *.
unfold addr_in_preDTA in |- *.
intros.
split with (M0 prec_list).
Admitted.

Lemma inter_DTA_main_state_correct_invar_lazy : forall d : DTA, DTA_main_state_correct d -> DTA_main_state_correct (DTA_kill_empty_states_lazy d).
Proof.
intro.
rewrite (kill_empty_states_lazy_eg_kill_empty_states d).
Admitted.

Lemma kill_empty_correct_wrt_sign_invar : forall (d : DTA) (sigma : signature), dta_correct_wrt_sign d sigma -> dta_correct_wrt_sign (DTA_kill_empty_states d) sigma.
Proof.
simple induction d.
simpl in |- *.
intros.
elim (option_sum state (MapGet state (preDTA_kill (dta_non_empty_states p) p) a)); intros y.
elim y.
intros x y0.
rewrite y0.
simpl in |- *.
exact (kill_empty_correct_wrt_sign_invar p sigma (dta_non_empty_states p) H).
rewrite y.
simpl in |- *.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H0.
elim (N.discr a0).
intros y0.
elim y0.
intros x y1.
rewrite y1 in H0.
inversion H0.
intros y0.
rewrite y0 in H0.
inversion H0.
unfold state_correct_wrt_sign in |- *.
intros.
inversion H1.
