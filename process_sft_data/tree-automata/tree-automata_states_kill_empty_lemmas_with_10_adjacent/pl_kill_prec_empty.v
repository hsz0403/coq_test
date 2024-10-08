Require Import ZArith.
Require Import NArith Ndec.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import lattice_fixpoint.
Require Import signature.
Require Import pl_path.
Require Import empty_test.
Fixpoint prec_list_kill (m : Map bool) (p : prec_list) {struct p} : option prec_list := match p with | prec_empty => Some prec_empty | prec_cons a la ls => match ls with | prec_empty => match MapGet bool m a with | None => None | Some b => if b then match prec_list_kill m la with | None => None | Some la' => Some (prec_cons a la' prec_empty) end else None end | prec_cons _ _ _ => match MapGet bool m a with | None => prec_list_kill m ls | Some b => if b then match prec_list_kill m la, prec_list_kill m ls with | None, None => None | None, Some ls' => Some ls' | Some la', None => Some (prec_cons a la' prec_empty) | Some la', Some ls' => Some (prec_cons a la' ls') end else prec_list_kill m ls end end end.
Fixpoint states_kill_aux (m : Map bool) (s : state) {struct s} : state := match s with | M0 => M0 prec_list | M1 a p => match prec_list_kill m p with | None => M0 prec_list | Some p' => M1 prec_list a p' end | M2 s0 s1 => match states_kill_aux m s0, states_kill_aux m s1 with | M0, M0 => M0 prec_list | M0, M1 a p => M1 prec_list (Ndouble_plus_one a) p | M1 a p, M0 => M1 prec_list (N.double a) p | s0', s1' => M2 prec_list s0' s1' end end.
Definition states_kill (m : Map bool) (s : state) : option state := match states_kill_aux m s with | M0 => None | x => Some x end.
Fixpoint preDTA_kill (m : Map bool) (d : preDTA) {struct d} : preDTA := match d with | M0 => M0 state | M1 a s => match states_kill m s with | None => M0 state | Some s' => M1 state a s' end | M2 d0 d1 => match preDTA_kill m d0, preDTA_kill m d1 with | M0, M0 => M0 state | M0, M1 a s' => M1 state (Ndouble_plus_one a) s' | M1 a s', M0 => M1 state (N.double a) s' | d0', d1' => M2 state d0' d1' end end.
Definition DTA_simpl (d : DTA) : DTA := match d with | dta p a => match MapGet state p a with | None => dta (M1 state N0 (M0 prec_list)) N0 | _ => dta p a end end.
Definition DTA_kill (m : Map bool) (d : DTA) : DTA := match d with | dta p a => DTA_simpl (dta (preDTA_kill m p) a) end.
Definition DTA_kill_empty_states (d : DTA) : DTA := DTA_kill (dta_states_non_empty d) d.
Definition DTA_kill_empty_states_lazy (d : DTA) : DTA := DTA_kill (dta_states_non_empty_lazy d) d.
Definition dt_kill_empty_def_0 (n : nat) : Prop := forall (d : preDTA) (a : ad) (t : term), term_high t <= n -> reconnaissance d a t -> reconnaissance (preDTA_kill (dta_non_empty_states d) d) a t.
Definition dt_kill_empty_def_1 (n : nat) : Prop := forall (d : preDTA) (a : ad) (t : term), term_high t <= n -> reconnaissance (preDTA_kill (dta_non_empty_states d) d) a t -> reconnaissance d a t.

Lemma pl_path_recon_true : forall (d : preDTA) (plp : pl_path) (tl : term_list), pl_path_recon d tl plp -> pl_path_true plp (dta_non_empty_states d).
Proof.
intro.
simple induction plp.
intros.
exact (plp_true_nil _).
intros.
inversion H0.
elim (dt_non_empty_fix d a).
intros.
apply (plp_true_cons (dta_non_empty_states d) a p (H tl0 H6)).
apply H8.
split with t.
Admitted.

Lemma kill_empty_states_lazy_eg_kill_empty_states : forall d : DTA, DTA_kill_empty_states_lazy d = DTA_kill_empty_states d.
Proof.
unfold DTA_kill_empty_states_lazy, DTA_kill_empty_states in |- *.
intros.
rewrite (dta_states_non_empty_lazy_eg_dta_states_non_empty d).
Admitted.

Lemma pl_kill_0 : forall (p : prec_list) (m : Map bool) (plp : pl_path), pl_path_incl plp p -> pl_path_true plp m -> exists pl : prec_list, prec_list_kill m p = Some pl /\ pl_path_incl plp pl.
Proof.
simple induction p.
intros.
elim (pl_sum p1).
intro.
rewrite H3.
simpl in |- *.
inversion H2.
rewrite <- H4 in H1.
inversion H1.
elim H11.
reflexivity.
rewrite <- H6 in H1.
inversion H1.
rewrite H11 in H5.
rewrite H5.
elim (H m pl H9 H4).
intros.
elim H14.
intros.
rewrite H15.
split with (prec_cons a x prec_empty).
split.
reflexivity.
exact (pl_path_incl_cons pl a x prec_empty H16).
rewrite H3 in H11.
inversion H11.
intros.
elim H3.
intros.
elim H4.
intros.
elim H5.
intros.
simpl in |- *.
rewrite H6.
rewrite <- H6.
inversion H2.
rewrite <- H7 in H1.
inversion H1.
elim (H14 (refl_equal _)).
rewrite <- H9 in H1.
inversion H1.
rewrite H14 in H8.
rewrite H8.
elim (H _ _ H12 H7).
intros.
elim H17.
intros.
rewrite H18.
elim (option_sum prec_list (prec_list_kill m p1)).
intro y.
elim y.
intros x3 y0.
rewrite y0.
split with (prec_cons a x2 x3).
split.
reflexivity.
exact (pl_path_incl_cons pl a x2 x3 H19).
intro y.
rewrite y.
split with (prec_cons a x2 prec_empty).
split.
reflexivity.
exact (pl_path_incl_cons pl a x2 prec_empty H19).
rewrite <- H9 in H2.
elim (H0 _ _ H14 H2).
intros.
elim H17.
intros.
rewrite H18.
elim (option_sum bool (MapGet bool m a)); intro y.
elim y.
intros x3 y0.
rewrite y0.
elim (bool_is_true_or_false x3); intro; rewrite H20.
elim (option_sum prec_list (prec_list_kill m p0)); intros y1.
elim y1.
intros x4 y2.
rewrite y2.
split with (prec_cons a x4 x2).
split.
reflexivity.
apply (pl_path_incl_next (pl_path_cons a0 pl) a x4 x2 H19).
intro.
inversion H21.
rewrite y1.
split with x2.
split.
reflexivity.
assumption.
split with x2.
split.
reflexivity.
assumption.
rewrite y.
split with x2.
split.
reflexivity.
assumption.
intros.
simpl in |- *.
split with prec_empty.
split.
reflexivity.
inversion H.
Admitted.

Lemma pl_kill_1 : forall (p p' : prec_list) (m : Map bool) (pl : pl_path), prec_list_kill m p = Some p' -> pl_path_incl pl p' -> pl_path_incl pl p /\ pl_path_true pl m.
Proof.
simple induction p.
intros.
elim (pl_sum p1); intros.
rewrite H3.
rewrite H3 in H1.
simpl in H1.
elim (option_sum bool (MapGet bool m a)); intro y.
elim y.
intros x y0.
rewrite y0 in H1.
elim (bool_is_true_or_false x); intro; rewrite H4 in H1.
elim (option_sum prec_list (prec_list_kill m p0)); intro y1.
elim y1.
intros x0 y2.
rewrite y2 in H1.
inversion H1.
rewrite <- H6 in H2.
inversion H2.
elim (H _ _ _ y2 H8).
intros.
split.
apply (pl_path_incl_cons plp a p0 prec_empty).
exact H11.
rewrite H4 in y0.
exact (plp_true_cons m a plp H12 y0).
inversion H9.
elim H11.
symmetry in |- *.
exact H12.
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
simpl in H1.
rewrite H6 in H1.
elim (option_sum bool (MapGet bool m a)); intro y.
elim y.
intros x2 y0.
rewrite y0 in H1.
rewrite <- H6 in H1.
elim (bool_is_true_or_false x2); intros; rewrite H7 in H1.
elim (option_sum prec_list (prec_list_kill m p0)); intro y1; elim (option_sum prec_list (prec_list_kill m p1)); intro y2.
elim y1.
intros x3 y3.
elim y2.
intros x4 y4.
rewrite y3 in H1.
rewrite y4 in H1.
inversion H1.
rewrite <- H9 in H2.
inversion H2.
elim (H x3 m plp y3 H11).
intros.
split.
exact (pl_path_incl_cons plp a p0 p1 H14).
rewrite H7 in y0.
exact (plp_true_cons _ _ _ H15 y0).
elim (H0 x4 m pl y4 H12).
intros.
split.
apply (pl_path_incl_next pl a p0 p1 H15).
assumption.
exact H16.
elim y1.
intros x3 y3.
rewrite y2 in H1.
rewrite y3 in H1.
inversion H1.
rewrite <- H9 in H2.
inversion H2.
elim (H x3 m plp y3 H11).
intros.
split.
exact (pl_path_incl_cons plp a p0 p1 H14).
rewrite H7 in y0.
exact (plp_true_cons _ _ _ H15 y0).
inversion H12.
elim (H14 (sym_eq H15)).
elim y2.
intros x3 y3.
rewrite y1 in H1.
rewrite y3 in H1.
inversion H1.
rewrite <- H9 in H2.
elim (H0 x3 m pl y3 H2).
intros.
split.
apply (pl_path_incl_next pl a p0 p1 H8).
intro.
rewrite H11 in H8.
inversion H8.
rewrite H6 in H13.
inversion H13.
elim (H13 (refl_equal _)).
exact H10.
rewrite y1 in H1.
rewrite y2 in H1.
inversion H1.
elim (H0 _ _ _ H1 H2).
intros.
split.
apply (pl_path_incl_next pl a p0 p1 H8).
intro.
rewrite H10 in H8.
inversion H8.
rewrite H6 in H12.
inversion H12.
elim (H12 (refl_equal _)).
exact H9.
rewrite y in H1.
rewrite <- H6 in H1.
elim (H0 _ _ _ H1 H2).
intros.
split.
apply (pl_path_incl_next pl a p0 p1).
exact H7.
intro.
rewrite H9 in H7.
inversion H7.
rewrite H6 in H11.
inversion H11.
elim H11.
reflexivity.
exact H8.
intros.
simpl in H.
inversion H.
rewrite <- H2 in H0.
inversion H0.
split.
exact pl_path_incl_nil.
Admitted.

Lemma st_kill_0 : forall (s : state) (m : Map bool) (a : ad) (p p' : prec_list), prec_list_kill m p = Some p' -> MapGet prec_list s a = Some p -> MapGet prec_list (states_kill_aux m s) a = Some p'.
Proof.
simple induction s.
intros.
inversion H0.
intros.
simpl in H0.
elim (bool_is_true_or_false (N.eqb a a1)); intros; rewrite H1 in H0.
inversion H0.
simpl in |- *.
rewrite H.
simpl in |- *.
rewrite H1.
reflexivity.
inversion H0.
intros.
simpl in |- *.
simpl in H2.
simpl in |- *.
elim (map_sum prec_list (states_kill_aux m1 m)).
intro.
rewrite H3.
elim (map_sum prec_list (states_kill_aux m1 m0)).
intro.
rewrite H4.
induction a as [| p0].
rewrite <- (H _ _ _ _ H1 H2).
rewrite H3.
reflexivity.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H4.
reflexivity.
rewrite <- (H _ _ _ _ H1 H2).
rewrite H3.
reflexivity.
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H4.
reflexivity.
intro.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
rewrite H7.
induction a as [| p0].
cut (MapGet prec_list (states_kill_aux m1 m) N0 = Some p').
intro.
rewrite H3 in H8.
inversion H8.
exact (H _ _ _ _ H1 H2).
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H7.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb x (Npos p0))).
intro.
rewrite H8.
rewrite (Neqb_complete _ _ H8).
simpl in |- *.
rewrite (aux_Neqb_1_0 p0).
reflexivity.
intro.
rewrite H8.
elim (bool_is_true_or_false (N.eqb (Ndouble_plus_one x) (Npos (xI p0)))).
intro.
rewrite (Ndouble_plus_one_inv_xI _ _ (Neqb_complete _ _ H9)) in H8.
rewrite (Neqb_correct (Npos p0)) in H8.
inversion H8.
intro.
rewrite H9.
reflexivity.
rewrite <- (H _ _ _ _ H1 H2).
rewrite H3.
induction x as [| p1].
simpl in |- *.
reflexivity.
simpl in |- *.
reflexivity.
rewrite <- (H0 _ _ _ _ H1 H2).
simpl in |- *.
rewrite H7.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb (Ndouble_plus_one x) (Npos 1))); intro; rewrite H8.
elim (bool_is_true_or_false (N.eqb x N0)); intro; rewrite H9.
reflexivity.
rewrite (Ndouble_plus_one_inv_xH _ (Neqb_complete _ _ H8)) in H9.
rewrite (Neqb_correct N0) in H9.
inversion H9.
elim (bool_is_true_or_false (N.eqb x N0)); intro; rewrite H9.
rewrite (Neqb_complete _ _ H9) in H8.
inversion H8.
reflexivity.
intros.
elim H5.
intros.
elim H6.
intros.
rewrite H7.
induction a as [| p0].
rewrite <- (H _ _ _ _ H1 H2).
rewrite H3.
simpl in |- *.
reflexivity.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
rewrite <- H7.
simpl in |- *.
exact (H0 _ _ _ _ H1 H2).
rewrite <- (H _ _ _ _ H1 H2).
rewrite H3.
reflexivity.
rewrite <- (H0 _ _ _ _ H1 H2).
simpl in |- *.
rewrite H7.
simpl in |- *.
reflexivity.
intros.
elim H3.
intros.
elim H4.
intros.
elim H5.
intros.
rewrite H6.
elim (map_sum prec_list (states_kill_aux m1 m0)); intro.
rewrite H7.
induction a as [| p0].
rewrite <- (H _ _ _ _ H1 H2).
rewrite H6.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb (N.double x) N0)); intro; rewrite H8.
elim (bool_is_true_or_false (N.eqb x N0)); intro; rewrite H9.
reflexivity.
rewrite (Ndouble_inv_N0 _ (Neqb_complete _ _ H8)) in H9.
inversion H9.
elim (bool_is_true_or_false (N.eqb x N0)); intro; rewrite H9.
rewrite (Neqb_complete _ _ H9) in H8.
inversion H8.
reflexivity.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H7.
induction x as [| p1]; simpl in |- *.
reflexivity.
reflexivity.
rewrite <- (H _ _ _ _ H1 H2).
rewrite H6.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb (N.double x) (Npos (xO p0)))); intro; rewrite H8.
elim (bool_is_true_or_false (N.eqb x (Npos p0))); intro; rewrite H9.
reflexivity.
rewrite (Ndouble_inv_xO _ _ (Neqb_complete _ _ H8)) in H9.
rewrite (Neqb_correct (Npos p0)) in H9.
inversion H9.
elim (bool_is_true_or_false (N.eqb x (Npos p0))); intro; rewrite H9.
rewrite (Neqb_complete _ _ H9) in H8.
simpl in H8.
rewrite (aux_Neqb_1_0 p0) in H8.
inversion H8.
reflexivity.
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H7.
simpl in |- *.
induction x as [| p0]; reflexivity.
elim H7.
intros.
elim H8.
intros.
elim H9.
intros.
rewrite H10.
induction a as [| p0].
unfold MapGet in |- *.
rewrite <- (H _ _ _ _ H1 H2).
simpl in |- *.
rewrite H6.
reflexivity.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in |- *.
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H10.
reflexivity.
rewrite <- (H _ _ _ _ H1 H2).
rewrite H6.
simpl in |- *.
reflexivity.
rewrite <- (H0 _ _ _ _ H1 H2).
simpl in |- *.
rewrite H10.
reflexivity.
intros.
elim H8.
intros.
elim H9.
intros.
rewrite H10.
induction a as [| p0].
rewrite <- (H _ _ _ _ H1 H2).
rewrite H6.
reflexivity.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H10.
reflexivity.
rewrite <- (H _ _ _ _ H1 H2).
rewrite H6.
reflexivity.
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H10.
reflexivity.
intros.
elim H4.
intros.
elim H5.
intros.
rewrite H6.
rewrite <- H6.
induction a as [| p0].
simpl in |- *.
exact (H _ _ _ _ H1 H2).
induction p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in |- *.
exact (H0 _ _ _ _ H1 H2).
exact (H _ _ _ _ H1 H2).
Admitted.

Lemma st_kill_1 : forall (s : state) (m : Map bool) (a : ad) (p p' : prec_list), prec_list_kill m p = Some p' -> MapGet prec_list s a = Some p -> exists s' : state, states_kill m s = Some s' /\ MapGet prec_list s' a = Some p'.
Proof.
intros.
unfold states_kill in |- *.
elim (map_sum prec_list (states_kill_aux m s)); intros.
cut (MapGet prec_list (states_kill_aux m s) a = Some p').
intro.
rewrite H1 in H2.
inversion H2.
exact (st_kill_0 _ _ _ _ _ H H0).
elim H1.
intros.
elim H2.
intros.
elim H3.
intros.
rewrite H4.
split with (states_kill_aux m s).
rewrite <- H4.
split.
reflexivity.
exact (st_kill_0 _ _ _ _ _ H H0).
intros.
elim H2.
intros.
elim H3.
intros.
rewrite H4.
rewrite <- H4.
split with (states_kill_aux m s).
split.
reflexivity.
Admitted.

Lemma st_kill_2 : forall (s : state) (m : Map bool) (a : ad) (p : prec_list), MapGet prec_list (states_kill_aux m s) a = Some p -> exists p' : prec_list, MapGet prec_list s a = Some p' /\ prec_list_kill m p' = Some p.
Proof.
simple induction s.
intros.
inversion H.
intros.
simpl in H.
elim (option_sum prec_list (prec_list_kill m a0)).
intro y.
elim y.
intros x y0.
rewrite y0 in H.
simpl in H.
elim (bool_is_true_or_false (N.eqb a a1)); intros; rewrite H0 in H.
simpl in |- *.
rewrite H0.
inversion H.
split with a0.
split.
reflexivity.
rewrite H2 in y0.
exact y0.
inversion H.
intro y.
rewrite y in H.
inversion H.
intros.
simpl in H1.
elim (map_sum prec_list (states_kill_aux m1 m)); intros.
rewrite H2 in H1.
elim (map_sum prec_list (states_kill_aux m1 m0)); intros.
rewrite H3 in H1.
inversion H1.
elim H3.
intros.
elim H4.
intros.
elim H5.
intros.
rewrite H6 in H1.
induction a as [| p0].
induction x as [| p0]; inversion H1.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
elim (H0 m1 (Npos p0) p).
intros.
elim H7.
intros.
split with x1.
simpl in |- *.
split; assumption.
simpl in H1.
rewrite H6.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb (Ndouble_plus_one x) (Npos (xI p0)))); intros; rewrite H7 in H1.
inversion H1.
rewrite (Ndouble_plus_one_inv_xI _ _ (Neqb_complete _ _ H7)).
rewrite (Neqb_correct (Npos p0)).
reflexivity.
inversion H1.
simpl in H1.
induction x as [| p1]; inversion H1.
elim (H0 m1 N0 p).
intros.
elim H7.
intros.
split with x1.
simpl in |- *.
split; assumption.
rewrite H6.
simpl in |- *.
simpl in H1.
elim (bool_is_true_or_false (N.eqb (Ndouble_plus_one x) (Npos 1))); intros; rewrite H7 in H1.
inversion H1.
elim (bool_is_true_or_false (N.eqb x N0)); intros; rewrite H8.
reflexivity.
rewrite (Ndouble_plus_one_inv_xH _ (Neqb_complete _ _ H7)) in H8.
inversion H8.
inversion H1.
intros.
elim H4.
intros.
elim H5.
intros.
rewrite H6 in H1.
induction a as [| p0].
inversion H1.
rewrite <- H6 in H1.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in H1.
elim (H0 _ _ _ H1).
intros.
elim H7.
intros.
split with x1.
simpl in |- *.
split; assumption.
inversion H1.
elim (H0 _ _ _ H1).
intros.
elim H7.
intros.
split with x1.
simpl in |- *.
split; assumption.
elim H2.
intros.
elim H3.
intros.
elim H4.
intros.
rewrite H5 in H1.
elim (map_sum prec_list (states_kill_aux m1 m0)); intros.
rewrite H6 in H1.
induction a as [| p0].
simpl in H1.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb (N.double x) N0)); intros; rewrite H7 in H1.
inversion H1.
apply (H m1 N0 p).
rewrite H5.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb x N0)); intros; rewrite H8.
rewrite H9.
reflexivity.
rewrite (Ndouble_inv_N0 _ (Neqb_complete _ _ H7)) in H8.
inversion H8.
inversion H1.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
induction x as [| p1]; inversion H1.
simpl in H1.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb (N.double x) (Npos (xO p0)))); intros; rewrite H7 in H1.
inversion H1.
apply (H m1 (Npos p0) p).
rewrite H5.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb x (Npos p0))); intros; rewrite H8.
rewrite H9.
reflexivity.
rewrite (Ndouble_inv_xO _ _ (Neqb_complete _ _ H7)) in H8.
rewrite (Neqb_correct (Npos p0)) in H8.
inversion H8.
inversion H1.
induction x as [| p0]; inversion H1.
elim H6; intros; elim H7; intros; elim H8; intros.
rewrite H9 in H1.
induction a as [| p0].
simpl in |- *.
simpl in H1.
apply (H m1 N0 p).
rewrite H5.
simpl in |- *.
exact H1.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in |- *; simpl in H1.
apply (H0 m1 (Npos p0) p).
rewrite H9.
simpl in |- *.
exact H1.
apply (H m1 (Npos p0) p).
rewrite H5.
simpl in |- *.
exact H1.
apply (H0 m1 N0 p).
rewrite H9.
exact H1.
rewrite H9 in H1.
rewrite <- H9 in H1.
induction a as [| p0].
simpl in H1.
simpl in |- *.
apply (H m1 N0 p).
rewrite H5.
simpl in |- *.
exact H1.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in |- *; simpl in H1.
apply (H0 m1 (Npos p0) p).
rewrite H9.
rewrite H9 in H1.
exact H1.
apply (H m1 (Npos p0) p).
rewrite H5.
simpl in |- *.
exact H1.
apply (H0 m1 N0 p).
rewrite H9.
simpl in |- *.
rewrite H9 in H1.
simpl in H1.
exact H1.
intros.
elim H3.
intros.
elim H4.
intros.
rewrite H5 in H1.
rewrite <- H5 in H1.
induction a as [| p0].
simpl in |- *.
simpl in H1.
exact (H _ _ _ H1).
induction p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in |- *; simpl in H1.
exact (H0 _ _ _ H1).
exact (H _ _ _ H1).
Admitted.

Lemma st_kill_3 : forall (s' s : state) (m : Map bool), states_kill_aux m s = s' -> s' <> M0 prec_list -> exists p : prec_list, (exists a : ad, MapGet prec_list s' a = Some p).
Proof.
simple induction s'.
intros.
elim (H0 (refl_equal _)).
intros.
elim (map_sum prec_list s); intros.
rewrite H1 in H.
simpl in H.
inversion H.
elim H1; intros; elim H2; intros; elim H3; intros; rewrite H4 in H.
simpl in H.
elim (option_sum prec_list (prec_list_kill m x0)); intro y.
elim y.
intros x1 y0; rewrite y0 in H.
inversion H.
split with a0.
split with a.
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
rewrite y in H.
inversion H.
simpl in H.
elim (map_sum prec_list (states_kill_aux m x)); intros.
rewrite H5 in H.
elim (map_sum prec_list (states_kill_aux m x0)); intros.
rewrite H6 in H.
inversion H.
elim H6; intros; elim H7; intros; elim H8; intros; rewrite H9 in H.
inversion H.
split with a0.
split with (Ndouble_plus_one x1).
simpl in |- *.
rewrite (Neqb_correct (Ndouble_plus_one x1)).
reflexivity.
inversion H.
elim H5; intros; elim H6; intros; elim H7; intros; rewrite H8 in H.
elim (map_sum prec_list (states_kill_aux m x0)); intros.
rewrite H9 in H.
inversion H.
split with a0.
split with (N.double x1).
simpl in |- *.
rewrite (Neqb_correct (N.double x1)).
reflexivity.
elim H9; intros; elim H10; intros; elim H11; intros; rewrite H12 in H.
inversion H.
inversion H.
inversion H.
intros.
elim (map_sum prec_list s).
intros.
rewrite H3 in H1.
simpl in H1.
inversion H1.
intros.
elim H3; intros; elim H4; intros; elim H5; intros; rewrite H6 in H1.
simpl in H1.
elim (option_sum prec_list (prec_list_kill m1 x0)); intro y.
elim y.
intros x1 y0.
rewrite y0 in H1.
inversion H1.
rewrite y in H1.
inversion H1.
simpl in H1.
elim (map_sum prec_list (states_kill_aux m1 x)); intros.
rewrite H7 in H1.
elim (map_sum prec_list (states_kill_aux m1 x0)); intros.
rewrite H8 in H1.
inversion H1.
elim H8; intros; elim H9; intros; elim H10; intros; rewrite H11 in H1.
inversion H1.
inversion H1.
elim (H0 x0 m1).
intros.
elim H12.
intros.
split with x3.
split with (Ndouble_plus_one x4).
rewrite H14.
induction x4 as [| p]; simpl in |- *; exact H15.
rewrite H14 in H11.
exact H11.
intro.
rewrite <- H14 in H12.
inversion H12.
elim H7; intros; elim H8; intros; elim H9; intros; rewrite H10 in H1.
elim (map_sum prec_list (states_kill_aux m1 x0)); intros.
rewrite H11 in H1.
inversion H1.
elim H11; intros; elim H12; intros; elim H13; intros; rewrite H14 in H1.
inversion H1.
elim (H x m1).
intros.
elim H15.
intros.
split with x5.
split with (N.double x6).
rewrite <- H16 in H18.
simpl in H18.
induction x6 as [| p]; simpl in |- *; exact H18.
rewrite H16 in H10.
exact H10.
intro.
rewrite <- H16 in H15.
inversion H15.
inversion H1.
elim (H x m1); intros.
elim H15.
intros.
split with x5.
split with (N.double x6).
rewrite <- H16 in H18.
simpl in H18.
induction x6 as [| p]; simpl in |- *; exact H18.
rewrite H16 in H10.
exact H10.
intro.
rewrite <- H16 in H15.
inversion H15.
inversion H1.
elim (H x m1).
intros.
elim H11.
intros.
split with x3.
split with (N.double x4).
rewrite <- H12 in H14.
simpl in H14.
induction x4 as [| p]; simpl in |- *; exact H14.
rewrite <- H12.
assumption.
intro.
rewrite <- H12 in H11.
Admitted.

Lemma st_kill_4 : forall (s s' : state) (m : Map bool), states_kill m s = Some s' -> exists p : prec_list, (exists a : ad, MapGet prec_list s' a = Some p).
Proof.
unfold states_kill in |- *.
intros.
elim (map_sum prec_list (states_kill_aux m s)); intros.
rewrite H0 in H.
inversion H.
elim H0; intros; elim H1; intros; elim H2; intros; rewrite H3 in H.
inversion H.
apply (st_kill_3 _ _ _ H3).
intro.
inversion H4.
inversion H.
apply (st_kill_3 _ _ _ H3).
intro.
Admitted.

Lemma dt_kill_0 : forall (d : preDTA) (m : Map bool) (a : ad) (s s' : state), states_kill m s = Some s' -> MapGet state d a = Some s -> MapGet state (preDTA_kill m d) a = Some s'.
Proof.
simple induction d.
intros.
inversion H0.
intros.
simpl in H0.
elim (bool_is_true_or_false (N.eqb a a1)); intros; rewrite H1 in H0.
simpl in |- *.
inversion H0.
rewrite H.
simpl in |- *.
rewrite H1.
reflexivity.
inversion H0.
intros.
simpl in |- *.
simpl in H2.
elim (map_sum state (preDTA_kill m1 m)); intros.
rewrite H3.
elim (map_sum state (preDTA_kill m1 m0)); intro.
rewrite H4.
induction a as [| p].
rewrite <- (H _ _ _ _ H1 H2).
rewrite H3.
reflexivity.
induction p as [p Hrecp| p Hrecp| ].
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H4.
reflexivity.
rewrite <- (H _ _ _ _ H1 H2).
rewrite H3.
reflexivity.
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H4.
reflexivity.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
rewrite H7.
induction a as [| p].
rewrite <- (H _ _ _ _ H1 H2).
rewrite H3.
simpl in |- *.
induction x as [| p]; reflexivity.
induction p as [p Hrecp| p Hrecp| ].
rewrite <- (H0 _ _ _ _ H1 H2).
simpl in |- *.
rewrite H7.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb (Ndouble_plus_one x) (Npos (xI p)))); intros; rewrite H8.
elim (bool_is_true_or_false (N.eqb x (Npos p))); intros; rewrite H9.
reflexivity.
rewrite (Ndouble_plus_one_inv_xI _ _ (Neqb_complete _ _ H8)) in H9.
rewrite (Neqb_correct (Npos p)) in H9.
inversion H9.
elim (bool_is_true_or_false (N.eqb x (Npos p))); intros.
rewrite H9.
rewrite (Neqb_complete _ _ H9) in H8.
simpl in H8.
rewrite (aux_Neqb_1_0 p) in H8.
inversion H8.
rewrite H9.
reflexivity.
rewrite <- (H _ _ _ _ H1 H2).
rewrite H3.
simpl in |- *.
induction x as [| p0]; reflexivity.
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H7.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb (Ndouble_plus_one x) (Npos 1))); intros; rewrite H8.
elim (bool_is_true_or_false (N.eqb x N0)); intros; rewrite H9.
reflexivity.
rewrite (Ndouble_plus_one_inv_xH _ (Neqb_complete _ _ H8)) in H9.
rewrite (Neqb_correct N0) in H9.
inversion H9.
elim (bool_is_true_or_false (N.eqb x N0)); intro; rewrite H9.
rewrite (Neqb_complete _ _ H9) in H8.
simpl in H8.
inversion H8.
reflexivity.
intros.
elim H5.
intros.
elim H6.
intros.
rewrite H7.
induction a as [| p].
rewrite <- (H _ _ _ _ H1 H2).
rewrite H3.
reflexivity.
induction p as [p Hrecp| p Hrecp| ].
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H7.
reflexivity.
rewrite <- (H _ _ _ _ H1 H2).
rewrite H3.
reflexivity.
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H7.
reflexivity.
elim H3.
intros.
elim H4.
intros.
elim H5.
intros.
rewrite H6.
elim (map_sum state (preDTA_kill m1 m0)); intros.
rewrite H7.
induction a as [| p].
rewrite <- (H _ _ _ _ H1 H2).
rewrite H6.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb (N.double x) N0)); intros; rewrite H8.
elim (bool_is_true_or_false (N.eqb x N0)); intros; rewrite H9.
reflexivity.
rewrite (Ndouble_inv_N0 _ (Neqb_complete _ _ H8)) in H9.
rewrite (Neqb_correct N0) in H9.
inversion H9.
elim (bool_is_true_or_false (N.eqb x N0)); intros; rewrite H9.
rewrite (Neqb_complete _ _ H9) in H8.
simpl in H8.
inversion H8.
reflexivity.
induction p as [p Hrecp| p Hrecp| ].
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H7.
induction x as [| p0]; reflexivity.
rewrite <- (H _ _ _ _ H1 H2).
rewrite H6.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb (N.double x) (Npos (xO p)))); intros; rewrite H8.
elim (bool_is_true_or_false (N.eqb x (Npos p))); intros; rewrite H9.
reflexivity.
rewrite (Ndouble_inv_xO _ _ (Neqb_complete _ _ H8)) in H9.
rewrite (Neqb_correct (Npos p)) in H9.
inversion H9.
elim (bool_is_true_or_false (N.eqb x (Npos p))); intros; rewrite H9.
rewrite (Neqb_complete _ _ H9) in H8.
simpl in H8.
rewrite (aux_Neqb_1_0 p) in H8.
inversion H8.
reflexivity.
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H7.
induction x as [| p]; reflexivity.
elim H7.
intros.
elim H8.
intros.
elim H9.
intros.
rewrite H10.
induction a as [| p].
simpl in |- *.
rewrite <- (H _ _ _ _ H1 H2).
rewrite H6.
reflexivity.
induction p as [p Hrecp| p Hrecp| ].
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H10.
reflexivity.
rewrite <- (H _ _ _ _ H1 H2).
rewrite H6.
reflexivity.
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H10.
reflexivity.
intros.
elim H8.
intros.
elim H9.
intros.
rewrite H10.
rewrite <- H10.
induction a as [| p].
rewrite <- (H _ _ _ _ H1 H2).
rewrite H6.
reflexivity.
induction p as [p Hrecp| p Hrecp| ].
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H10.
reflexivity.
rewrite <- (H _ _ _ _ H1 H2).
rewrite H6.
reflexivity.
rewrite <- (H0 _ _ _ _ H1 H2).
rewrite H10.
reflexivity.
intros.
elim H4.
intros.
elim H5.
intros.
rewrite H6.
induction a as [| p].
rewrite <- (H _ _ _ _ H1 H2).
rewrite H6.
reflexivity.
induction p as [p Hrecp| p Hrecp| ].
exact (H0 _ _ _ _ H1 H2).
rewrite <- (H _ _ _ _ H1 H2).
rewrite H6.
reflexivity.
Admitted.

Lemma dt_kill_1 : forall (d : preDTA) (m : Map bool) (a : ad) (s : state), MapGet state (preDTA_kill m d) a = Some s -> exists s' : state, MapGet state d a = Some s' /\ states_kill m s' = Some s.
Proof.
simple induction d.
intros.
inversion H.
intros.
simpl in H.
simpl in |- *.
elim (option_sum state (states_kill m a0)); intro y.
elim y.
intros x y0.
rewrite y0 in H.
simpl in H.
elim (bool_is_true_or_false (N.eqb a a1)); intros; rewrite H0 in H; rewrite H0.
inversion H.
split with a0.
split.
reflexivity.
rewrite H2 in y0.
exact y0.
inversion H.
rewrite y in H.
inversion H.
intros.
simpl in H1.
elim (map_sum state (preDTA_kill m1 m)); intros.
rewrite H2 in H1.
elim (map_sum state (preDTA_kill m1 m0)); intros.
rewrite H3 in H1.
inversion H1.
elim H3.
intros.
elim H4.
intros.
elim H5.
intros.
rewrite H6 in H1.
induction a as [| p].
simpl in H1.
induction x as [| p]; inversion H1.
induction p as [p Hrecp| p Hrecp| ]; simpl in |- *; simpl in H1.
apply (H0 m1 (Npos p) s).
rewrite H6.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb (Ndouble_plus_one x) (Npos (xI p)))); intros; rewrite H7 in H1.
inversion H1.
elim (bool_is_true_or_false (N.eqb x (Npos p))); intros; rewrite H8.
reflexivity.
rewrite (Ndouble_plus_one_inv_xI _ _ (Neqb_complete _ _ H7)) in H8.
rewrite (Neqb_correct (Npos p)) in H8.
inversion H8.
inversion H1.
induction x as [| p0]; inversion H1.
apply (H0 m1 N0 s).
rewrite H6.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb (Ndouble_plus_one x) (Npos 1))); intros; rewrite H7 in H1.
inversion H1.
elim (bool_is_true_or_false (N.eqb x N0)); intros; rewrite H8.
reflexivity.
rewrite (Ndouble_plus_one_inv_xH _ (Neqb_complete _ _ H7)) in H8.
inversion H8.
inversion H1.
intros.
elim H4.
intros.
elim H5.
intros.
rewrite H6 in H1.
induction a as [| p].
inversion H1.
rewrite <- H6 in H1.
induction p as [p Hrecp| p Hrecp| ]; simpl in |- *; simpl in H1.
apply (H0 m1 (Npos p) s).
rewrite H6.
rewrite H6 in H1.
exact H1.
inversion H1.
exact (H0 _ _ _ H1).
elim H2.
intros.
elim H3.
intros.
elim H4.
intros.
rewrite H5 in H1.
elim (map_sum state (preDTA_kill m1 m0)); intros.
rewrite H6 in H1.
induction a as [| p].
simpl in |- *.
simpl in H1.
apply (H m1 N0 s).
rewrite H5.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb (N.double x) N0)); intros; rewrite H7 in H1.
inversion H1.
elim (bool_is_true_or_false (N.eqb x N0)); intros; rewrite H8.
reflexivity.
rewrite (Ndouble_inv_N0 _ (Neqb_complete _ _ H7)) in H8.
inversion H8.
inversion H1.
induction p as [p Hrecp| p Hrecp| ]; simpl in |- *; simpl in H1.
induction x as [| p0]; inversion H1.
elim (bool_is_true_or_false (N.eqb (N.double x) (Npos (xO p)))); intros; rewrite H7 in H1.
inversion H1.
apply (H m1 (Npos p) s).
rewrite H5.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb x (Npos p))); intros; rewrite H8.
assumption.
rewrite (Ndouble_inv_xO _ _ (Neqb_complete _ _ H7)) in H8.
rewrite (Neqb_correct (Npos p)) in H8.
inversion H8.
inversion H1.
induction x as [| p]; inversion H1.
elim H6; intros; elim H7; intros; elim H8; intros; rewrite H9 in H1.
rewrite <- H9 in H1.
induction a as [| p].
simpl in |- *.
rewrite <- H5 in H1.
simpl in H1.
exact (H _ _ _ H1).
rewrite <- H5 in H1.
induction p as [p Hrecp| p Hrecp| ]; simpl in |- *; simpl in H1.
exact (H0 _ _ _ H1).
exact (H _ _ _ H1).
exact (H0 _ _ _ H1).
rewrite <- H9 in H1.
rewrite <- H5 in H1.
induction a as [| p].
simpl in |- *.
simpl in H1.
exact (H _ _ _ H1).
induction p as [p Hrecp| p Hrecp| ]; simpl in |- *; simpl in H1.
exact (H0 _ _ _ H1).
exact (H _ _ _ H1).
exact (H0 _ _ _ H1).
intros.
elim H3.
intros.
elim H4.
intros.
rewrite H5 in H1.
rewrite <- H5 in H1.
induction a as [| p].
simpl in |- *.
simpl in H1.
exact (H _ _ _ H1).
induction p as [p Hrecp| p Hrecp| ]; simpl in |- *; simpl in H1.
exact (H0 _ _ _ H1).
exact (H _ _ _ H1).
Admitted.

Lemma dt_kill_empty_d_0 : dt_kill_empty_def_0 0.
Proof.
unfold dt_kill_empty_def_0 in |- *.
intros.
induction t as (a0, t).
simpl in H.
Admitted.

Lemma dt_kill_empty_d_1 : forall (n : nat) (d : preDTA) (p : prec_list) (tl : term_list), dt_kill_empty_def_0 n -> term_high_0 tl <= n -> liste_reconnait d p tl -> exists p' : prec_list, prec_list_kill (dta_non_empty_states d) p = Some p' /\ liste_reconnait (preDTA_kill (dta_non_empty_states d) d) p' tl.
Proof.
simple induction p.
intros.
inversion H3.
elim (pl_sum p1); intros.
rewrite H11.
simpl in |- *.
elim (dt_non_empty_fix d a).
intros.
rewrite H13.
elim (H tl0 H1).
intros.
elim H14.
intros.
rewrite H15.
split with (prec_cons a x prec_empty).
split.
reflexivity.
apply (rec_consi (preDTA_kill (dta_non_empty_states d) d) a x prec_empty hd tl0).
rewrite <- H7 in H2.
exact (H1 d a hd (le_trans _ _ _ (le_max_l _ _) H2) H9).
exact H16.
rewrite <- H7 in H2.
exact (le_trans (term_high_0 tl0) (term_high_0 (tcons hd tl0)) n (le_max_r _ _) H2).
exact H10.
split with hd.
exact H9.
elim H11.
intros.
elim H12.
intros.
elim H13.
intros.
simpl in |- *.
rewrite H14.
rewrite <- H14.
elim (dt_non_empty_fix d a).
intros.
rewrite H16.
rewrite <- H7 in H2.
elim (H tl0 H1 (le_trans _ _ _ (le_max_r _ _) H2) H10).
intros.
elim H17.
intros.
rewrite H18.
elim (option_sum prec_list (prec_list_kill (dta_non_empty_states d) p1)); intro y.
elim y.
intros x3 y0.
rewrite y0.
split with (prec_cons a x2 x3).
split.
reflexivity.
exact (rec_consi (preDTA_kill (dta_non_empty_states d) d) a x2 x3 hd tl0 (H1 d a hd (le_trans _ _ _ (le_max_l _ _) H2) H9) H19).
rewrite y.
split with (prec_cons a x2 prec_empty).
split.
reflexivity.
exact (rec_consi (preDTA_kill (dta_non_empty_states d) d) a x2 prec_empty hd tl0 (H1 d a hd (le_trans _ _ _ (le_max_l _ _) H2) H9) H19).
split with hd.
exact H9.
rewrite <- H6 in H2.
elim (H0 (tcons hd tl0) H1 H2 H9).
intros.
elim H10.
intros.
elim (pl_sum p1); intros.
rewrite H13 in H9.
inversion H9.
elim H13.
intros.
elim H14.
intros.
intros.
elim H15.
intros.
simpl in |- *.
rewrite H16.
rewrite <- H16.
rewrite H11.
elim (option_sum bool (MapGet bool (dta_non_empty_states d) a)).
intro y.
elim y.
intros x3 y0.
rewrite y0.
elim (bool_is_true_or_false x3); intros; rewrite H17.
elim (option_sum prec_list (prec_list_kill (dta_non_empty_states d) p0)); intro y1.
elim y1.
intros x4 y2.
rewrite y2.
split with (prec_cons a x4 x).
split.
reflexivity.
exact (rec_consn (preDTA_kill (dta_non_empty_states d) d) a x4 x hd tl0 H12).
rewrite y1.
split with x.
split.
reflexivity.
exact H12.
split with x.
split.
reflexivity.
exact H12.
intro y.
rewrite y.
split with x.
split.
reflexivity.
exact H12.
intros.
inversion H1.
split with prec_empty.
split.
reflexivity.
Admitted.

Lemma dt_kill_empty_d_2 : forall n : nat, dt_kill_empty_def_0 n -> dt_kill_empty_def_0 (S n).
Proof.
unfold dt_kill_empty_def_0 in |- *.
intros.
inversion H1.
inversion H3.
rewrite <- H11 in H0.
simpl in H0.
fold term_high_0 in H0.
elim (dt_kill_empty_d_1 n d l tl H (le_S_n _ _ H0) H8).
intros.
elim H12.
intros.
apply (rec_dta (preDTA_kill (dta_non_empty_states d) d) a (app c tl) (states_kill_aux (dta_non_empty_states d) ladj)).
elim (st_kill_1 _ _ _ _ _ H13 H7).
intros.
elim H15.
intros.
apply (dt_kill_0 d (dta_non_empty_states d) a ladj (states_kill_aux (dta_non_empty_states d) ladj)).
unfold states_kill in |- *.
elim (map_sum prec_list (states_kill_aux (dta_non_empty_states d) ladj)); intros.
unfold states_kill in H16.
rewrite H18 in H16.
inversion H16.
elim H18; intros; elim H19; intros; elim H20; intros; rewrite H21; reflexivity.
exact H2.
apply (rec_st (preDTA_kill (dta_non_empty_states d) d) (states_kill_aux (dta_non_empty_states d) ladj) c tl x).
exact (st_kill_0 ladj (dta_non_empty_states d) c l x H13 H7).
Admitted.

Lemma pl_kill_prec_empty : forall (p : prec_list) (m : Map bool), prec_list_kill m p = Some prec_empty -> p = prec_empty.
Proof.
simple induction p.
intros.
simpl in H1.
elim (pl_sum p1); intros.
rewrite H2 in H1.
elim (option_sum bool (MapGet bool m a)); intro y.
elim y.
intros x y0.
rewrite y0 in H1.
elim (bool_is_true_or_false x); intros; rewrite H3 in H1.
elim (option_sum prec_list (prec_list_kill m p0)); intro y1.
elim y1.
intros x0 y2.
rewrite y2 in H1.
inversion H1.
rewrite y1 in H1.
inversion H1.
inversion H1.
rewrite y in H1.
inversion H1.
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
elim (bool_is_true_or_false x2).
intros.
rewrite H6 in H1.
elim (option_sum prec_list (prec_list_kill m p0)); intro y1.
elim y1.
intros x3 y2.
rewrite y2 in H1.
elim (option_sum prec_list (prec_list_kill m (prec_cons x x0 x1))); intro y3.
elim y3.
intros x4 y4.
rewrite y4 in H1.
inversion H1.
rewrite y3 in H1.
inversion H1.
rewrite y1 in H1.
elim (option_sum prec_list (prec_list_kill m (prec_cons x x0 x1))); intro y2.
elim y2.
intros x4 y3.
rewrite y3 in H1.
inversion H1.
rewrite H8 in y3.
rewrite <- H5 in y3.
rewrite (H0 _ y3) in H5.
inversion H5.
rewrite y2 in H1.
inversion H1.
intros.
rewrite H6 in H1.
rewrite <- H5 in H1.
rewrite (H0 _ H1) in H5.
inversion H5.
rewrite y in H1.
rewrite <- H5 in H1.
rewrite (H0 _ H1) in H5.
inversion H5.
intros.
reflexivity.
