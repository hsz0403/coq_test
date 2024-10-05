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

Lemma dt_kill_empty_semantics : forall (d : preDTA) (a : ad) (t : term), reconnaissance d a t <-> reconnaissance (preDTA_kill (dta_non_empty_states d) d) a t.
Proof.
intros.
split.
exact (dt_kill_empty_d d a t).
Admitted.

Lemma dta_kill_empty_states_semantics : forall (d : DTA) (t : term), reconnait d t <-> reconnait (DTA_kill_empty_states d) t.
Proof.
simple induction d.
intros.
unfold DTA_kill_empty_states in |- *.
simpl in |- *.
elim (option_sum state (MapGet state (preDTA_kill (dta_non_empty_states p) p) a)).
intro y.
elim y.
intros x y0.
rewrite y0.
exact (dt_kill_empty_semantics p a t).
intro y.
rewrite y.
split.
intros.
elim (dt_non_empty_fix p a).
intros.
elim (dt_kill_empty_semantics p a t).
intros.
cut (reconnaissance (preDTA_kill (dta_non_empty_states p) p) a t).
intro.
inversion H4.
rewrite H5 in y.
inversion y.
exact (H2 H).
intros.
simpl in H.
inversion H.
inversion H1.
simpl in H0.
inversion H0.
rewrite <- H11 in H5.
Admitted.

Lemma dta_kill_empty_states_lazy_semantics : forall (d : DTA) (t : term), reconnait d t <-> reconnait (DTA_kill_empty_states_lazy d) t.
Proof.
intro.
rewrite (kill_empty_states_lazy_eg_kill_empty_states d).
Admitted.

Lemma kill_empty_correct_wrt_sign_invar_0 : forall (p p' : prec_list) (m : Map bool) (n : nat), pl_tl_length p n -> prec_list_kill m p = Some p' -> pl_tl_length p' n.
Proof.
simple induction p.
intros.
simpl in H2.
elim (pl_sum p1); intros.
rewrite H3 in H2.
elim (option_sum bool (MapGet bool m a)); intro y.
elim y.
intros x y0.
rewrite y0 in H2.
elim (bool_is_true_or_false x); intros; rewrite H4 in H2.
elim (option_sum prec_list (prec_list_kill m p0)); intro y1.
elim y1.
intros x0 y2.
rewrite y2 in H2.
inversion H2.
elim (nat_sum n); intros.
rewrite H5 in H1.
inversion H1.
elim H5.
intros.
rewrite H7.
apply (pl_tl_S a x0 x1).
rewrite H7 in H1.
inversion H1.
exact (H _ _ _ H9 y2).
exact (H _ _ _ H10 y2).
rewrite y1 in H2.
inversion H2.
inversion H2.
rewrite y in H2.
inversion H2.
elim H3.
intros.
elim H4.
intros.
elim H5.
intros.
rewrite H6 in H2.
rewrite <- H6 in H2.
elim (option_sum bool (MapGet bool m a)); intro y.
elim y.
intros x2 y0.
rewrite y0 in H2.
elim (bool_is_true_or_false x2); intros; rewrite H7 in H2.
elim (option_sum prec_list (prec_list_kill m p0)); intro y1.
elim y1.
intros x3 y2.
rewrite y2 in H2.
elim (option_sum prec_list (prec_list_kill m p1)); intro y3.
elim y3.
intros x4 y4.
rewrite y4 in H2.
inversion H2.
elim (nat_sum n); intros.
rewrite H8 in H1.
inversion H1.
elim H8.
intros.
rewrite H10 in H1.
inversion H1.
rewrite <- H14 in H6.
inversion H6.
rewrite H10.
apply (pl_tl_propag a x3 x4 x5).
exact (H _ _ _ H13 y2).
exact (H0 _ _ _ H16 y4).
rewrite y3 in H2.
inversion H2.
elim (nat_sum n); intros.
rewrite H8 in H1.
inversion H1.
elim H8.
intros.
rewrite H10 in H1.
rewrite H10.
inversion H1.
rewrite <- H14 in H6.
inversion H6.
apply (pl_tl_S a x3 x4).
exact (H _ _ _ H13 y2).
rewrite y1 in H2.
elim (option_sum prec_list (prec_list_kill m p1)); intro y2.
elim y2.
intros x3 y3.
rewrite y3 in H2.
inversion H2.
rewrite <- H9.
inversion H1.
rewrite <- H12 in H6.
inversion H6.
exact (H0 _ _ _ H14 y3).
rewrite y2 in H2.
inversion H2.
inversion H1.
rewrite <- H11 in H6.
inversion H6.
exact (H0 _ _ _ H13 H2).
rewrite y in H2.
inversion H1.
rewrite <- H10 in H6.
inversion H6.
exact (H0 _ _ _ H12 H2).
intros.
inversion H.
simpl in H0.
inversion H0.
Admitted.

Lemma kill_empty_correct_wrt_sign_invar_1 : forall (s : state) (sigma : signature) (m : Map bool), state_correct_wrt_sign s sigma -> state_correct_wrt_sign (states_kill_aux m s) sigma.
Proof.
unfold state_correct_wrt_sign in |- *.
intros.
elim (st_kill_2 s m a p H0).
intros.
elim H1.
intros.
elim (H a x H2).
intros.
elim H4.
intros.
split with x0.
split.
exact H5.
Admitted.

Lemma kill_empty_correct_wrt_sign_invar : forall (d : preDTA) (sigma : signature) (m : Map bool), predta_correct_wrt_sign d sigma -> predta_correct_wrt_sign (preDTA_kill m d) sigma.
Proof.
unfold predta_correct_wrt_sign in |- *.
intros.
elim (dt_kill_1 _ _ _ _ H0).
intros.
elim H1.
intros.
cut (s = states_kill_aux m x).
intros.
rewrite H4.
exact (kill_empty_correct_wrt_sign_invar_1 _ _ _ (H _ _ H2)).
unfold states_kill in H3.
elim (map_sum prec_list (states_kill_aux m x)); intros.
rewrite H4 in H3.
inversion H3.
Admitted.

Lemma dt_kill_empty_kill_empty_0 : forall (d : preDTA) (p p' : prec_list), prec_list_kill (dta_non_empty_states d) p = Some p' -> exists plp : pl_path, pl_path_incl plp p'.
Proof.
simple induction p.
intros.
simpl in H1.
elim (pl_sum p1); intros.
rewrite H2 in H1.
elim (option_sum bool (MapGet bool (dta_non_empty_states d) a)); intro y.
elim y.
intros x y0.
rewrite y0 in H1.
elim (bool_is_true_or_false x); intros.
rewrite H3 in H1.
elim (option_sum prec_list (prec_list_kill (dta_non_empty_states d) p0)); intro y1.
elim y1.
intros x0 y2.
rewrite y2 in H1.
inversion H1.
elim (H _ y2).
intros.
split with (pl_path_cons a x1).
exact (pl_path_incl_cons x1 a x0 prec_empty H4).
rewrite y1 in H1.
inversion H1.
rewrite H3 in H1.
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
elim (option_sum bool (MapGet bool (dta_non_empty_states d) a)); intro y.
elim y.
intros x2 y0.
rewrite y0 in H1.
elim (bool_is_true_or_false x2); intros; rewrite H6 in H1.
elim (option_sum prec_list (prec_list_kill (dta_non_empty_states d) p0)); intro y1.
elim y1.
intros x3 y2.
rewrite <- H5 in H1.
elim (option_sum prec_list (prec_list_kill (dta_non_empty_states d) p0)); intro y3.
elim y3.
intros x4 y4.
rewrite y4 in H1.
elim (option_sum prec_list (prec_list_kill (dta_non_empty_states d) p1)); intro y5.
elim y5.
intros x5 y6.
rewrite y6 in H1.
inversion H1.
elim (H _ y4).
intros.
split with (pl_path_cons a x6).
exact (pl_path_incl_cons x6 a x4 x5 H7).
rewrite y5 in H1.
inversion H1.
elim (H _ y4).
intros.
split with (pl_path_cons a x5).
exact (pl_path_incl_cons x5 a x4 prec_empty H7).
rewrite y3 in H1.
elim (option_sum prec_list (prec_list_kill (dta_non_empty_states d) p1)); intro y4.
elim y4.
intros x4 y5.
rewrite y5 in H1.
inversion H1.
rewrite <- H8.
elim (H0 _ y5).
intros.
split with x5.
exact H7.
rewrite y4 in H1.
inversion H1.
rewrite y1 in H1.
elim (option_sum prec_list (prec_list_kill (dta_non_empty_states d) (prec_cons x x0 x1))).
intro y2.
elim y2.
intros x3 y3.
rewrite y3 in H1.
inversion H1.
rewrite <- H5 in y3.
rewrite <- H8.
exact (H0 _ y3).
intro y2.
rewrite y2 in H1.
inversion H1.
rewrite <- H5 in H1.
exact (H0 _ H1).
rewrite y in H1.
rewrite <- H5 in H1.
exact (H0 _ H1).
intros.
simpl in H.
inversion H.
split with pl_path_nil.
Admitted.

Lemma dt_kill_empty_kill_empty_1 : forall (d : preDTA) (plp : pl_path) (tl : term_list), pl_path_recon d tl plp <-> pl_path_recon (preDTA_kill (dta_non_empty_states d) d) tl plp.
Proof.
simple induction plp.
intros.
split; intros.
inversion H.
exact (pl_path_rec_nil (preDTA_kill (dta_non_empty_states d) d)).
inversion H.
exact (pl_path_rec_nil d).
intros.
split; intros.
inversion H0.
apply (pl_path_rec_cons (preDTA_kill (dta_non_empty_states d) d) a t p tl0).
elim (dt_kill_empty_semantics d a t).
intros.
exact (H7 H5).
elim (H tl0).
intros.
exact (H7 H6).
inversion H0.
apply (pl_path_rec_cons d a t p tl0).
elim (dt_kill_empty_semantics d a t).
intros.
exact (H8 H5).
elim (H tl0).
intros.
Admitted.

Lemma dt_kill_empty_kill_empty_2 : forall (d : preDTA) (p : prec_list) (plp : pl_path), pl_path_incl plp p -> pl_path_true plp (dta_non_empty_states d) -> exists tl : term_list, pl_path_recon d tl plp.
Proof.
simple induction p.
intros.
inversion H1.
inversion H2.
rewrite <- H8 in H4.
inversion H4.
elim (dt_non_empty_fix d a1).
intros.
elim (H12 H9).
intros.
rewrite <- H4 in H10.
inversion H10.
rewrite H17 in H8.
elim (H _ H5 H8).
intros.
split with (tcons x x0).
rewrite H3 in H16.
rewrite <- H16.
exact (pl_path_rec_cons d a1 x plp0 x0 H14 H15).
inversion H2.
elim (H8 (sym_eq H9)).
elim (H0 plp H6 H2).
intros.
split with x.
rewrite H11.
exact H13.
intros.
inversion H.
split with tnil.
Admitted.

Lemma dt_kill_empty_kill_empty_3 : forall (d : preDTA) (a : ad) (s : state) (sigma : signature), MapGet state (preDTA_kill (dta_non_empty_states d) d) a = Some s -> predta_correct_wrt_sign d sigma -> exists t : term, reconnaissance (preDTA_kill (dta_non_empty_states d) d) a t.
Proof.
intros.
elim (dt_kill_1 _ _ _ _ H).
intros.
elim H1.
intros.
elim (st_kill_4 _ _ _ H3).
intros.
elim H4.
intros.
unfold states_kill in H3.
cut (states_kill_aux (dta_non_empty_states d) x = s).
intro.
rewrite <- H6 in H5.
elim (st_kill_2 _ _ _ _ H5).
intros.
elim H7.
intros.
elim (dt_kill_empty_kill_empty_0 _ _ _ H9).
intros.
elim (pl_kill_1 _ _ _ _ H9 H10).
intros.
elim (dt_kill_empty_kill_empty_2 _ _ _ H11 H12).
intros.
elim (dt_kill_empty_kill_empty_1 d x3 x4).
intros.
split with (app x1 x4).
apply (rec_dta (preDTA_kill (dta_non_empty_states d) d) a (app x1 x4) s H).
rewrite <- H6.
apply (rec_st (preDTA_kill (dta_non_empty_states d) d) (states_kill_aux (dta_non_empty_states d) x) x1 x4 x0 H5).
elim (kill_empty_correct_wrt_sign_invar d sigma (dta_non_empty_states d) H0 a s H x1 x0).
intros.
elim H16.
intros.
exact (pl_path_rec_equiv_1 x3 x0 H10 (preDTA_kill (dta_non_empty_states d) d) x4 x5 (H14 H13) H18).
rewrite H6 in H5.
exact H5.
elim (map_sum prec_list (states_kill_aux (dta_non_empty_states d) x)); intros.
rewrite H6 in H3.
inversion H3.
Admitted.

Lemma dt_kill_empty_kill_empty : forall (d : preDTA) (a : ad) (sigma : signature), predta_correct_wrt_sign d sigma -> ((exists s : state, MapGet state (preDTA_kill (dta_non_empty_states d) d) a = Some s) <-> (exists t : term, reconnaissance d a t)).
Proof.
intros.
split; intros.
elim H0.
intros.
elim (dt_kill_empty_kill_empty_3 d a x sigma H1 H).
intros.
elim (dt_kill_empty_semantics d a x0).
intros.
split with x0.
elim H1.
intros.
elim (dt_kill_empty_semantics d a x0).
intros.
exact (H6 H2).
elim H0.
intros.
cut (reconnaissance (preDTA_kill (dta_non_empty_states d) d) a x).
intro.
inversion H2.
split with ladj.
exact H3.
elim (dt_kill_empty_semantics d a x).
intros.
exact (H2 H1).
