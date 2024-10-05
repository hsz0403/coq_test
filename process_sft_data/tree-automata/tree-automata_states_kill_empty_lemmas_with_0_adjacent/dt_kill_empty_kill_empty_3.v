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
elim H6; intros; elim H7; intros; elim H8; intros; rewrite H9 in H3; rewrite <- H9 in H3; inversion H3; reflexivity.
