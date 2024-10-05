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
exact pl_path_incl_nil.
