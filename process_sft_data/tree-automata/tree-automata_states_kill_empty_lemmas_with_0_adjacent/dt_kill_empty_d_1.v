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
exact (rec_empty _).
