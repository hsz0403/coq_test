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
exact pl_tl_O.
