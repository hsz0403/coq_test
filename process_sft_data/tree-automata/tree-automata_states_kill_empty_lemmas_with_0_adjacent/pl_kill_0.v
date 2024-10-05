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
exact pl_path_incl_nil.
