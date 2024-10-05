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
inversion H11.
