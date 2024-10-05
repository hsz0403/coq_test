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
exact (H0 _ _ _ H1).
