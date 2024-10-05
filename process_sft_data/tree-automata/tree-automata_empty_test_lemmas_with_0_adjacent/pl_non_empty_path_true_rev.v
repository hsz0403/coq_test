Require Import Bool.
Require Import Arith.
Require Import NArith.
Require Import Ndec.
Require Import ZArith.
Require Import Classical_Prop.
From IntMap Require Import Allmaps.
Require Import lattice_fixpoint.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import pl_path.
Fixpoint pl_non_empty (m : Map bool) (p : prec_list) {struct p} : bool := match p with | prec_empty => true | prec_cons a la ls => match ls with | prec_empty => match MapGet bool m a with | Some b => b && pl_non_empty m la | None => false end | prec_cons _ _ _ => match MapGet bool m a with | Some b => pl_non_empty m ls || b && pl_non_empty m la | None => pl_non_empty m ls end end end.
Fixpoint st_non_empty (m : Map bool) (s : state) {struct s} : bool := match s with | M0 => false | M1 _ p => pl_non_empty m p | M2 a b => st_non_empty m a || st_non_empty m b end.
Fixpoint dta_app_ne_aux (d : preDTA) (m r : Map bool) {struct r} : Map bool := match d, r with | M0, _ => M0 bool | M1 a s, M0 => M0 bool | M1 a s, M1 a' b => if N.eqb a a' then M1 bool a (b || st_non_empty m s) else M0 bool | M1 a s, M2 _ _ => M0 bool | M2 d0 d1, M0 => M0 bool | M2 d0 d1, M1 _ _ => M0 bool | M2 d0 d1, M2 r0 r1 => M2 bool (dta_app_ne_aux d0 m r0) (dta_app_ne_aux d1 m r1) end.
Definition dta_app_ne (d : preDTA) (m : Map bool) : Map bool := dta_app_ne_aux d m m.
Definition dta_non_empty_states (d : preDTA) : Map bool := power (Map bool) (dta_app_ne d) (map_mini state d) (S (MapCard state d)).
Definition dta_states_non_empty (d : DTA) : Map bool := match d with | dta p a => dta_non_empty_states p end.
Definition dta_non_empty_states_lazy (d : preDTA) : Map bool := lazy_power bool eqm_bool (dta_app_ne d) (map_mini state d) (S (MapCard state d)).
Definition dta_states_non_empty_lazy (d : DTA) : Map bool := match d with | dta p a => dta_non_empty_states_lazy p end.
Inductive pl_path_true : pl_path -> Map bool -> Prop := | plp_true_nil : forall m : Map bool, pl_path_true pl_path_nil m | plp_true_cons : forall (m : Map bool) (a : ad) (pl : pl_path), pl_path_true pl m -> MapGet bool m a = Some true -> pl_path_true (pl_path_cons a pl) m.
Definition pl_non_empty_path_true_def_0 (pl : pl_path) (p : prec_list) : Prop := forall m : Map bool, pl_path_incl pl p -> pl_path_true pl m -> pl_non_empty m p = true.
Definition dt_non_empty_def_0 (d : preDTA) (a : ad) (t : term) (pr : reconnaissance d a t) := forall n : nat, term_high t <= n -> MapGet bool (power (Map bool) (dta_app_ne d) (map_mini state d) n) a = Some true.
Definition dt_non_empty_def_1 (d : preDTA) (s : state) (t : term) (pr : state_reconnait d s t) := forall n : nat, term_high t <= S n -> st_non_empty (power (Map bool) (dta_app_ne d) (map_mini state d) n) s = true.
Definition dt_non_empty_def_2 (d : preDTA) (p : prec_list) (t : term_list) (pr : liste_reconnait d p t) := forall n : nat, term_high_0 t <= n -> pl_non_empty (power (Map bool) (dta_app_ne d) (map_mini state d) n) p = true.
Definition dt_non_empty_r_def_0 (n : nat) : Prop := forall (d : preDTA) (a : ad), MapGet bool (power (Map bool) (dta_app_ne d) (map_mini state d) n) a = Some true -> exists t : term, reconnaissance d a t.

Lemma pl_non_empty_path_true_rev : forall (p : prec_list) (m : Map bool), pl_non_empty m p = true -> exists plp : pl_path, pl_path_incl plp p /\ pl_path_true plp m.
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
elim (bool_is_true_or_false x); intro; rewrite H3 in H1.
elim (bool_is_true_or_false (pl_non_empty m p0)); intros.
elim (H m H4).
intros.
elim H5.
intros.
split with (pl_path_cons a x0).
split.
exact (pl_path_incl_cons x0 a p0 p1 H6).
rewrite H3 in y0.
exact (plp_true_cons m a x0 H7 y0).
rewrite H4 in H1.
inversion H1.
elim (bool_is_true_or_false (pl_non_empty m p0)); intro; rewrite H4 in H1; inversion H1.
rewrite y in H1.
inversion H1.
elim H2.
intros.
elim H3.
intros.
elim H4.
intros.
rewrite H5 in H1.
rewrite <- H5 in H1.
elim (option_sum bool (MapGet bool m a)); intro y.
elim y.
intros x2 y0.
rewrite y0 in H1.
elim (bool_is_true_or_false (pl_non_empty m p1)); intros.
elim (H0 m H6); intros.
split with x3.
split.
elim H7.
intros.
apply (pl_path_incl_next x3 a p0 p1 H8).
intro.
rewrite H10 in H8.
rewrite H5 in H8.
inversion H8.
exact (H16 (refl_equal _)).
elim H7; intros.
assumption.
rewrite H6 in H1.
elim (bool_is_true_or_false (x2 && pl_non_empty m p0)); intros; rewrite H7 in H1.
elim (bool_is_true_or_false x2); intros; rewrite H8 in H7.
rewrite H8 in y0.
elim (bool_is_true_or_false (pl_non_empty m p0)); intros.
elim (H m H9); intros.
split with (pl_path_cons a x3).
split.
elim H10.
intros.
exact (pl_path_incl_cons x3 a p0 p1 H11).
elim H10.
intros.
exact (plp_true_cons m a x3 H12 y0).
rewrite H9 in H7.
inversion H7.
elim (bool_is_true_or_false (pl_non_empty m p0)); intros; rewrite H9 in H7; inversion H7.
inversion H1.
rewrite y in H1.
elim (H0 _ H1).
intros.
split with x2.
split.
apply (pl_path_incl_next x2 a p0 p1).
elim H6.
intros.
assumption.
intro.
rewrite H7 in H6.
elim H6.
intros.
inversion H8.
rewrite <- H11 in H5.
inversion H5.
exact (H11 (refl_equal _)).
elim H6; intros.
assumption.
intros.
split with pl_path_nil.
split.
exact pl_path_incl_nil.
exact (plp_true_nil m).
