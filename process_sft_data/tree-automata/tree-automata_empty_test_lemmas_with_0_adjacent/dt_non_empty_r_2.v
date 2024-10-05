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

Lemma dt_non_empty_r_2 : forall (p : prec_list) (m : Map bool), pl_non_empty m p = true -> exists pl : pl_path, pl_path_true pl m /\ pl_path_incl pl p.
Proof.
simple induction p.
intros.
simpl in H1.
elim (pl_sum p1).
intros.
rewrite H2 in H1.
elim (option_sum bool (MapGet bool m a)).
intro y.
elim y.
intros x y0.
rewrite y0 in H1.
elim (bool_is_true_or_false x); intros; rewrite H3 in H1; simpl in H1.
elim (H m H1).
intros.
elim H4.
intros.
rewrite H3 in y0.
split with (pl_path_cons a x0).
split.
exact (plp_true_cons m a x0 H5 y0).
exact (pl_path_incl_cons x0 a p0 p1 H6).
inversion H1.
intro y.
rewrite y in H1.
inversion H1.
intros.
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
rewrite <- H5 in H1.
elim (bool_is_true_or_false (pl_non_empty m p1)); intros.
elim (H0 _ H6).
intros.
elim H7.
intros.
split with x3.
split.
exact H8.
apply (pl_path_incl_next x3 a p0 p1 H9).
intro.
rewrite H10 in H9.
inversion H9.
rewrite <- H12 in H5.
inversion H5.
elim (H12 (refl_equal _)).
rewrite H6 in H1.
simpl in H1.
elim (bool_is_true_or_false x2); intro.
rewrite H7 in y0.
elim (bool_is_true_or_false (pl_non_empty m p0)); intro.
elim (H _ H8).
intros.
elim H9.
intros.
split with (pl_path_cons a x3).
split.
exact (plp_true_cons _ _ _ H10 y0).
exact (pl_path_incl_cons x3 a p0 p1 H11).
rewrite H8 in H1.
rewrite H7 in H1.
inversion H1.
rewrite H7 in H1.
inversion H1.
rewrite y in H1.
rewrite <- H5 in H1.
elim (H0 _ H1).
intros.
elim H6.
intros.
split with x2.
split.
exact H7.
apply (pl_path_incl_next x2 a p0 p1 H8).
intro.
rewrite H9 in H8.
inversion H8.
rewrite <- H11 in H5.
inversion H5.
elim H11.
reflexivity.
intros.
split with pl_path_nil.
split.
exact (plp_true_nil m).
exact pl_path_incl_nil.
