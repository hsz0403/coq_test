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

Lemma dt_non_empty_r_4 : forall (p : prec_list) (n : nat) (d : preDTA) (pl : pl_path), dt_non_empty_r_def_0 n -> pl_path_true pl (power (Map bool) (dta_app_ne d) (map_mini state d) n) -> pl_path_incl pl p -> exists tl : term_list, liste_reconnait d p tl.
Proof.
unfold dt_non_empty_r_def_0 in |- *.
simple induction p.
intros.
inversion H2.
inversion H3.
rewrite <- H4 in H7.
inversion H7.
elim H11; auto.
elim (H1 _ _ H5).
intros.
inversion H3.
rewrite <- H10 in H6.
inversion H6.
rewrite <- H10 in H2.
inversion H2.
elim (H n d plp H1 H18 H11).
intros.
split with (tcons x x0).
rewrite H15 in H8.
rewrite H9 in H8.
exact (rec_consi d a p0 p1 x x0 H8 H21).
elim (H0 n d pl H1 H2 H12).
intros.
induction x0 as [| t x0 Hrecx0].
inversion H15.
rewrite <- H17 in H12.
inversion H12.
elim H14; auto.
split with (tcons t x0).
exact (rec_consn d a p0 p1 t x0 H15).
intros.
inversion H1.
split with tnil.
exact (rec_empty d).
