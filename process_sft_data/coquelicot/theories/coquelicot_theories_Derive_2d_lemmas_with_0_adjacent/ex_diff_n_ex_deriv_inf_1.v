Require Import Reals Omega Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Hierarchy Continuity Derive.
Definition differentiable_pt_lim (f : R -> R -> R) (x y : R) (lx ly : R) := forall eps : posreal, locally_2d (fun u v => Rabs (f u v - f x y - (lx * (u - x) + ly * (v - y))) <= eps * Rmax (Rabs (u - x)) (Rabs (v - y))) x y.
Definition differentiable_pt (f : R -> R -> R) (x y : R) := exists lx, exists ly, differentiable_pt_lim f x y lx ly.
Definition partial_derive (m k : nat) (f : R -> R -> R) : R -> R -> R := fun x y => Derive_n (fun t => Derive_n (fun z => f t z) k y) m x.
Definition differential (p : nat) (f : R -> R -> R) (x y dx dy : R) : R := sum_f_R0 (fun m => C p m * partial_derive m (p - m)%nat f x y * dx ^ m * dy ^ (p - m)%nat) p.
Definition DL_pol (n : nat) (f : R -> R -> R) (x y dx dy : R) : R := sum_f_R0 (fun p => differential p f x y dx dy / INR (fact p)) n.
Fixpoint ex_diff_n f n x y := continuity_2d_pt f x y /\ match n with | O => True | S n => ex_derive (fun z => f z y) x /\ ex_derive (fun z => f x z) y /\ ex_diff_n (fun u v => Derive (fun z => f z v) u) n x y /\ ex_diff_n (fun u v => Derive (fun z => f u z) v) n x y end.
Definition DL_regular_n f m x y := exists D, locally_2d (fun u v => Rabs (f u v - DL_pol m f x y (u-x) (v-y)) <= D * (Rmax (Rabs (u-x)) (Rabs (v-y))) ^ (S m)) x y.

Lemma ex_diff_n_ex_deriv_inf_1 : forall n p k, (p+k < n)%nat -> forall f x y, ex_diff_n f n x y -> ex_derive (fun z : R => partial_derive p k f z y) x.
Proof.
intros n p; case p; clear p.
intros k; case k; clear k.
case n; clear n.
intros Hn; contradict Hn; apply lt_n_O.
intros n _ f x y H.
unfold partial_derive; simpl.
apply H.
intros n0 H f x y Hf.
assert (ex_diff_n (partial_derive 0 n0 f) (n -(0+n0)) x y).
apply ex_diff_n_deriv.
auto with zarith.
exact Hf.
revert H0; rewrite plus_0_l.
case_eq (n-n0)%nat.
intros H1; contradict H; auto with zarith.
intros n1 H1 H2.
apply ex_derive_ext with (fun z => Derive (fun t => (partial_derive 0 n0 f z) t) y).
intros y0; unfold partial_derive; simpl.
reflexivity.
simpl in H2.
destruct H2 as (T1&T2&T3&T4&T5).
case_eq n1.
intros H2; rewrite H2 in H1.
clear -H H1; contradict H; auto with zarith.
intros n2 Hn2; rewrite Hn2 in T5.
apply T5.
intros p q H f x y Hf.
assert (ex_diff_n (partial_derive p q f) (n -(p+q)) x y).
apply ex_diff_n_deriv.
auto with zarith.
exact Hf.
case_eq (n-(p+q))%nat.
intros H1; contradict H; auto with zarith.
intros n1 H1.
apply ex_derive_ext with (fun z => Derive (fun t => (partial_derive p q f t) y) z).
intros x0; unfold partial_derive; simpl.
reflexivity.
rewrite H1 in H0; simpl in H0.
destruct H0 as (T1&T2&T3&T4&T5).
case_eq n1.
intros H2; rewrite H2 in H1.
clear -H H1; contradict H; auto with zarith.
intros n2 Hn2; rewrite Hn2 in T4.
apply T4.
