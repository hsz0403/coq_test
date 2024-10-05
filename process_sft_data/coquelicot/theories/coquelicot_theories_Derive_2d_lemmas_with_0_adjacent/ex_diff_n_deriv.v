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

Lemma ex_diff_n_deriv: forall n p q, (p+q <= n)%nat -> forall f x y, ex_diff_n f n x y-> ex_diff_n (partial_derive p q f) (n -(p+q)) x y.
induction p.
intros q; rewrite plus_0_l.
induction q.
intros H f x y H1.
unfold partial_derive.
simpl.
rewrite - minus_n_O.
apply: (ex_diff_n_ext_loc _ _ _ _ _ _ H1).
now apply locally_2d_forall.
intros H f x y H1.
apply (ex_diff_n_ext_loc (fun u v => Derive (fun z => (partial_derive 0 q f) u z) v)).
apply locally_2d_forall.
intros u v; unfold partial_derive.
reflexivity.
apply ex_diff_n_deriv_aux2.
replace ((S (n - S q))) with (n-q)%nat by omega.
apply IHq.
now apply lt_le_weak.
exact H1.
intros q H f x y H1.
apply (ex_diff_n_ext_loc (fun u v => Derive (fun z => (partial_derive p q f) z v) u)).
apply locally_2d_forall.
intros u v; unfold partial_derive.
reflexivity.
apply ex_diff_n_deriv_aux1.
replace ((S (n - (S p +q)))) with (n-(p+q))%nat by omega.
apply IHp.
now apply lt_le_weak.
exact H1.
