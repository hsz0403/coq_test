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

Lemma partial_derive_add_zero: forall f p q r s x y, (q=0)%nat \/ (r=0)%nat -> partial_derive p q (partial_derive r s f) x y = partial_derive (p+r) (q+s) f x y.
intros f p q r s x y H.
destruct H; rewrite H.
rewrite plus_0_l.
unfold partial_derive.
simpl.
rewrite -Derive_n_comp.
now apply Derive_n_ext.
rewrite plus_0_r.
unfold partial_derive.
simpl.
apply Derive_n_ext.
intros y0.
rewrite -Derive_n_comp.
now apply Derive_n_ext.
