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

Lemma ex_diff_n_ext_loc: forall f g n x y, locally_2d (fun u v => f u v = g u v) x y -> ex_diff_n f n x y -> ex_diff_n g n x y.
Proof.
intros f g n; revert f g.
induction n.
intros f g x y H; simpl.
intros (H1,_); split.
apply (continuity_2d_pt_ext_loc _ _ _ _ H H1).
easy.
simpl.
intros f g x y H (H1&H2&H3&H4&H5).
split.
apply (continuity_2d_pt_ext_loc _ _ _ _ H H1).
split.
apply: ex_derive_ext_loc H2.
apply locally_2d_1d_const_y with (1:=H).
split.
apply: ex_derive_ext_loc H3.
apply locally_2d_1d_const_x with (1:=H).
split.
apply IHn with (2:=H4).
apply locally_2d_impl_strong with (2:=H).
apply locally_2d_forall.
intros u v H6.
apply Derive_ext_loc.
apply locally_2d_1d_const_y with (1:=H6).
apply IHn with (2:=H5).
apply locally_2d_impl_strong with (2:=H).
apply locally_2d_forall.
intros u v H6.
apply Derive_ext_loc.
apply locally_2d_1d_const_x with (1:=H6).
