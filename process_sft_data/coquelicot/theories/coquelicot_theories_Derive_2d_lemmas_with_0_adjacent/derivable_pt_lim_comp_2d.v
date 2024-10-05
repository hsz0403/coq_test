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

Lemma derivable_pt_lim_comp_2d : forall f1 f2 f3 x l1x l1y l2 l3, differentiable_pt_lim f1 (f2 x) (f3 x) l1x l1y -> derivable_pt_lim f2 x l2 -> derivable_pt_lim f3 x l3 -> derivable_pt_lim (fun t => f1 (f2 t) (f3 t)) x (l1x * l2 + l1y * l3).
Proof.
intros.
apply (differentiable_pt_lim_proj1_1 _ x 0 (l1x * l2 + l1y * l3)).
pattern 0 at 2 ; replace 0 with (l1x * 0 + l1y * 0) by ring.
apply differentiable_pt_lim_comp.
apply H.
apply: differentiable_pt_lim_proj1_0 H0.
apply: differentiable_pt_lim_proj1_0 H1.
