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

Lemma differentiable_pt_lim_proj1_0 (f : R -> R) (x y l : R) : derivable_pt_lim f x l -> differentiable_pt_lim (fun u v => f u) x y l 0.
Proof.
intros Df eps.
apply is_derive_Reals in Df ; elim (proj2 Df x (fun P H => H) eps) ; clear Df ; intros delta Df.
exists delta ; simpl ; intros.
rewrite Rmult_0_l Rplus_0_r.
apply (Rle_trans _ (eps * Rabs (u - x))).
rewrite Rmult_comm ; apply (Df _ H).
apply Rmult_le_compat_l.
apply Rlt_le, eps.
apply RmaxLess1.
