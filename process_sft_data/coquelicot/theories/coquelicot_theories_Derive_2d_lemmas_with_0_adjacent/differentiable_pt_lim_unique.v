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

Lemma differentiable_pt_lim_unique (f : R -> R -> R) (x y : R) (lx ly : R) : differentiable_pt_lim f x y lx ly -> Derive (fun x => f x y) x = lx /\ Derive (fun y => f x y) y = ly.
Proof.
move => Df ; split ; apply is_derive_unique, is_derive_Reals => e He ; case: (Df (pos_div_2 (mkposreal e He))) => {Df} delta /= Df ; exists delta => h Hh0 Hh.
replace ((f (x + h) y - f x y) / h - lx) with ((f (x+h) y - f x y - (lx * ((x+h) - x) + ly * (y - y))) / h) by (by field).
rewrite Rabs_div.
apply Rlt_div_l.
by apply Rabs_pos_lt.
apply Rle_lt_trans with (e / 2 * Rmax (Rabs (x + h - x)) (Rabs (y - y))).
apply (Df (x+h) y).
by (ring_simplify (x + h - x)).
rewrite Rminus_eq_0 Rabs_R0 ; by apply delta.
ring_simplify (x + h - x).
rewrite Rmax_left.
apply Rmult_lt_compat_r.
by apply Rabs_pos_lt.
lra.
rewrite Rminus_eq_0 Rabs_R0 ; by apply Rabs_pos.
by [].
replace ((f x (y + h) - f x y) / h - ly) with ((f x (y + h) - f x y - (lx * (x - x) + ly * ((y + h) - y))) / h) by (by field).
rewrite Rabs_div.
apply Rlt_div_l.
by apply Rabs_pos_lt.
apply Rle_lt_trans with (e / 2 * Rmax (Rabs (x - x)) (Rabs (y + h - y))).
apply (Df x (y + h)).
rewrite Rminus_eq_0 Rabs_R0 ; by apply delta.
by (ring_simplify (y + h - y)).
ring_simplify (y + h - y).
rewrite Rmax_right.
apply Rmult_lt_compat_r.
by apply Rabs_pos_lt.
lra.
rewrite Rminus_eq_0 Rabs_R0 ; by apply Rabs_pos.
by [].
