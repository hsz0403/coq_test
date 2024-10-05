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

Lemma Schwarz_aux : forall f x y (eps : posreal), ( forall u v, Rabs (u - x) < eps -> Rabs (v - y) < eps -> ex_derive (fun z : R => f z v) u /\ ex_derive (fun z : R => Derive (fun t => f t z) u) v ) -> forall h k, Rabs h < eps -> Rabs k < eps -> let phi k x := f x (y + k) - f x y in exists u, exists v, Rabs (u - x) <= Rabs h /\ Rabs (v - y) <= Rabs k /\ phi k (x + h) - phi k x = h * k * (Derive (fun z => Derive (fun t => f t z) u) v).
Proof.
intros f x y eps HD h k Hh Hk phi.
assert (Hx: x + h - x = h) by ring.
assert (Hy: y + k - y = k) by ring.
destruct (MVT_cor4 (phi k) (Derive (phi k)) x (Rabs h)) with (b := x + h) as (u&Hu1&Hu2).
intros c Hc.
apply Derive_correct.
apply: ex_derive_minus.
apply (HD c).
now apply Rle_lt_trans with (Rabs h).
now rewrite Hy.
apply (HD c).
now apply Rle_lt_trans with (Rabs h).
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
rewrite Hx.
apply Rle_refl.
rewrite Hx in Hu1, Hu2.
exists u.
destruct (MVT_cor4 (fun v => Derive (fun t => f t v) u) (Derive (fun v => Derive (fun t => f t v) u)) y (Rabs k)) with (b := y + k) as (v&Hv1&Hv2).
intros c Hc.
apply Derive_correct, HD.
now apply Rle_lt_trans with (Rabs h).
now apply Rle_lt_trans with (1 := Hc).
rewrite Hy.
apply Rle_refl.
rewrite Hy in Hv1, Hv2.
exists v.
refine (conj Hu2 (conj Hv2 _)).
rewrite Hu1 /phi Derive_minus.
rewrite Hv1.
ring.
apply (HD u).
now apply Rle_lt_trans with (Rabs h).
now rewrite Hy.
apply (HD u).
now apply Rle_lt_trans with (Rabs h).
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
