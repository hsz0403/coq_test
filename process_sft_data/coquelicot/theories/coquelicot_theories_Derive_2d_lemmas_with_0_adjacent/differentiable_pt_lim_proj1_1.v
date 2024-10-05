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

Lemma differentiable_pt_lim_proj1_1 (f : R -> R) (x y l : R) : differentiable_pt_lim (fun u v => f u) x y l 0 -> derivable_pt_lim f x l.
Proof.
intros Df.
apply is_derive_Reals ; split => [ | z Hz eps].
by apply @is_linear_scal_l.
rewrite -(is_filter_lim_locally_unique _ _ Hz) => {z Hz}.
elim (Df eps) ; clear Df ; intros delta Df.
exists delta ; simpl in Df ; simpl ; intros.
rewrite /minus /plus /opp /scal /= /mult /=.
replace (f y0 + - f x + - ((y0 + - x) * l)) with (f y0 - f x - (l * (y0 - x) + 0 * (y - y))) by ring.
assert (Rabs (y0 - x) = Rmax (Rabs (y0 - x)) (Rabs (y-y))).
rewrite Rmax_comm ; apply sym_equal, Rmax_right.
rewrite Rminus_eq_0 Rabs_R0 ; apply Rabs_pos.
rewrite /norm /= /abs /=.
rewrite H0 ; clear H0.
apply (Df _ _ H).
rewrite Rminus_eq_0 Rabs_R0 ; apply delta.
