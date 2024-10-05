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

Lemma filterdiff_differentiable_pt_lim (f : R -> R -> R) (x y lx ly : R) : filterdiff (fun u : R * R => f (fst u) (snd u)) (locally (x,y)) (fun u : R * R => fst u * lx + snd u * ly) <-> differentiable_pt_lim f x y lx ly.
Proof.
split => Df.
move => eps.
case: Df => _ Df.
assert (is_filter_lim (locally (x, y)) (x, y)) by now intro.
specialize (Df (x,y) H) => {H}.
apply locally_2d_locally.
assert (0 < eps / sqrt 2).
apply Rdiv_lt_0_compat.
by apply eps.
by apply Rlt_sqrt2_0.
move: (Df (mkposreal _ H)).
apply filter_imp => [[u v] /= Huv].
rewrite !(Rmult_comm _ (_-_)).
eapply Rle_trans.
apply Huv.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
by apply Rlt_le, eps.
rewrite Rmult_comm Rle_div_l.
rewrite Rmult_comm.
eapply Rle_trans.
apply norm_prod.
apply Rle_refl.
by apply Rlt_sqrt2_0.
split.
apply (is_linear_comp (fun u : R * R => (scal (fst u) lx,scal (snd u) ly)) (fun u : R * R => plus (fst u) (snd u))).
apply is_linear_prod.
apply (is_linear_comp (@fst _ _) (fun t : R => scal t lx)).
by apply is_linear_fst.
by apply @is_linear_scal_l.
apply (is_linear_comp (@snd _ _) (fun t : R => scal t ly)).
by apply is_linear_snd.
by apply @is_linear_scal_l.
by apply @is_linear_plus.
simpl => u Hu.
replace u with (x,y) by now apply is_filter_lim_locally_unique.
move => {u Hu} eps /=.
move: (proj1 (locally_2d_locally _ _ _) (Df eps)).
apply filter_imp => [[u v]] /= Huv.
rewrite !(Rmult_comm (_-_)).
eapply Rle_trans.
apply Huv.
apply Rmult_le_compat_l.
by apply Rlt_le, eps.
apply (norm_prod (u - x) (v - y)).
