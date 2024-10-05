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

Lemma differentiable_continuity_pt : forall f x y, differentiable_pt f x y -> continuity_2d_pt f x y.
Proof.
intros f x y (l1&l2&Df) eps ; simpl in Df.
assert (0 < eps / 2).
apply Rdiv_lt_0_compat ; [apply eps|apply Rlt_R0_R2].
set (eps' := mkposreal _ H).
elim (Df eps') ; clear Df ; intros d0 Df.
assert (0 < Rmin (Rmin d0 1) (Rmin (eps/(4*Rmax (Rabs l1) 1)) (eps / (4* Rmax (Rabs l2) 1)))).
apply Rmin_pos ; apply Rmin_pos.
apply d0.
apply Rlt_0_1.
apply Rdiv_lt_0_compat.
apply eps.
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat ; apply Rlt_R0_R2.
apply (Rlt_le_trans _ _ _ Rlt_0_1 (RmaxLess2 _ _)).
apply Rdiv_lt_0_compat.
apply eps.
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat ; apply Rlt_R0_R2.
apply (Rlt_le_trans _ _ _ Rlt_0_1 (RmaxLess2 _ _)).
set (delta := mkposreal _ H0).
exists delta ; intros x' y' H1 H2.
rewrite (double_var eps).
apply (Rle_lt_trans _ (Rabs (f x' y' - f x y - (l1 * (x' - x) + l2 * (y' - y))) + Rabs (l1 * (x' - x) + l2 * (y' - y)))).
assert (Rabs (f x' y' - f x y) = Rabs ((f x' y' - f x y - (l1 * (x' - x) + l2 * (y' - y))) + (l1 * (x' - x) + l2 * (y' - y)))).
assert ((f x' y' - f x y) = (f x' y' - f x y - (l1 * (x' - x) + l2 * (y' - y)) + (l1 * (x' - x) + l2 * (y' - y)))).
ring.
rewrite <- H3 ; clear H3 ; reflexivity.
rewrite H3 ; clear H3 ; apply Rabs_triang.
apply Rplus_lt_le_compat.
apply (Rle_lt_trans _ (eps' * Rmax (Rabs (x' - x)) (Rabs (y' - y)))).
apply Df.
apply (Rlt_le_trans _ _ _ H1) ; unfold delta ; simpl ; apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_l _ _)).
apply (Rlt_le_trans _ _ _ H2) ; unfold delta ; simpl ; apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_l _ _)).
rewrite <- (Rmult_1_r (eps/2)) ; unfold eps' ; simpl.
apply Rmult_lt_compat_l.
apply H.
apply (Rlt_le_trans _ delta).
apply (Rmax_lub_lt _ _ _ H1 H2).
unfold delta ; simpl ; apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_r _ _)).
apply (Rle_trans _ (Rabs l1 * Rabs (x'-x) + Rabs l2 * Rabs (y'-y))).
repeat rewrite <- Rabs_mult.
apply Rabs_triang.
rewrite (double_var (eps/2)).
apply Rplus_le_compat.
apply (Rle_trans _ (Rabs l1 * delta)).
apply Rmult_le_compat_l.
apply Rabs_pos.
apply Rlt_le, H1.
apply (Rle_trans _ (Rabs l1 * (Rmin (eps / (4 * Rmax (Rabs l1) 1)) (eps / (4 * Rmax (Rabs l2) 1))))).
apply Rmult_le_compat_l ; unfold delta ; simpl ; [apply Rabs_pos| apply Rmin_r].
apply (Rle_trans _ (Rabs l1 * (eps / (4 * Rmax (Rabs l1) 1)))).
apply Rmult_le_compat_l ; [apply Rabs_pos | apply Rmin_l].
unfold Rmax ; destruct (Rle_dec (Rabs l1) 1).
rewrite <- (Rmult_1_l (eps/2/2)).
apply Rmult_le_compat.
apply Rabs_pos.
apply Rlt_le, Rdiv_lt_0_compat ; [apply eps | apply Rmult_lt_0_compat ; [apply Rmult_lt_0_compat ; apply Rlt_R0_R2|apply Rlt_0_1]].
apply r.
apply Req_le ; field.
apply Req_le ; field.
apply Rnot_le_lt in n.
apply sym_not_eq, Rlt_not_eq, (Rlt_trans _ _ _ Rlt_0_1 n).
apply (Rle_trans _ (Rabs l2 * delta)).
apply Rmult_le_compat_l.
apply Rabs_pos.
apply Rlt_le, H2.
apply (Rle_trans _ (Rabs l2 * (Rmin (eps / (4 * Rmax (Rabs l1) 1)) (eps / (4 * Rmax (Rabs l2) 1))))).
apply Rmult_le_compat_l ; unfold delta ; simpl ; [apply Rabs_pos| apply Rmin_r].
apply (Rle_trans _ (Rabs l2 * (eps / (4 * Rmax (Rabs l2) 1)))).
apply Rmult_le_compat_l ; [apply Rabs_pos | apply Rmin_r].
unfold Rmax ; destruct (Rle_dec (Rabs l2) 1).
rewrite <- (Rmult_1_l (eps/2/2)).
apply Rmult_le_compat.
apply Rabs_pos.
apply Rlt_le, Rdiv_lt_0_compat ; [apply eps | apply Rmult_lt_0_compat ; [apply Rmult_lt_0_compat ; apply Rlt_R0_R2|apply Rlt_0_1]].
apply r.
apply Req_le ; field.
apply Req_le ; field.
apply Rnot_le_lt in n.
apply sym_not_eq, Rlt_not_eq, (Rlt_trans _ _ _ Rlt_0_1 n).
