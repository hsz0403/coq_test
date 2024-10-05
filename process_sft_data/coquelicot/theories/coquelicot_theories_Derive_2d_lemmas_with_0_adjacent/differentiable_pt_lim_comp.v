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

Lemma differentiable_pt_lim_comp : forall f1 f2 f3 x y l1x l1y l2x l2y l3x l3y, differentiable_pt_lim f1 (f2 x y) (f3 x y) l1x l1y -> differentiable_pt_lim f2 x y l2x l2y -> differentiable_pt_lim f3 x y l3x l3y -> differentiable_pt_lim (fun u v => f1 (f2 u v) (f3 u v)) x y (l1x * l2x + l1y * l3x) (l1x * l2y + l1y * l3y).
Proof.
intros f1 f2 f3 x y l1_1 l1_2 l2_1 l2_2 l3_1 l3_2 Df1 Df2 Df3 eps ; simpl.
assert (Cf2 : continuity_2d_pt f2 x y).
apply differentiable_continuity_pt.
exists l2_1 ; exists l2_2 ; apply Df2.
assert (Cf3 : continuity_2d_pt f3 x y).
apply differentiable_continuity_pt.
exists l3_1 ; exists l3_2 ; apply Df3.
assert (He2 : 0 < eps / (4 * Rmax (Rabs l1_1) 1)).
apply Rdiv_lt_0_compat ; [apply eps | apply Rmult_lt_0_compat].
apply Rmult_lt_0_compat ; apply Rlt_R0_R2.
apply (Rlt_le_trans _ _ _ Rlt_0_1 (RmaxLess2 _ _)).
set (eps2 := mkposreal _ He2).
assert (He3 : 0 < eps / (4 * Rmax (Rabs l1_2) 1)).
apply Rdiv_lt_0_compat ; [apply eps | apply Rmult_lt_0_compat].
apply Rmult_lt_0_compat ; apply Rlt_R0_R2.
apply (Rlt_le_trans _ _ _ Rlt_0_1 (RmaxLess2 _ _)).
set (eps3 := mkposreal _ He3).
assert (He1 : 0 < eps / (2 * Rmax (eps2 + Rabs l2_1 + Rabs l2_2) (eps3 + Rabs l3_1 + Rabs l3_2))).
apply Rdiv_lt_0_compat ; [apply eps | apply Rmult_lt_0_compat].
apply Rlt_R0_R2.
apply (Rlt_le_trans _ (eps2 + Rabs l2_1 + Rabs l2_2)).
rewrite Rplus_assoc ; apply Rplus_lt_le_0_compat.
apply eps2.
apply Rplus_le_le_0_compat ; apply Rabs_pos.
apply RmaxLess1.
set (eps1 := mkposreal _ He1).
elim (Df1 eps1) ; clear Df1 ; intros d0 Df1.
elim (Cf2 d0) ; clear Cf2 ; intros d1 Cf2.
elim (Cf3 d0) ; clear Cf3 ; intros d'1 Cf3.
elim (Df2 eps2) ; clear Df2 ; intros d2 Df2.
elim (Df3 eps3) ; clear Df3 ; intros d3 Df3.
assert (Hd : 0 < Rmin (Rmin d1 d'1) (Rmin d2 d3)).
apply Rmin_pos ; apply Rmin_pos ; [apply d1 | apply d'1 | apply d2 | apply d3].
set (delta := mkposreal _ Hd).
exists delta ; intros x' y' ; intros.
apply (Rle_trans _ (Rabs (f1 (f2 x' y') (f3 x' y') - f1 (f2 x y) (f3 x y) - (l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y))) + Rabs (l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y) - ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) + (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y))))).
replace ((f1 (f2 x' y') (f3 x' y') - f1 (f2 x y) (f3 x y) - ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) + (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y)))) with ((f1 (f2 x' y') (f3 x' y') - f1 (f2 x y) (f3 x y) - (l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y))) + (l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y) - ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) + (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y)))) by ring.
apply Rabs_triang.
rewrite (double_var eps) (Rmult_plus_distr_r (eps/2)).
apply Rplus_le_compat.
apply (Rle_trans _ (eps1 * Rmax (Rabs (f2 x' y' - f2 x y)) (Rabs (f3 x' y' - f3 x y)))).
apply Df1.
apply Cf2.
apply (Rlt_le_trans _ _ _ H) ; simpl ; apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_l _ _)).
apply (Rlt_le_trans _ _ _ H0) ; simpl ; apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_l _ _)).
apply Cf3.
apply (Rlt_le_trans _ _ _ H) ; simpl ; apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_r _ _)).
apply (Rlt_le_trans _ _ _ H0) ; simpl ; apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_r _ _)).
apply (Rle_trans _ (eps1 * (Rmax (eps2 + Rabs l2_1 + Rabs l2_2) (eps3 + Rabs l3_1 + Rabs l3_2) * Rmax (Rabs (x'-x)) (Rabs (y'-y))))).
apply Rmult_le_compat_l.
apply Rlt_le, eps1.
rewrite Rmax_mult.
apply Rmax_le_compat.
rewrite Rplus_assoc Rmult_plus_distr_r.
apply (Rle_trans _ (Rabs (f2 x' y' - f2 x y - (l2_1 * (x' - x) + l2_2 * (y' - y))) + Rabs (l2_1 * (x' - x) + l2_2 * (y' - y)))).
assert (Rabs (f2 x' y' - f2 x y) = Rabs ((f2 x' y' - f2 x y - (l2_1 * (x' - x) + l2_2 * (y' - y))) + (l2_1 * (x' - x) + l2_2 * (y' - y)))).
assert ((f2 x' y' - f2 x y) = ((f2 x' y' - f2 x y - (l2_1 * (x' - x) + l2_2 * (y' - y))) + (l2_1 * (x' - x) + l2_2 * (y' - y)))).
ring.
rewrite <- H1 ; clear H1 ; reflexivity.
rewrite H1 ; clear H1 ; apply Rabs_triang.
apply Rplus_le_compat.
apply Df2.
apply (Rlt_le_trans _ _ _ H) ; simpl ; apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_l _ _)).
apply (Rlt_le_trans _ _ _ H0) ; simpl ; apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_l _ _)).
apply (Rle_trans _ (Rabs l2_1 * Rabs (x'-x) + Rabs l2_2 * Rabs (y'-y))).
repeat rewrite <- Rabs_mult ; apply Rabs_triang.
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat ; apply Rmult_le_compat_l.
apply Rabs_pos.
apply RmaxLess1.
apply Rabs_pos.
apply RmaxLess2.
rewrite Rplus_assoc Rmult_plus_distr_r.
apply (Rle_trans _ (Rabs (f3 x' y' - f3 x y - (l3_1 * (x' - x) + l3_2 * (y' - y))) + Rabs (l3_1 * (x' - x) + l3_2 * (y' - y)))).
assert (Rabs (f3 x' y' - f3 x y) = Rabs ((f3 x' y' - f3 x y - (l3_1 * (x' - x) + l3_2 * (y' - y))) + (l3_1 * (x' - x) + l3_2 * (y' - y)))).
assert ((f3 x' y' - f3 x y) = ((f3 x' y' - f3 x y - (l3_1 * (x' - x) + l3_2 * (y' - y))) + (l3_1 * (x' - x) + l3_2 * (y' - y)))).
ring.
rewrite <- H1 ; clear H1 ; reflexivity.
rewrite H1 ; clear H1 ; apply Rabs_triang.
apply Rplus_le_compat.
apply Df3.
apply (Rlt_le_trans _ _ _ H) ; simpl ; apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_r _ _)).
apply (Rlt_le_trans _ _ _ H0) ; simpl ; apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_r _ _)).
apply (Rle_trans _ (Rabs l3_1 * Rabs (x'-x) + Rabs l3_2 * Rabs (y'-y))).
repeat rewrite <- Rabs_mult ; apply Rabs_triang.
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat ; apply Rmult_le_compat_l.
apply Rabs_pos.
apply RmaxLess1.
apply Rabs_pos.
apply RmaxLess2.
apply (Rle_trans _ _ _ (Rabs_pos _) (RmaxLess1 _ _)).
simpl ; apply Req_le ; field.
apply sym_not_eq, Rlt_not_eq, (Rlt_le_trans _ (eps2 + Rabs l2_1 + Rabs l2_2)).
rewrite Rplus_assoc ; apply Rplus_lt_le_0_compat.
apply eps2.
apply Rplus_le_le_0_compat ; apply Rabs_pos.
apply RmaxLess1.
rewrite (double_var (eps/2)) (Rmult_plus_distr_r (eps/2/2)).
apply (Rle_trans _ (Rabs l1_1 * Rabs (f2 x' y' - f2 x y - (l2_1 * (x' - x) + l2_2 * (y' - y))) + Rabs l1_2 * Rabs (f3 x' y' - f3 x y - (l3_1 * (x' - x) + l3_2 * (y' - y))))).
repeat rewrite <- Rabs_mult.
assert ((l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y) - ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) + (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y))) = (l1_1 * (f2 x' y' - f2 x y - (l2_1 * (x' - x) + l2_2 * (y' - y)))) + (l1_2 * (f3 x' y' - f3 x y - (l3_1 * (x' - x) + l3_2 * (y' - y))))).
ring.
rewrite H1 ; clear H1 ; apply Rabs_triang.
apply Rplus_le_compat.
apply (Rle_trans _ (Rabs l1_1 * (eps2 * Rmax (Rabs (x' - x)) (Rabs (y' - y))))).
apply Rmult_le_compat_l.
apply Rabs_pos.
apply Df2.
apply (Rlt_le_trans _ _ _ H) ; simpl ; apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_l _ _)).
apply (Rlt_le_trans _ _ _ H0) ; simpl ; apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_l _ _)).
rewrite <- Rmult_assoc ; apply Rmult_le_compat_r.
apply (Rle_trans _ _ _ (Rabs_pos _) (RmaxLess1 _ _)).
unfold eps2, Rmax ; simpl ; destruct (Rle_dec (Rabs l1_1) 1).
rewrite <- (Rmult_1_l (eps/2/2)) ; apply Rmult_le_compat.
apply Rabs_pos.
rewrite Rmult_1_r ; apply Rlt_le, Rdiv_lt_0_compat ; [apply eps | apply Rmult_lt_0_compat ; apply Rlt_R0_R2].
apply r.
apply Req_le ; field.
apply Req_le ; field.
apply sym_not_eq, Rlt_not_eq, (Rlt_trans _ _ _ Rlt_0_1 (Rnot_le_lt _ _ n)).
apply (Rle_trans _ (Rabs l1_2 * (eps3 * Rmax (Rabs (x' - x)) (Rabs (y' - y))))).
apply Rmult_le_compat_l.
apply Rabs_pos.
apply Df3.
apply (Rlt_le_trans _ _ _ H) ; simpl ; apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_r _ _)).
apply (Rlt_le_trans _ _ _ H0) ; simpl ; apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_r _ _)).
rewrite <- Rmult_assoc ; apply Rmult_le_compat_r.
apply (Rle_trans _ _ _ (Rabs_pos _) (RmaxLess1 _ _)).
unfold eps3, Rmax ; simpl ; destruct (Rle_dec (Rabs l1_2) 1).
rewrite <- (Rmult_1_l (eps/2/2)) ; apply Rmult_le_compat.
apply Rabs_pos.
rewrite Rmult_1_r ; apply Rlt_le, Rdiv_lt_0_compat ; [apply eps | apply Rmult_lt_0_compat ; apply Rlt_R0_R2].
apply r.
apply Req_le ; field.
apply Req_le ; field.
apply sym_not_eq, Rlt_not_eq, (Rlt_trans _ _ _ Rlt_0_1 (Rnot_le_lt _ _ n)).
