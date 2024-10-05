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
Admitted.

Lemma differentiable_pt_lim_ext : forall f1 f2 x y lx ly, locally_2d (fun u v => f1 u v = f2 u v) x y -> differentiable_pt_lim f1 x y lx ly -> differentiable_pt_lim f2 x y lx ly.
Proof.
intros f1 f2 x y lx ly H H1 eps.
apply: locally_2d_impl (H1 eps) => {H1}.
rewrite (locally_2d_singleton _ _ _ H).
apply: locally_2d_impl H.
apply locally_2d_forall.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Lemma derivable_pt_lim_comp_2d : forall f1 f2 f3 x l1x l1y l2 l3, differentiable_pt_lim f1 (f2 x) (f3 x) l1x l1y -> derivable_pt_lim f2 x l2 -> derivable_pt_lim f3 x l3 -> derivable_pt_lim (fun t => f1 (f2 t) (f3 t)) x (l1x * l2 + l1y * l3).
Proof.
intros.
apply (differentiable_pt_lim_proj1_1 _ x 0 (l1x * l2 + l1y * l3)).
pattern 0 at 2 ; replace 0 with (l1x * 0 + l1y * 0) by ring.
apply differentiable_pt_lim_comp.
apply H.
apply: differentiable_pt_lim_proj1_0 H0.
Admitted.

Lemma partial_derive_ext_loc : forall f g p q x y, locally_2d (fun u v => f u v = g u v) x y -> partial_derive p q f x y = partial_derive p q g x y.
Proof.
intros f g p q x y H.
unfold partial_derive.
apply Derive_n_ext_loc.
destruct H as (e,He).
exists e.
intros u Hu.
apply Derive_n_ext_loc.
exists e.
intros v Hv.
Admitted.

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
Admitted.

Lemma Schwarz : forall (f : R -> R -> R) x y, locally_2d (fun u v => ex_derive (fun z : R => f z v) u /\ ex_derive (fun z : R => f u z) v /\ ex_derive (fun z : R => Derive (fun t => f z t) v) u /\ ex_derive (fun z : R => Derive (fun t => f t z) u) v) x y -> continuity_2d_pt (fun u v => Derive (fun z => Derive (fun t => f z t) v) u) x y -> continuity_2d_pt (fun u v => Derive (fun z => Derive (fun t => f t z) u) v) x y -> Derive (fun z => Derive (fun t => f z t) y) x = Derive (fun z => Derive (fun t => f t z) x) y.
Proof.
intros f x y (eps, HD) HC2 HC1.
refine ((fun H1 => _) (Schwarz_aux f x y eps _)).
2: intros u v Hu Hv ; split ; now apply (HD u v).
refine ((fun H2 => _ )(Schwarz_aux (fun x y => f y x) y x eps _)).
2: intros u v Hu Hv ; split ; now apply (HD v u).
simpl in H1, H2.
apply Req_lt_aux.
intros e.
destruct (HC1 (pos_div_2 e)) as (d1,Hc1).
destruct (HC2 (pos_div_2 e)) as (d2,Hc2).
set (d := Rmin (Rmin (pos_div_2 d1) (pos_div_2 d2)) (pos_div_2 eps)).
assert (Hd: d > 0).
apply Rmin_glb_lt.
apply Rmin_stable_in_posreal.
apply cond_pos.
assert (K: Rabs d < eps).
rewrite Rabs_right.
apply Rle_lt_trans with (1 := Rmin_r _ _).
apply (Rlt_eps2_eps eps).
apply cond_pos.
now apply Rgt_ge.
specialize (H1 d d K K).
specialize (H2 d d K K).
destruct H1 as (u1&v1&Hu1&Hv1&H1).
destruct H2 as (v2&u2&Hv2&Hu2&H2).
clear K.
rewrite (Rabs_right d (Rgt_ge _ _ Hd)) in Hu1 Hv1 Hu2 Hv2.
assert (K: forall a b, Rabs (a - b) <= d -> Rabs (a - b) < d1).
intros a b H.
apply Rle_lt_trans with (1 := H).
apply Rle_lt_trans with (1 := Rmin_l _ _).
apply Rle_lt_trans with (1 := Rmin_l _ _).
apply (Rlt_eps2_eps d1).
apply cond_pos.
specialize (Hc1 u1 v1 (K _ _ Hu1) (K _ _ Hv1)).
clear K.
assert (K: forall a b, Rabs (a - b) <= d -> Rabs (a - b) < d2).
intros a b H.
apply Rle_lt_trans with (1 := H).
apply Rle_lt_trans with (1 := Rmin_l _ _).
apply Rle_lt_trans with (1 := Rmin_r _ _).
apply (Rlt_eps2_eps d2).
apply cond_pos.
specialize (Hc2 u2 v2 (K _ _ Hu2) (K _ _ Hv2)).
clear -Hd H1 H2 Hc1 Hc2.
assert (H: forall a b c, b - c = -(a - b) + (a - c)) by (intros ; ring).
rewrite (H (Derive (fun z : R => Derive (fun t : R => f z t) v2) u2)).
clear H.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite Rabs_Ropp (double_var e).
apply Rplus_lt_compat.
exact Hc2.
replace (Derive (fun z : R => Derive (fun t : R => f z t) v2) u2) with (Derive (fun z : R => Derive (fun t : R => f t z) u1) v1).
exact Hc1.
apply Rmult_eq_reg_l with (d * d).
rewrite -H1 -H2.
ring.
apply Rgt_not_eq.
Admitted.

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
Admitted.

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
Admitted.

Lemma ex_diff_n_m : forall n m, (m <= n)%nat -> forall f x y, ex_diff_n f n x y -> ex_diff_n f m x y.
Proof.
assert (forall n f x y, ex_diff_n f (S n) x y -> ex_diff_n f n x y).
induction n.
simpl.
intros f x y H; split; try apply H.
intros f x y H.
repeat (split; try apply H).
apply IHn.
apply H.
apply IHn.
apply H.
intros n m H1 f x y Hn.
induction n.
replace m with 0%nat.
exact Hn.
now apply le_n_0_eq.
case (le_lt_or_eq _ _ H1).
intros H2; apply IHn.
now apply gt_S_le.
apply (H _ _ _ _ Hn).
Admitted.

Lemma ex_diff_n_deriv_aux1: forall f n x y, ex_diff_n f (S n) x y -> ex_diff_n (fun u v => Derive (fun z => f z v) u) n x y.
Proof.
intros f n x y.
case n.
simpl.
intros H; split; apply H.
clear n;intros n H.
simpl in H.
Admitted.

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
