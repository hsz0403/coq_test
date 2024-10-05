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

Theorem Taylor_Lagrange_2d : forall f n x y, locally_2d (fun u v => ex_diff_n f (S n) u v) x y -> DL_regular_n f n x y.
Proof.
intros f n x y Df.
assert (exists D, locally_2d (fun u v => forall p, (p <= S n)%nat -> Rabs (partial_derive p (S n - p) f u v) <= D) x y).
assert (forall p, (p <= S n)%nat -> exists D, locally_2d (fun u v => Rabs (partial_derive p (S n - p) f u v) <= D) x y).
intros p Hp.
assert (continuity_2d_pt (partial_derive p (S n - p) f) x y).
apply locally_2d_singleton in Df.
refine (proj1 (_: ex_diff_n (partial_derive p (S n - p) f) 0 x y)).
replace O with (S n - (p + (S n - p)))%nat by rewrite le_plus_minus_r // minus_diag //.
cut (p + (S n - p) <= S n)%nat.
2: now rewrite le_plus_minus_r.
generalize (S n - p)%nat.
clear Hp.
revert f Df p.
generalize (S n).
clear n.
induction n.
intros f (H,_) [|p] [|q] H' ; try inversion H'.
done.
intros f H [|p] q H'.
destruct q as [|q].
exact H.
now apply ex_diff_n_deriv.
now apply ex_diff_n_deriv.
exists (Rabs (partial_derive p (S n - p) f x y) + 1).
specialize (H (mkposreal 1 Rlt_0_1)).
apply: locally_2d_impl H.
apply: locally_2d_forall => u v H.
replace (partial_derive p (S n - p) f u v) with (partial_derive p (S n - p) f x y + (partial_derive p (S n - p) f u v - partial_derive p (S n - p) f x y)) by ring.
apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat_l.
now apply Rlt_le.
clear -H.
generalize (le_refl (S n)).
generalize (S n) at 1 3.
intros p Hp.
induction p.
move: (H _ Hp) => {H} [D H].
exists D.
apply: locally_2d_impl H.
apply locally_2d_forall => u v H [|p] Hp' //.
inversion Hp'.
move: (IHp (le_S _ _ (le_S_n _ _ Hp))) => {IHp} [D1 H1].
move: (H _ Hp) => {H} [D2 H2].
exists (Rmax D1 D2).
move: (locally_2d_and _ _ x y H1 H2) => {H1 H2} H.
apply: locally_2d_impl H.
apply locally_2d_forall => u v H p' Hp'.
destruct (le_lt_or_eq _ _ Hp').
apply Rle_trans with (2 := Rmax_l _ _).
apply H.
now apply gt_S_le.
apply Rle_trans with (2 := Rmax_r _ _).
now rewrite H0.
destruct H as (D,H).
exists (/ INR (fact (S n)) * D * sum_f_R0 (fun i : nat => Rabs (C (S n) i)) (S n)).
move: (locally_2d_and _ _ _ _ Df H) => {Df H} HH.
apply locally_2d_1d_strong in HH.
apply: locally_2d_impl HH.
apply locally_2d_forall => u v HH.
set (g t := f (x + t * (u - x)) (y + t * (v - y))).
replace (f u v) with (g 1) by (rewrite /g 2!Rmult_1_l ; apply f_equal2 ; ring).
assert (forall k t, (k <= S n)%nat -> 0 <= t <= 1 -> is_derive_n g k t (sum_f_R0 (fun m => C k m * partial_derive m (k - m)%nat f (x+t*(u-x)) (y+t*(v-y)) * (u-x) ^ m * (v-y) ^ (k - m)%nat) k)).
intros k t Hk Ht.
specialize (HH t Ht).
revert HH.
pattern t ; apply locally_singleton.
induction k.
rewrite /C /partial_derive /g /=.
apply filter_forall.
intros ; field.
specialize (IHk (le_S _ _ (le_S_n _ _ Hk))).
rewrite /is_derive_n.
apply locally_locally in IHk.
move: IHk ; apply filter_imp => {t Ht} z IHk HH.
apply is_derive_ext_loc with (fun t => sum_n (fun m => C k m * partial_derive m (k - m) f (x + t * (u - x)) (y + t * (v - y)) * (u - x) ^ m * (v - y) ^ (k - m)) k).
apply locally_locally in HH.
generalize (filter_and _ _ HH IHk).
apply filter_imp => {z HH IHk} z [Hz HH].
specialize (HH Hz).
apply sym_eq.
rewrite sum_n_Reals.
now apply is_derive_n_unique.
replace (sum_f_R0 (fun m : nat => C (S k) m * partial_derive m (S k - m) f (x + z * (u - x)) (y + z * (v - y)) * (u - x) ^ m * (v - y) ^ (S k - m)) (S k)) with (sum_n (fun m : nat => C k m * (u - x) ^ m * (v - y) ^ (k - m) * ((u - x) * partial_derive (S m) (k - m) f (x + z * (u - x)) (y + z * (v - y)) + (v - y) * partial_derive m (S (k - m)) f (x + z * (u - x)) (y + z * (v - y)))) k).
apply: is_derive_sum_n => p Hp.
apply is_derive_ext with (fun u0 => C k p * (u - x) ^ p * (v - y) ^ (k - p) * partial_derive p (k - p) f (x + u0 * (u - x)) (y + u0 * (v - y))).
intros w.
simpl ; ring.
apply is_derive_Reals, derivable_pt_lim_scal.
rewrite (Rmult_comm (u - x)) (Rmult_comm (v - y)).
apply derivable_pt_lim_comp_2d.
apply locally_singleton in HH.
replace (partial_derive (S p) (k - p) f (x + z * (u - x)) (y + z * (v - y))) with (Derive (fun u : R => partial_derive p (k - p) f u (y + z * (v - y))) (x + z * (u - x))).
2: reflexivity.
replace (partial_derive p (S (k - p)) f (x + z * (u - x)) (y + z * (v - y))) with (Derive (fun v : R => partial_derive p (k - p) f (x + z * (u - x)) v) (y + z * (v - y))).
apply filterdiff_differentiable_pt_lim.
eapply filterdiff_ext_lin.
apply is_derive_filterdiff.
apply locally_2d_locally in HH.
apply filter_imp with (2:=HH).
clear - Hk Hp ; intros [u' v'] (H1,H2).
evar_last.
apply Derive_correct.
apply ex_diff_n_ex_deriv_inf_1 with (S n).
now rewrite - le_plus_minus.
exact H1.
simpl ; reflexivity.
apply locally_2d_singleton in HH.
apply Derive_correct.
apply ex_diff_n_ex_deriv_inf_2 with (S n).
now rewrite - le_plus_minus.
apply HH.
apply locally_2d_singleton in HH.
apply continuity_2d_pt_filterlim.
apply ex_diff_n_continuity_inf_1 with (S n).
now rewrite - le_plus_minus.
apply HH.
case => /= u' v'.
reflexivity.
apply Derive_partial_derive_aux2.
apply locally_2d_impl with (2:=HH).
apply locally_2d_forall.
intros u' v' (Y,_).
apply ex_diff_n_m with (2:=Y).
omega.
apply is_derive_Reals ; eapply filterdiff_ext_lin.
apply @filterdiff_plus_fct ; try apply locally_filter.
apply filterdiff_const.
apply @filterdiff_scal_l ; try apply locally_filter.
simpl => y0 ; apply plus_zero_l.
apply is_derive_Reals ; eapply filterdiff_ext_lin.
apply @filterdiff_plus_fct ; try apply locally_filter.
apply filterdiff_const.
apply @filterdiff_scal_l ; try apply locally_filter.
simpl => y0 ; apply plus_zero_l.
rewrite sum_n_Reals -(sum_eq (fun m => C k m * (u - x) ^ (S m) * (v - y) ^ (k - m) * partial_derive (S m) (k - m) f (x + z * (u - x)) (y + z * (v - y)) + C k m * (u - x) ^ m * (v - y) ^ (S (k - m)) * partial_derive m (S (k - m)) f (x + z * (u - x)) (y + z * (v - y)))).
2: intros ; simpl ; ring.
case k; clear Hk IHk k.
unfold C; simpl.
simpl ; field.
intros k.
apply sym_eq.
rewrite (decomp_sum _ (S (S k))).
2: apply lt_0_Sn.
rewrite - pred_Sn.
rewrite tech5.
rewrite (sum_eq _ (fun i : nat => (C (S k) i* partial_derive (S i) (S (S k) - S i) f (x + z * (u - x)) (y + z * (v - y)) * (u - x) ^ S i * (v - y) ^ (S (S k) - S i)) + (C (S k) (S i) * partial_derive (S i) (S (S k) - S i) f (x + z * (u - x)) (y + z * (v - y)) * (u - x) ^ S i * (v - y) ^ (S (S k) - S i)))).
rewrite sum_plus.
apply sym_eq.
rewrite sum_plus.
rewrite tech5.
rewrite (tech2 _ 0 (S k)).
2: apply lt_0_Sn.
replace (sum_f_R0 (fun l : nat => C (S k) l * (u - x) ^ l * (v - y) ^ S (S k - l) * partial_derive l (S (S k - l)) f (x + z * (u - x)) (y + z * (v - y))) 0) with (C (S (S k)) 0 * partial_derive 0 (S (S k) - 0) f (x + z * (u - x)) (y + z * (v - y)) * (u - x) ^ 0 * (v - y) ^ (S (S k) - 0)).
replace (C (S k) (S k) * (u - x) ^ S (S k) * (v - y) ^ (S k - S k) * partial_derive (S (S k)) (S k - S k) f (x + z * (u - x)) (y + z * (v - y))) with (C (S (S k)) (S (S k)) * partial_derive (S (S k)) (S (S k) - S (S k)) f (x + z * (u - x)) (y + z * (v - y)) * (u - x) ^ S (S k) * (v - y) ^ (S (S k) - S (S k))).
replace (sum_f_R0 (fun l : nat => C (S k) l * partial_derive (S l) (S (S k) - S l) f (x + z * (u - x)) (y + z * (v - y)) * (u - x) ^ S l * (v - y) ^ (S (S k) - S l)) k) with (sum_f_R0 (fun l : nat => C (S k) l * (u - x) ^ S l * (v - y) ^ (S k - l) * partial_derive (S l) (S k - l) f (x + z * (u - x)) (y + z * (v - y))) k).
replace (sum_f_R0 (fun l : nat => C (S k) (S l) * partial_derive (S l) (S (S k) - S l) f (x + z * (u - x)) (y + z * (v - y)) * (u - x) ^ S l * (v - y) ^ (S (S k) - S l)) k) with (sum_f_R0 (fun i : nat => C (S k) (1 + i) * (u - x) ^ (1 + i) * (v - y) ^ S (S k - (1 + i)) * partial_derive (1 + i) (S (S k - (1 + i))) f (x + z * (u - x)) (y + z * (v - y))) (S k - 1)).
simpl ; ring.
replace (S k - 1)%nat with k.
2: now apply plus_minus.
apply sum_eq.
intros i Hi.
replace (1+i)%nat with (S i) by reflexivity.
replace (S (S k - S i))%nat with (S (S k) - S i)%nat.
ring.
now (rewrite minus_Sn_m; try apply le_n_S).
apply sum_eq.
intros i Hi.
replace (S k - i)%nat with (S (S k) - S i)%nat by reflexivity.
ring.
rewrite 2!C_n_n 2!minus_diag.
ring.
simpl.
rewrite 2!C_n_0.
ring.
intros.
rewrite - (pascal (S k) i).
ring.
now apply le_lt_n_Sm.
destruct (Taylor_Lagrange g n 0 1 Rlt_0_1) as (t&Ht&Hg).
intros t Ht.
intros [|k] Hk.
easy.
eexists.
now apply (H (S k)).
rewrite Hg /DL_pol.
replace (1 - 0) with 1 by ring.
rewrite pow1 {1}/Rminus Rplus_assoc [_*_+_]Rplus_comm -Rplus_assoc -/(Rminus _ _).
assert (forall k t, (k <= S n)%nat -> 0 <= t <= 1 -> Derive_n g k t = (sum_f_R0 (fun m => C k m * partial_derive m (k - m)%nat f (x+t*(u-x)) (y+t*(v-y)) * (u-x) ^ m * (v-y) ^ (k - m)%nat) k)).
intros k t0 Hk Ht0.
apply is_derive_n_unique.
now apply H.
rewrite -minus_sum sum_eq_R0.
rewrite H0.
rewrite Rplus_0_l.
unfold differential.
rewrite Rabs_mult.
eapply Rle_trans.
apply Rmult_le_compat_l.
apply Rabs_pos.
eapply Rle_trans.
apply Rsum_abs.
apply sum_Rle.
intros n0 Hn0.
rewrite Rmult_assoc 3!Rabs_mult.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rabs_pos.
apply Rmult_le_compat.
apply Rabs_pos.
apply Rmult_le_pos; apply Rabs_pos.
specialize (HH t (conj (Rlt_le _ _ (proj1 Ht)) (Rlt_le _ _ (proj2 Ht)))).
apply locally_singleton in HH.
apply locally_2d_singleton in HH.
now apply HH.
rewrite - 2!RPow_abs.
instantiate (1:=(Rmax (Rabs (u - x)) (Rabs (v - y)) ^ S n)).
apply Rle_trans with ((Rmax (Rabs (u - x)) (Rabs (v - y)) ^ n0) * (Rmax (Rabs (u - x)) (Rabs (v - y)) ^ (S n - n0))).
apply Rmult_le_compat.
apply pow_le ; apply Rabs_pos.
apply pow_le ; apply Rabs_pos.
apply pow_incr.
split.
apply Rabs_pos.
apply Rmax_l.
apply pow_incr.
split.
apply Rabs_pos.
apply Rmax_r.
rewrite -pow_add.
rewrite -le_plus_minus.
apply Rle_refl.
exact Hn0.
rewrite - scal_sum.
rewrite /Rdiv Rmult_1_l Rabs_right .
right; ring.
apply Rle_ge; apply Rlt_le; apply Rinv_0_lt_compat.
apply INR_fact_lt_0.
apply le_refl.
split; apply Rlt_le, Ht.
intros n0 hn0.
rewrite H0.
rewrite 2!Rmult_0_l 2!Rplus_0_r pow1.
unfold differential, Rdiv; ring.
now apply le_S.
split; [apply Rle_refl | apply Rle_0_1].
