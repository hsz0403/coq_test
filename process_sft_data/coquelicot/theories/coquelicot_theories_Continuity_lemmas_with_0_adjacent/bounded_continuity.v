Require Import Reals.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Hierarchy.
Require Import Compactness Lim_seq.
Definition is_lim (f : R -> R) (x l : Rbar) := filterlim f (Rbar_locally' x) (Rbar_locally l).
Definition is_lim' (f : R -> R) (x l : Rbar) := match l with | Finite l => forall eps : posreal, Rbar_locally' x (fun y => Rabs (f y - l) < eps) | p_infty => forall M : R, Rbar_locally' x (fun y => M < f y) | m_infty => forall M : R, Rbar_locally' x (fun y => f y < M) end.
Definition ex_lim (f : R -> R) (x : Rbar) := exists l : Rbar, is_lim f x l.
Definition ex_finite_lim (f : R -> R) (x : Rbar) := exists l : R, is_lim f x l.
Definition Lim (f : R -> R) (x : Rbar) := Lim_seq (fun n => f (Rbar_loc_seq x n)).
Definition continuity_2d_pt f x y := forall eps : posreal, locally_2d (fun u v => Rabs (f u v - f x y) < eps) x y.
Section Continuity.
Context {T U : UniformSpace}.
Definition continuous_on (D : T -> Prop) (f : T -> U) := forall x, D x -> filterlim f (within D (locally x)) (locally (f x)).
Definition continuous (f : T -> U) (x : T) := filterlim f (locally x) (locally (f x)).
End Continuity.
Section Continuity_op.
Context {U : UniformSpace} {K : AbsRing} {V : NormedModule K}.
End Continuity_op.
Section UnifCont.
Context {V : UniformSpace}.
End UnifCont.
Section UnifCont_N.
Context {K : AbsRing} {V : NormedModule K}.
End UnifCont_N.

Lemma bounded_continuity {K : AbsRing} {V : NormedModule K} (f : R -> V) a b : (forall x, a <= x <= b -> filterlim f (locally x) (locally (f x))) -> {M : R | forall x, a <= x <= b -> norm (f x) < M}.
Proof.
destruct (Rle_dec b a) as [Hab|Hab].
exists (norm (f a) + 1).
intros x [Hax Hxb].
replace x with a.
rewrite -{1}(Rplus_0_r (norm (f a))).
apply Rplus_lt_compat_l, Rlt_0_1.
apply Rle_antisym with (1 := Hax).
now apply Rle_trans with b.
apply Rnot_le_lt in Hab.
wlog: f / (forall x, filterlim f (locally x) (locally (f x))) => [ Hw Cf | Cf _ ].
destruct (C0_extension_le f a b) as [g [Cg Hg]].
by apply Cf.
destruct (Hw g) as [M HM] => //.
exists M ; intros.
rewrite -Hg //.
by apply HM.
assert (forall x : R, locally x (fun y : R => Rabs (norm (f y) - norm (f x)) < 1)).
intro x.
generalize (proj1 (filterlim_locally_ball_norm _ _) (Cf x)) => {Cf} Cf.
apply: filter_imp (Cf (mkposreal _ Rlt_0_1)) => y Hy.
apply Rle_lt_trans with (2 := Hy).
apply norm_triangle_inv.
assert (forall x y : R, Rabs (norm (f y) - norm (f x)) < 1 \/ ~ Rabs (norm (f y) - norm (f x)) < 1).
intros x y ; edestruct Rlt_dec.
left ; by apply r.
by right.
set delta := (fun (x : R) => proj1_sig (locally_ex_dec x _ (H0 x) (H x))).
destruct (compactness_value_1d a b delta) as [d Hd].
destruct (nfloor_ex ((b - a) / d)) as [N HN].
apply Rdiv_le_0_compat.
now apply Rlt_le, Rlt_Rminus.
apply cond_pos.
set (M := (fix g n := match n with O => 0 | S n => Rmax (norm (f (a + INR n * d)) + 3) (g n) end) (S N)).
exists M => x Hx.
apply Rnot_le_lt => H2.
apply (Hd x Hx) ; case => t.
unfold delta.
case: locally_ex_dec => e /= He [Ht [Hxt Hde]].
contradict H2 ; apply Rlt_not_le.
move: (fun (y : R) Hy => He y (norm_compat1 _ _ _ Hy)) => {He} He.
apply He in Hxt.
rewrite -(Rabs_pos_eq (norm _) (norm_ge_0 _)).
replace (norm (f x)) with ((norm (f x) - norm (f t)) + norm (f t))%R by ring.
eapply Rle_lt_trans.
apply Rabs_triang.
eapply Rlt_trans.
apply Rplus_lt_compat_r.
by apply Hxt.
rewrite Rplus_comm ; apply Rlt_minus_r.
clear x Hx Hxt.
destruct (nfloor_ex ((t - a) / d)) as [n Hn].
apply Rdiv_le_0_compat.
apply Rplus_le_reg_r with a.
now ring_simplify.
apply cond_pos.
set (y := a + INR n * d).
replace (norm (f t)) with (-(norm (f y) - norm (f t)) + norm (f y))%R by ring.
eapply Rle_lt_trans.
apply Rabs_triang.
eapply Rlt_trans.
apply Rplus_lt_compat_r.
rewrite Rabs_Ropp.
apply He.
change (Rabs (a + INR n * d - t) < e).
replace (a + INR n * d - t) with (-((t - a) / d - INR n) * d).
rewrite Rabs_mult (Rabs_pos_eq d).
2: apply Rlt_le, cond_pos.
apply Rlt_le_trans with (1 * d).
apply Rmult_lt_compat_r with (1 := cond_pos d).
rewrite Rabs_Ropp Rabs_pos_eq.
apply Rplus_lt_reg_r with (INR n).
now rewrite /Rminus Rplus_assoc Rplus_opp_l Rplus_0_r (Rplus_comm 1).
apply Rplus_le_reg_r with (INR n).
now ring_simplify.
now rewrite Rmult_1_l.
field.
apply Rgt_not_eq, cond_pos.
apply Rplus_lt_reg_l with 1.
ring_simplify.
rewrite -> Rabs_pos_eq by apply norm_ge_0.
assert (n < S N)%nat.
apply INR_lt.
apply Rle_lt_trans with (1 := proj1 Hn).
rewrite S_INR.
apply Rle_lt_trans with (2 := proj2 HN).
apply Rmult_le_compat_r.
apply Rlt_le, Rinv_0_lt_compat, cond_pos.
now apply Rplus_le_compat_r.
unfold M, y.
clear -H1.
induction N.
apply Rlt_le_trans with (2 := Rmax_l _ _).
destruct n.
apply Rplus_lt_compat_l, Rplus_lt_compat_l.
now apply (IZR_lt 1 2).
now apply lt_S_n in H1.
destruct (le_lt_eq_dec _ _ (lt_n_Sm_le _ _ H1)) as [H2|H2].
apply Rlt_le_trans with (2 := Rmax_r _ _).
now apply IHN.
apply Rlt_le_trans with (2 := Rmax_l _ _).
rewrite H2.
apply Rplus_lt_compat_l, Rplus_lt_compat_l.
now apply (IZR_lt 1 2).
