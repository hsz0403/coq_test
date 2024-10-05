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

Lemma unifcont_normed_1d (f : R -> V) a b : (forall x, a <= x <= b -> continuous f x) -> forall eps : posreal, {delta : posreal | forall x y, a <= x <= b -> a <= y <= b -> ball x delta y -> ball_norm (f x) eps (f y)}.
Proof.
intros H eps.
assert (0 < eps / (@norm_factor _ V)).
apply Rdiv_lt_0_compat.
apply cond_pos.
exact norm_factor_gt_0.
destruct (unifcont_1d f a b H (mkposreal _ H0)) as [d Hd].
exists d => x y Hx Hy Hxy.
specialize (Hd x y Hx Hy Hxy).
apply Rnot_le_lt.
contradict Hd ; contradict Hd.
apply Rlt_not_le.
evar_last.
apply norm_compat2, Hd.
simpl ; field.
apply Rgt_not_eq, norm_factor_gt_0.
