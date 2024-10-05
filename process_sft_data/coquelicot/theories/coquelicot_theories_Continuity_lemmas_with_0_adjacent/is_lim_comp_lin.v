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

Lemma is_lim_comp_lin (f : R -> R) (a b : R) (x l : Rbar) : is_lim f (Rbar_plus (Rbar_mult a x) b) l -> a <> 0 -> is_lim (fun y => f (a * y + b)) x l.
Proof.
move => Hf Ha.
apply is_lim_comp with (Rbar_plus (Rbar_mult a x) b).
by apply Hf.
eapply is_lim_plus.
apply is_lim_scal_l.
apply is_lim_id.
apply is_lim_const.
apply Rbar_plus_correct.
case: (Rbar_mult a x) => //.
case: x {Hf} => [x | | ] //=.
exists (mkposreal _ Rlt_0_1) => y _ Hy.
apply Rbar_finite_neq, Rminus_not_eq ; ring_simplify (a * y + b - (a * x + b)).
rewrite -Rmult_minus_distr_l.
apply Rmult_integral_contrapositive ; split.
by [].
by apply Rminus_eq_contra.
exists 0 => x Hx.
apply sym_not_eq in Ha.
case: Rle_dec => // H.
case: Rle_lt_or_eq_dec => //.
exists 0 => x Hx.
apply sym_not_eq in Ha.
case: Rle_dec => // H.
case: Rle_lt_or_eq_dec => //.
