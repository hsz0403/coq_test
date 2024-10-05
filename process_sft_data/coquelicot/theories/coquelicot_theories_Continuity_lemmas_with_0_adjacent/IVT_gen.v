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

Lemma IVT_gen (f : R -> R) (a b y : R) : Ranalysis1.continuity f -> Rmin (f a) (f b) <= y <= Rmax (f a) (f b) -> { x : R | Rmin a b <= x <= Rmax a b /\ f x = y }.
Proof.
case: (Req_EM_T a b) => [ <- {b} | Hab].
rewrite /Rmin /Rmax ; case: Rle_dec (Rle_refl a) (Rle_refl (f a)) ; case: Rle_dec => // _ _ _ _ Cf Hy.
exists a ; split.
split ; by apply Rle_refl.
apply Rle_antisym ; by apply Hy.
wlog: a b Hab / (a < b) => [Hw | {Hab} Hab].
case: (Rle_lt_dec a b) => Hab'.
case: (Rle_lt_or_eq_dec _ _ Hab') => {Hab'} // Hab'.
by apply Hw.
rewrite (Rmin_comm (f a)) (Rmin_comm a) (Rmax_comm (f a)) (Rmax_comm a) ; apply Hw => //.
by apply Rlt_not_eq.
rewrite /(Rmin a) /(Rmax a) ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
wlog: f y / (f a <= f b) => [Hw |].
case: (Rle_lt_dec (f a) (f b)) => Hf' Hf Hy.
by apply Hw.
case: (Hw (fun y => - f y) (- y)).
by apply Ropp_le_contravar, Rlt_le.
by apply Ranalysis1.continuity_opp.
rewrite Rmin_opp_Rmax Rmax_opp_Rmin ; split ; apply Ropp_le_contravar, Hy.
move => x [Hx Hfx].
exists x ; intuition.
by rewrite -(Ropp_involutive y) -Hfx Ropp_involutive.
rewrite /Rmin /Rmax ; case: Rle_dec => // _ _.
wlog: y / (f a < y < f b) => [Hw Hf Hy | Hy Hf _].
case: Hy => Hay Hyb.
case: (Rle_lt_or_eq_dec _ _ Hay) => {Hay} [Hay | <- ].
case: (Rle_lt_or_eq_dec _ _ Hyb) => {Hyb} [Hyb | -> ].
apply Hw ; intuition.
exists b ; intuition.
exists a ; intuition.
case (IVT (fun x => f x - y) a b).
apply Ranalysis1.continuity_minus.
exact Hf.
apply continuity_const.
intros _ _ ; reflexivity.
exact Hab.
apply Rlt_minus_l ; rewrite Rplus_0_l ; apply Hy.
apply Rlt_minus_r ; rewrite Rplus_0_l ; apply Hy.
intros x [Hx Hfx].
apply Rminus_diag_uniq in Hfx.
by exists x.
