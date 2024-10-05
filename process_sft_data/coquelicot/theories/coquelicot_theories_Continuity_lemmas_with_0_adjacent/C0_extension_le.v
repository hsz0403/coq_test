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

Lemma C0_extension_le {T : UniformSpace} (f : R -> T) (a b : R) : (forall c : R, a <= c <= b -> filterlim f (locally c) (locally (f c))) -> {g : R -> T | (forall c, filterlim g (locally c) (locally (g c))) /\ (forall c : R, a <= c <= b -> g c = f c)}.
Proof.
intros.
case: (Rlt_le_dec a b) => Hab.
destruct (C0_extension_lt f (f a) (f b) a b Hab) as [g [Cg [Gab [Ga Gb]]]].
intros c Hc.
apply H ; split ; apply Rlt_le, Hc.
eapply filterlim_filter_le_1, H.
by apply filter_le_within.
intuition.
eapply filterlim_filter_le_1, H.
by apply filter_le_within.
intuition.
exists g ; repeat split => //.
intros c [Hac Hcb].
case: Hac => [ Hac | <-] //.
case: Hcb => [ Hcb | ->] //.
apply Gab ; by split.
exists (fun _ => f a) ; split ; simpl.
move => c.
by apply filterlim_const.
intros c [Hac Hca].
case: Hab => Hab.
contradict Hab ; apply Rle_not_lt.
by apply Rle_trans with c.
rewrite Hab in Hca.
by apply f_equal, Rle_antisym.
