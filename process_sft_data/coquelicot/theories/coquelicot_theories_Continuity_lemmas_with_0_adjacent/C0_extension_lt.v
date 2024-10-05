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

Lemma C0_extension_lt {T : UniformSpace} (f : R -> T) la lb (a b : R) : a < b -> (forall c : R, a < c < b -> filterlim f (locally c) (locally (f c))) -> (filterlim f (at_right a) (locally la)) -> (filterlim f (at_left b) (locally lb)) -> {g : R -> T | (forall c, filterlim g (locally c) (locally (g c))) /\ (forall c : R, a < c < b -> g c = f c) /\ g a = la /\ g b = lb}.
Proof.
intros.
destruct (C0_extension_left f la a b) as [g [Cg [Gab Ga]]] => //.
destruct (C0_extension_right g lb a b) as [h [Ch [Hab Hb]]] => //.
intros.
apply Cg, H3.
eapply filterlim_ext_loc.
2: by apply H2.
apply Rminus_lt_0 in H.
exists (mkposreal _ H) => y /= Hy Hy'.
apply sym_eq, Gab.
apply Ropp_lt_cancel, (Rplus_lt_reg_l b).
eapply Rle_lt_trans, Hy.
rewrite -abs_opp opp_minus.
apply Rle_abs.
exists h ; repeat split.
intros c.
case: (Rlt_le_dec a c) => Hac.
by apply Ch.
rewrite Hab.
eapply filterlim_ext_loc.
2: apply Cg.
apply locally_interval with m_infty b => //.
by eapply Rle_lt_trans, H.
intros y _ Hy ; by apply sym_eq, Hab.
by eapply Rle_lt_trans, H.
by eapply Rle_lt_trans, H.
intros c [Hac Hcb].
rewrite Hab => //.
by apply Gab.
by rewrite Hab.
by [].
