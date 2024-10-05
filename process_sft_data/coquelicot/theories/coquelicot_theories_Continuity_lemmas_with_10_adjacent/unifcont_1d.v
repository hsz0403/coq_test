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

Lemma continuous_snd {U V : UniformSpace} (x : U) (y : V) : continuous (snd (B:=V)) (x, y).
Proof.
intros P [d Hd].
exists d => z [/= Hz1 Hz2].
Admitted.

Lemma continuous_const {U V : UniformSpace} (c : V) (x : U) : continuous (fun _ => c) x.
Proof.
Admitted.

Lemma continuous_id {U : UniformSpace} (x : U) : continuous (fun y => y) x.
Proof.
Admitted.

Lemma continuous_opp (f : U -> V) (x : U) : continuous f x -> continuous (fun x : U => opp (f x)) x.
Proof.
intros.
eapply filterlim_comp.
by apply H.
Admitted.

Lemma continuous_plus (f g : U -> V) (x : U) : continuous f x -> continuous g x -> continuous (fun x : U => plus (f x) (g x)) x.
Proof.
intros.
eapply filterlim_comp_2.
by apply H.
by apply H0.
Admitted.

Lemma continuous_minus (f g : U -> V) (x : U) : continuous f x -> continuous g x -> continuous (fun x : U => minus (f x) (g x)) x.
Proof.
intros.
apply continuous_plus.
apply H.
Admitted.

Lemma continuous_scal (k : U -> K) (f : U -> V) (x : U) : continuous k x -> continuous f x -> continuous (fun y => scal (k y) (f y)) x.
Proof.
intros.
Admitted.

Lemma continuous_scal_r (k : K) (f : U -> V) (x : U) : continuous f x -> continuous (fun y => scal k (f y)) x.
Proof.
intros.
Admitted.

Lemma continuous_scal_l (f : U -> K) (k : V) (x : U) : continuous f x -> continuous (fun y => scal (f y) k) x.
Proof.
intros.
apply (continuous_comp f (fun y => scal y k)) => //.
Admitted.

Lemma continuous_mult {U : UniformSpace} {K : AbsRing} (f g : U -> K) (x : U) : continuous f x -> continuous g x -> continuous (fun y => mult (f y) (g y)) x.
Proof.
intros.
Admitted.

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
Admitted.

Lemma unifcont_1d (f : R -> V) a b : (forall x, a <= x <= b -> continuous f x) -> forall eps : posreal, {delta : posreal | forall x y, a <= x <= b -> a <= y <= b -> ball x delta y -> ~~ ball (f x) eps (f y)}.
Proof.
intros Cf eps.
wlog: f Cf / (forall z : R, continuous f z) => [ Hw | {Cf} Cf ].
destruct (C0_extension_le f a b) as [g [Cg Hg]].
by apply Cf.
destruct (Hw g) as [d Hd].
intros x Hx ; apply Cg.
apply Cg.
exists d => x y Hx Hy Hxy.
rewrite -!Hg //.
by apply Hd.
assert (forall (x : R), {delta : posreal | forall y : R, ball x delta y -> ~~ ball (f x) (pos_div_2 eps) (f y)}).
move: (pos_div_2 eps) => {eps} eps x.
assert (Rbar_lt 0 (Lub.Lub_Rbar (fun d => forall y : R, ball x d y -> ball (f x) eps (f y)))).
case: (Lub.Lub_Rbar_correct (fun d => forall y : R, ball x d y -> ball (f x) eps (f y))).
move: (Lub.Lub_Rbar _) => l H1 H2.
case: (proj1 (filterlim_locally _ _) (Cf x) eps) => d Hd.
eapply Rbar_lt_le_trans, H1.
by apply d.
by apply Hd.
assert (0 < Rbar_min 1 (Lub.Lub_Rbar (fun d => forall y : R, ball x d y -> ball (f x) eps (f y)))).
move: H ; case: (Lub.Lub_Rbar (fun d => forall y : R, ball x d y -> ball (f x) eps (f y))) => [l | | ] //= H0.
apply Rmin_case => //.
by apply Rlt_0_1.
by apply Rlt_0_1.
set d := mkposreal _ H0.
exists d.
unfold d ; clear d ; simpl.
case: (Lub.Lub_Rbar_correct (fun d => forall y : R, ball x d y -> ball (f x) eps (f y))).
move: (Lub.Lub_Rbar (fun d => forall y : R, ball x d y -> ball (f x) eps (f y))) H => {H0} l H0 H1 H2 y Hy.
contradict Hy.
apply Rle_not_lt.
apply (Rbar_le_trans (Finite _) l (Finite _)).
case: (l) H0 => [r | | ] //= H0.
apply Rmin_r.
apply H2 => d /= Hd.
apply Rnot_lt_le ; contradict Hy.
by apply Hd.
destruct (compactness_value_1d a b (fun x => pos_div_2 (proj1_sig (H x)))) as [d Hd].
exists d => x y Hx Hy Hxy Hf.
apply (Hd x Hx).
case => {Hd} t [Ht].
case: H => /= delta Hdelta [Htx Hdt].
apply (Hdelta x).
eapply ball_le, Htx.
rewrite {2}(double_var delta).
apply Rminus_le_0 ; ring_simplify.
apply Rlt_le, is_pos_div_2.
intro Hftx.
apply (Hdelta y).
rewrite (double_var delta).
apply ball_triangle with x.
apply Htx.
by eapply ball_le, Hxy.
contradict Hf.
rewrite (double_var eps).
eapply ball_triangle, Hf.
by apply ball_sym.
