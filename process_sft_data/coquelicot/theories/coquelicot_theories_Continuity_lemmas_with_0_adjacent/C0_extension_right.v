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

Lemma C0_extension_right {T : UniformSpace} (f : R -> T) lb (a b : R) : a < b -> (forall c : R, a < c < b -> filterlim f (locally c) (locally (f c))) -> (filterlim f (at_left b) (locally lb)) -> {g : R -> T | (forall c, a < c -> filterlim g (locally c) (locally (g c))) /\ (forall c : R, c < b -> g c = f c) /\ g b = lb}.
Proof.
intros Hab ; intros.
set g := fun x => match Rlt_dec x b with | left _ => f x | right _ => lb end.
assert (Gab : forall c : R, c < b -> g c = f c).
intros c Hcb.
unfold g.
by (case: Rlt_dec).
assert (Gb : forall c : R, b <= c -> g c = lb).
intros c Hbc.
unfold g.
case: Rlt_dec (Rle_not_lt _ _ Hbc) => //.
exists g ; split.
intros c Hac.
case: (Rlt_le_dec c b) ; (try case) => Hbc.
-
apply filterlim_ext_loc with f.
apply locally_interval with m_infty b => //= y _ Hyb.
by apply sym_eq, Gab.
rewrite Gab //.
apply H ; by split.
-
rewrite Gb.
2: by apply Rlt_le.
eapply filterlim_ext_loc.
2: by apply filterlim_const.
apply locally_interval with b p_infty => //= y Hby _.
apply sym_eq, Gb.
by apply Rlt_le.
-
rewrite -Hbc => {c Hbc Hac}.
rewrite Gb.
2: by apply Rle_refl.
apply filterlim_locally => eps /= {H}.
destruct (proj1 (filterlim_locally _ _) H0 eps) as [d Hd].
simpl in Hd.
exists d => x Hx.
case: (Rlt_le_dec x b) => Hxb.
rewrite Gab //.
by apply Hd.
rewrite Gb //.
by apply ball_center.
-
split.
by apply Gab.
apply Gb ; by apply Rle_refl.
