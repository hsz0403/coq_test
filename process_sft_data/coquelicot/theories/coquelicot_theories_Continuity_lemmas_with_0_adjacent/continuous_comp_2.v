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

Lemma continuous_comp_2 {U V W X : UniformSpace} (f : U -> V) (g : U -> W) (h : V -> W -> X) (x : U) : continuous f x -> continuous g x -> continuous (fun (x : V * W) => h (fst x) (snd x)) (f x,g x) -> continuous (fun x => h (f x) (g x)) x.
Proof.
intros Cf Cg Ch.
eapply filterlim_comp_2.
by apply Cf.
by apply Cg.
apply filterlim_locally => eps.
case: (proj1 (filterlim_locally _ _) Ch eps) => /= del Hdel.
rewrite {1}/ball /= /prod_ball /= in Hdel.
exists (fun y => ball (f x) (pos del) y) (fun y => ball (g x) (pos del) y).
apply locally_ball.
apply locally_ball.
move => y z /= Hy Hz.
apply (Hdel (y,z)).
by split.
