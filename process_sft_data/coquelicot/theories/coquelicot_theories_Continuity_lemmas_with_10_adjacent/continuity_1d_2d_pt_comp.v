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

Lemma uniform_continuity_2d_1d' : forall f a b c, (forall x, a <= x <= b -> continuity_2d_pt f c x) -> forall eps : posreal, exists delta : posreal, forall x y u v, a <= x <= b -> c - delta <= y <= c + delta -> a <= u <= b -> c - delta <= v <= c + delta -> Rabs (u - x) < delta -> Rabs (f v u - f y x) < eps.
Proof.
intros f a b c Cf eps.
assert (T:(forall x : R, a <= x <= b -> continuity_2d_pt (fun x0 y : R => f y x0) x c) ).
intros x Hx e.
destruct (Cf x Hx e) as (d,Hd).
exists d.
intros; now apply Hd.
destruct (uniform_continuity_2d_1d (fun x y => f y x) a b c T eps) as (d,Hd).
exists d; intros.
Admitted.

Lemma continuity_2d_pt_neq_0 : forall f x y, continuity_2d_pt f x y -> f x y <> 0 -> locally_2d (fun u v => f u v <> 0) x y.
Proof.
intros f x y Cf H.
apply continuity_2d_pt_filterlim in Cf.
apply locally_2d_locally.
apply (Cf (fun y => y <> 0)).
Admitted.

Lemma continuity_pt_id : forall x, continuity_pt (fun x => x) x.
Proof.
intros x.
apply continuity_pt_filterlim.
Admitted.

Lemma continuity_2d_pt_id1 : forall x y, continuity_2d_pt (fun u v => u) x y.
Proof.
Admitted.

Lemma continuity_2d_pt_id2 : forall x y, continuity_2d_pt (fun u v => v) x y.
Proof.
Admitted.

Lemma continuity_2d_pt_const : forall x y c, continuity_2d_pt (fun u v => c) x y.
Proof.
intros x y c eps; exists eps; rewrite Rminus_eq_0 Rabs_R0.
Admitted.

Lemma continuity_pt_ext_loc : forall f g x, locally x (fun x => f x = g x) -> continuity_pt f x -> continuity_pt g x.
Proof.
intros f g x Heq Cf.
apply continuity_pt_filterlim in Cf.
apply continuity_pt_filterlim.
rewrite -(locally_singleton _ _ Heq).
Admitted.

Lemma continuity_pt_ext : forall f g x, (forall x, f x = g x) -> continuity_pt f x -> continuity_pt g x.
Proof.
intros f g x Heq.
apply continuity_pt_ext_loc.
Admitted.

Lemma continuity_2d_pt_ext_loc : forall f g x y, locally_2d (fun u v => f u v = g u v) x y -> continuity_2d_pt f x y -> continuity_2d_pt g x y.
Proof.
intros f g x y Heq Cf.
apply locally_2d_locally in Heq.
apply continuity_2d_pt_filterlim in Cf.
apply continuity_2d_pt_filterlim.
rewrite -(locally_singleton _ _ Heq).
apply filterlim_ext_loc with (2 := Cf).
Admitted.

Lemma continuity_2d_pt_ext : forall f g x y, (forall x y, f x y = g x y) -> continuity_2d_pt f x y -> continuity_2d_pt g x y.
Proof.
intros f g x y Heq.
apply continuity_2d_pt_ext_loc.
apply locally_2d_locally.
apply filter_forall.
Admitted.

Lemma continuity_2d_pt_opp (f : R -> R -> R) (x y : R) : continuity_2d_pt f x y -> continuity_2d_pt (fun u v => - f u v) x y.
Proof.
apply continuity_1d_2d_pt_comp.
apply continuity_pt_opp.
Admitted.

Lemma continuity_2d_pt_plus (f g : R -> R -> R) (x y : R) : continuity_2d_pt f x y -> continuity_2d_pt g x y -> continuity_2d_pt (fun u v => f u v + g u v) x y.
Proof.
intros Cf Cg.
apply continuity_2d_pt_filterlim in Cf.
apply continuity_2d_pt_filterlim in Cg.
apply continuity_2d_pt_filterlim.
eapply filterlim_comp_2.
apply Cf.
apply Cg.
Admitted.

Lemma continuity_2d_pt_minus (f g : R -> R -> R) (x y : R) : continuity_2d_pt f x y -> continuity_2d_pt g x y -> continuity_2d_pt (fun u v => f u v - g u v) x y.
Proof.
move => Cf Cg.
apply continuity_2d_pt_plus.
exact: Cf.
Admitted.

Lemma continuity_2d_pt_inv (f : R -> R -> R) (x y : R) : continuity_2d_pt f x y -> f x y <> 0 -> continuity_2d_pt (fun u v => / f u v) x y.
Proof.
intros Cf Df.
apply continuity_2d_pt_filterlim in Cf.
apply continuity_2d_pt_filterlim.
apply filterlim_comp with (1 := Cf).
apply (filterlim_Rbar_inv (f x y)).
contradict Df.
Admitted.

Lemma continuity_2d_pt_mult (f g : R -> R -> R) (x y : R) : continuity_2d_pt f x y -> continuity_2d_pt g x y -> continuity_2d_pt (fun u v => f u v * g u v) x y.
Proof.
intros Cf Cg.
apply continuity_2d_pt_filterlim in Cf.
apply continuity_2d_pt_filterlim in Cg.
apply continuity_2d_pt_filterlim.
eapply filterlim_comp_2.
apply Cf.
apply Cg.
Admitted.

Lemma continuous_continuous_on : forall (D : T -> Prop) (f : T -> U) (x : T), locally x D -> continuous_on D f -> continuous f x.
Proof.
intros D f x Dx CD P Pfx.
assert (Dx' := locally_singleton _ _ Dx).
generalize (filter_and _ _ Dx (CD x Dx' P Pfx)).
unfold filtermap, within.
apply filter_imp.
intros t [H1 H2].
Admitted.

Lemma continuous_on_subset : forall (D E : T -> Prop) (f : T -> U), (forall x, E x -> D x) -> continuous_on D f -> continuous_on E f.
Proof.
intros D E f H CD x Ex P Pfx.
generalize (CD x (H x Ex) P Pfx).
unfold filtermap, within.
apply filter_imp.
intros t H' Et.
Admitted.

Lemma continuous_on_forall : forall (D : T -> Prop) (f : T -> U), (forall x, D x -> continuous f x) -> continuous_on D f.
Proof.
intros D f H x Dx P Pfx.
generalize (H x Dx P Pfx).
unfold filtermap, within.
Admitted.

Lemma continuous_ext_loc (f g : T -> U) (x : T) : locally x (fun y : T => g y = f y) -> continuous g x -> continuous f x.
Proof.
intros.
eapply filterlim_ext_loc.
by apply H.
Admitted.

Lemma continuous_ext : forall (f g : T -> U) (x : T), (forall x, f x = g x) -> continuous f x -> continuous g x.
Proof.
intros f g x H Cf.
apply filterlim_ext with (1 := H).
Admitted.

Lemma continuity_1d_2d_pt_comp : forall f g x y, continuity_pt f (g x y) -> continuity_2d_pt g x y -> continuity_2d_pt (fun x y => f (g x y)) x y.
Proof.
intros f g x y Cf Cg.
apply continuity_pt_filterlim in Cf.
apply continuity_2d_pt_filterlim in Cg.
apply continuity_2d_pt_filterlim.
apply: filterlim_comp Cg Cf.
