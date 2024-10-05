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

Lemma continuity_2d_pt_ext : forall f g x y, (forall x y, f x y = g x y) -> continuity_2d_pt f x y -> continuity_2d_pt g x y.
Proof.
intros f g x y Heq.
apply continuity_2d_pt_ext_loc.
apply locally_2d_locally.
apply filter_forall.
Admitted.

Lemma continuity_1d_2d_pt_comp : forall f g x y, continuity_pt f (g x y) -> continuity_2d_pt g x y -> continuity_2d_pt (fun x y => f (g x y)) x y.
Proof.
intros f g x y Cf Cg.
apply continuity_pt_filterlim in Cf.
apply continuity_2d_pt_filterlim in Cg.
apply continuity_2d_pt_filterlim.
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

Lemma continuous_ext : forall (f g : T -> U) (x : T), (forall x, f x = g x) -> continuous f x -> continuous g x.
Proof.
intros f g x H Cf.
apply filterlim_ext with (1 := H).
Admitted.

Lemma continuous_on_ext : forall (D : T -> Prop) (f g : T -> U), (forall x, D x -> f x = g x) -> continuous_on D f -> continuous_on D g.
Proof.
intros D f g H Cf x Dx.
apply filterlim_within_ext with (1 := H).
rewrite <- H with (1 := Dx).
Admitted.

Lemma continuous_comp {U V W : UniformSpace} (f : U -> V) (g : V -> W) (x : U) : continuous f x -> continuous g (f x) -> continuous (fun x => g (f x)) x.
Proof.
Admitted.

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
Admitted.

Lemma is_lim_comp_continuous (f g : R -> R) (x : Rbar) (l : R) : is_lim f x l -> continuous g l -> is_lim (fun x => g (f x)) x (g l).
Proof.
intros Hf Hg.
apply filterlim_locally => eps.
destruct (proj1 (filterlim_locally _ _) Hg eps) as [e He] ; clear Hg.
eapply filter_imp.
intros y Hy.
apply He, Hy.
Admitted.

Lemma continuous_fst {U V : UniformSpace} (x : U) (y : V) : continuous (fst (B:=V)) (x, y).
Proof.
intros P [d Hd].
exists d => z [/= Hz1 Hz2].
Admitted.

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

Lemma continuous_ext_loc (f g : T -> U) (x : T) : locally x (fun y : T => g y = f y) -> continuous g x -> continuous f x.
Proof.
intros.
eapply filterlim_ext_loc.
by apply H.
by rewrite -(locally_singleton _ _ H).
