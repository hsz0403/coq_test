Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export Image.
Require Import ImageImplicit.
Require Export Finite_sets.
Require Export FunctionProperties.
Require Import DecidableDec.
Require Import ProofIrrelevance.
Require Import Description.
Set Asymmetric Patterns.
Inductive FiniteT : Type -> Prop := | empty_finite: FiniteT False | add_finite: forall T:Type, FiniteT T -> FiniteT (option T) | bij_finite: forall (X Y:Type) (f:X->Y), FiniteT X -> invertible f -> FiniteT Y.
Require Import FunctionalExtensionality.
Definition FiniteT_nat_cardinal (X:Type) (H:FiniteT X) : nat := proj1_sig (constructive_definite_description _ (FiniteT_has_nat_cardinal X H)).

Lemma finite_inj_surj: forall (X:Type) (f:X->X), FiniteT X -> injective f -> surjective f.
Proof.
intros.
induction H.
red.
destruct y.
remember (f None) as f0; destruct f0 as [a|].
assert (forall x:T, f (Some x) <> Some a).
unfold not; intros.
assert (Some x = None).
apply H0.
congruence.
discriminate H2.
pose (g := fun x:T => match f (Some x) with | Some y => y | None => a end).
assert (surjective g).
apply IHFiniteT.
red; intros.
remember (f (Some x)) as fx; destruct fx; remember (f (Some y)) as fy; destruct fy.
unfold g in H2.
rewrite <- Heqfx in H2; rewrite <- Heqfy in H2.
destruct H2; assert (f (Some x) = f (Some y)).
congruence.
apply H0 in H2.
injection H2; trivial.
unfold g in H2; rewrite <- Heqfx in H2; rewrite <- Heqfy in H2.
destruct H2.
contradiction (H1 x).
symmetry; assumption.
unfold g in H2; rewrite <- Heqfx in H2; rewrite <- Heqfy in H2.
destruct H2.
contradiction (H1 y).
symmetry; assumption.
assert (Some x = Some y).
apply H0.
congruence.
injection H3; trivial.
red; intro.
destruct y.
case (finite_eq_dec _ H t a).
exists None.
congruence.
destruct (H2 t).
exists (Some x).
unfold g in H3.
destruct (f (Some x)).
congruence.
contradiction n.
symmetry; assumption.
destruct (H2 a).
exists (Some x).
unfold g in H3.
remember (f (Some x)) as fx; destruct fx.
destruct H3.
contradiction (H1 x).
symmetry; assumption.
reflexivity.
assert (forall x:T, { y:T | f (Some x) = Some y }).
intros.
remember (f (Some x)) as fx; destruct fx.
exists t; reflexivity.
assert (Some x = None).
apply H0.
congruence.
discriminate H1.
pose (g := fun x:T => proj1_sig (X x)).
assert (surjective g).
apply IHFiniteT.
red; intros.
unfold g in H1.
repeat destruct X in H1.
simpl in H1.
assert (Some x = Some y).
apply H0.
congruence.
injection H2; trivial.
red; intro.
destruct y.
destruct (H1 t).
unfold g in H2; destruct X in H2.
simpl in H2.
exists (Some x).
congruence.
exists None.
symmetry; assumption.
destruct H1.
pose (f' := fun (x:X) => g (f (f0 x))).
assert (surjective f').
apply IHFiniteT.
red; intros.
unfold f' in H3.
assert (f (f0 x) = f (f0 y)).
congruence.
apply H0 in H4.
congruence.
red; intro.
destruct (H3 (g y)).
unfold f' in H4.
exists (f0 x).
Admitted.

Lemma finite_surj_inj: forall (X:Type) (f:X->X), FiniteT X -> surjective f -> injective f.
Proof.
intros.
assert (exists g:X->X, forall x:X, f (g x) = x).
apply finite_choice with (R:=fun (x y:X) => f y = x).
assumption.
assumption.
destruct H1 as [g].
assert (surjective g).
apply finite_inj_surj.
assumption.
red; intros.
rewrite <- H1 with x.
rewrite <- H1 with y.
rewrite H2; reflexivity.
red; intros.
destruct (H2 x).
destruct (H2 y).
rewrite <- H4 in H3.
rewrite <- H5 in H3.
repeat rewrite H1 in H3.
rewrite <- H4.
rewrite <- H5.
rewrite H3.
Admitted.

Lemma finite_sum: forall X Y:Type, FiniteT X -> FiniteT Y -> FiniteT (X+Y).
Proof.
intros.
induction H0.
apply bij_finite with _ inl.
assumption.
pose (g := fun (x:X+False) => match x with | inl x => x | inr f => False_rect X f end).
exists g.
intro; simpl.
reflexivity.
destruct y.
simpl.
reflexivity.
destruct f.
pose (g := fun (x:option (X+T)) => match x with | Some (inl x) => inl _ x | Some (inr t) => inr _ (Some t) | None => inr _ None end).
apply bij_finite with _ g.
apply add_finite.
assumption.
pose (ginv := fun (x:X + option T) => match x with | inl x => Some (inl _ x) | inr (Some t) => Some (inr _ t) | inr None => None end).
exists ginv.
destruct x as [[x|t]|]; trivial.
destruct y as [x|[t|]]; trivial.
pose (g := fun (x:X+X0) => match x with | inl x0 => inl _ x0 | inr x0 => inr _ (f x0) end).
destruct H1.
pose (ginv := fun (x:X+Y) => match x with | inl x0 => inl _ x0 | inr y0 => inr _ (g0 y0) end).
apply bij_finite with _ g.
assumption.
exists ginv.
destruct x as [x0|x0]; trivial.
simpl.
rewrite H1; reflexivity.
destruct y as [x|y0]; trivial.
simpl.
Admitted.

Lemma finite_prod: forall (X Y:Type), FiniteT X -> FiniteT Y -> FiniteT (X*Y).
Proof.
intros.
induction H0.
apply bij_finite with _ (False_rect _).
constructor.
exists (@snd X False).
destruct x.
destruct y.
destruct f.
pose (g := fun (x:X*T + X) => match x with | inl (pair x0 t) => pair x0 (Some t) | inr x0 => pair x0 None end).
pose (ginv := fun (x:X * option T) => match x with | (x0, Some t) => inl _ (x0, t) | (x0, None) => inr _ x0 end).
apply bij_finite with _ g.
apply finite_sum.
assumption.
assumption.
exists ginv.
destruct x as [[x0 t]|x0]; trivial.
destruct y as [x0 [t|]]; trivial.
pose (g := fun (y:X*X0) => match y with | pair x x0 => pair x (f x0) end).
destruct H1.
pose (ginv := fun (y:X*Y) => let (x,y0) := y in (x, g0 y0)).
apply bij_finite with _ g.
assumption.
exists ginv.
destruct x as [x x0]; unfold ginv, g; try rewrite H1; trivial.
Admitted.

Lemma finite_exp: forall X Y:Type, FiniteT X -> FiniteT Y -> FiniteT (X->Y).
Proof.
intros.
induction H.
pose (g := fun (x:True) (f:False) => False_rect Y f).
pose (ginv := fun (_:False->Y) => I).
apply bij_finite with _ g.
apply True_finite.
exists ginv.
destruct x as [].
trivial.
intro; extensionality f.
destruct f.
pose (g := fun (p:(T->Y)*Y) (x:option T) => let (f,y0) := p in match x with | Some x0 => f x0 | None => y0 end).
pose (ginv := fun (f:option T->Y) => (fun x:T => f (Some x), f None)).
apply bij_finite with _ g.
apply finite_prod.
assumption.
assumption.
exists ginv.
destruct x as [f y0]; try extensionality t; try destruct t as [t0|]; trivial.
intro.
extensionality t; destruct t as [t0|]; trivial.
destruct H1.
pose (g0 := fun (h:X->Y) (y:Y0) => h (g y)).
apply bij_finite with _ g0.
assumption.
pose (g0inv := fun (h:Y0->Y) (x:X) => h (f x)).
exists g0inv.
intro.
extensionality x0; unfold g0; unfold g0inv; simpl.
rewrite H1; reflexivity.
intro.
extensionality y0; unfold g0; unfold g0inv; simpl.
Admitted.

Lemma FiniteT_has_nat_cardinal: forall X:Type, FiniteT X -> exists! n:nat, cardinal _ (@Full_set X) n.
Proof.
intros.
apply -> unique_existence; split.
apply finite_cardinal.
pose (idX := fun x:X => x).
assert (Im Full_set idX = Full_set).
apply Extensionality_Ensembles.
red; split.
red; intros; constructor.
red; intros.
exists x.
constructor.
trivial.
rewrite <- H0.
apply FiniteT_img with (f:=fun x:X => x).
assumption.
intros.
case (finite_eq_dec X H y1 y2); tauto.
red; intros.
Admitted.

Lemma FiniteT_nat_cardinal_def: forall (X:Type) (H:FiniteT X), cardinal _ (@Full_set X) (FiniteT_nat_cardinal X H).
Proof.
intros; unfold FiniteT_nat_cardinal.
destruct constructive_definite_description.
Admitted.

Lemma FiniteT_nat_cardinal_cond: forall (X:Type) (H:FiniteT X) (n:nat), cardinal _ (@Full_set X) n -> FiniteT_nat_cardinal X H = n.
Proof.
intros.
pose proof (FiniteT_has_nat_cardinal X H).
destruct H1.
red in H1.
destruct H1.
transitivity x.
symmetry; apply H2.
apply FiniteT_nat_cardinal_def.
Admitted.

Lemma FiniteT_nat_cardinal_False: FiniteT_nat_cardinal False empty_finite = 0.
Proof.
apply FiniteT_nat_cardinal_cond.
assert (@Full_set False = @Empty_set False).
apply Extensionality_Ensembles; red; split; auto with sets.
red; intros.
destruct x.
rewrite H.
Admitted.

Lemma injection_preserves_cardinal: forall (X Y:Type) (f:X->Y) (n:nat) (S:Ensemble X), cardinal _ S n -> injective f -> cardinal _ (Im S f) n.
Proof.
intros.
induction H.
assert (Im Empty_set f = Empty_set).
apply Extensionality_Ensembles; split; auto with sets.
red; intros.
destruct H.
destruct H.
rewrite H; constructor.
assert (Im (Add A x) f = Add (Im A f) (f x)).
apply Extensionality_Ensembles; split.
red; intros.
destruct H2.
symmetry in H3; destruct H3.
destruct H2.
left; exists x0; auto with sets.
destruct H2; right; auto with sets.
red; intros.
destruct H2.
destruct H2.
exists x0.
left; auto with sets.
assumption.
destruct H2.
exists x; trivial; right; auto with sets.
rewrite H2.
constructor; trivial.
red; intro H3; inversion H3.
apply H0 in H5; destruct H5.
Admitted.

Lemma FiniteT_nat_cardinal_bijection: forall (X Y:Type) (H:FiniteT X) (g:X->Y) (Hinv:invertible g), FiniteT_nat_cardinal Y (bij_finite X Y g H Hinv) = FiniteT_nat_cardinal X H.
Proof.
intros.
apply FiniteT_nat_cardinal_cond.
apply invertible_impl_bijective in Hinv.
destruct Hinv as [g_inj g_surj].
assert (Full_set = Im Full_set g).
apply Extensionality_Ensembles; split; red; intros; try constructor.
destruct (g_surj x).
exists x0; try constructor; auto.
rewrite H0; apply injection_preserves_cardinal; trivial.
Admitted.

Lemma unique_FiniteT_nat_cardinal: exists! f: (forall (X:Type), FiniteT X -> nat), f False empty_finite = 0 /\ (forall (X:Type) (H:FiniteT X), f (option X) (add_finite X H) = S (f X H)) /\ (forall (X Y:Type) (H:FiniteT X) (g:X->Y) (Hinv:invertible g), f Y (bij_finite X Y g H Hinv) = f X H).
Proof.
match goal with |- @ex ?T (@unique ?T ?f) => apply -> (@unique_existence T f) end.
split.
exists FiniteT_nat_cardinal.
repeat split.
exact FiniteT_nat_cardinal_False.
exact FiniteT_nat_cardinal_option.
exact FiniteT_nat_cardinal_bijection.
red; intros f g Hf Hg.
destruct Hf as [HFalse_f [Hoption_f Hbijection_f]].
destruct Hg as [HFalse_g [Hoption_g Hbijection_g]].
extensionality X; extensionality HFinite.
generalize HFinite.
induction HFinite.
intro.
destruct (proof_irrelevance _ empty_finite HFinite).
congruence.
intro.
destruct (proof_irrelevance _ (add_finite T HFinite) HFinite0).
rewrite Hoption_f.
rewrite Hoption_g.
rewrite IHHFinite.
reflexivity.
intro.
destruct (proof_irrelevance _ (bij_finite _ _ f0 HFinite H) HFinite0).
Admitted.

Lemma FiniteT_nat_cardinal_option: forall (X:Type) (H:FiniteT X), FiniteT_nat_cardinal (option X) (add_finite X H) = S (FiniteT_nat_cardinal X H).
Proof.
intros.
apply FiniteT_nat_cardinal_cond.
assert (Full_set = Add (Im Full_set (@Some X)) None).
apply Extensionality_Ensembles; split.
red; intros.
destruct x.
left; exists x; constructor.
right; constructor.
red; intros; constructor.
rewrite H0.
constructor.
apply injection_preserves_cardinal.
apply FiniteT_nat_cardinal_def.
red; intros x1 x2 Heq; injection Heq; trivial.
red; intro.
inversion H1.
discriminate H3.
