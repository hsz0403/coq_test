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

Lemma finite_dec_exists: forall (X:Type) (P:X->Prop), FiniteT X -> (forall x:X, {P x} + {~ P x}) -> { exists x:X, P x } + { forall x:X, ~ P x }.
Proof.
intros.
apply exclusive_dec.
red; intro.
destruct H0.
destruct H0.
contradiction (H1 x).
revert P X0.
induction H.
right.
destruct x.
intros.
case (IHFiniteT (fun x:T => P (Some x)) (fun x:T => X0 (Some x))).
left.
destruct H0.
exists (Some x).
assumption.
intro.
case (X0 None).
left.
exists None.
assumption.
right.
destruct x.
apply H0.
assumption.
destruct H0.
intros.
case (IHFiniteT (fun x:X => P (f x)) (fun x:X => X0 (f x))).
left.
destruct H2.
exists (f x).
assumption.
right.
intro.
rewrite <- H1 with x.
Admitted.

Lemma finite_dec_forall: forall (X:Type) (P:X->Prop), FiniteT X -> (forall x:X, { P x } + { ~ P x }) -> { forall x:X, P x } + { exists x:X, ~ P x }.
Proof.
intros.
apply exclusive_dec.
intuition.
destruct H2.
contradiction (H1 x).
revert P X0.
induction H.
left.
destruct x.
intros.
case (IHFiniteT (fun x:T => P (Some x)) (fun x:T => X0 (Some x))).
intro.
case (X0 None).
left.
destruct x.
apply H0.
assumption.
right.
exists None.
assumption.
right.
destruct H0.
exists (Some x).
assumption.
intros.
destruct H0.
case (IHFiniteT (fun x:X => P (f x)) (fun x:X => X0 (f x))).
left.
intro y.
rewrite <- H1.
apply H2.
right.
destruct H2.
exists (f x).
Admitted.

Lemma finite_eq_dec: forall X:Type, FiniteT X -> forall x y:X, {x=y} + {x<>y}.
Proof.
intros.
apply decidable_dec.
induction H.
destruct x.
decide equality.
destruct H0.
case (IHFiniteT (g x) (g y)).
left.
rewrite <- H1.
rewrite <- H1 with x.
rewrite H2.
reflexivity.
right.
contradict H2.
rewrite H2.
Admitted.

Lemma finite_dep_choice: forall (A:Type) (B:forall x:A, Type) (R:forall x:A, B x->Prop), FiniteT A -> (forall x:A, exists y:B x, R x y) -> exists f:(forall x:A, B x), forall x:A, R x (f x).
Proof.
intros.
revert B R H0.
induction H.
intros.
exists (fun x:False => False_rect (B x) x).
destruct x.
intros.
pose proof (IHFiniteT (fun x:T => B (Some x)) (fun x:T => R (Some x)) (fun x:T => H0 (Some x))).
destruct H1.
pose proof (H0 None).
destruct H2.
exists (fun y:option T => match y return (B y) with | Some y0 => x y0 | None => x0 end).
destruct x1.
apply H1.
assumption.
intros.
destruct H0.
pose proof (IHFiniteT (fun x:X => B (f x)) (fun x:X => R (f x)) (fun x:X => H1 (f x))).
destruct H3.
pose (f0 := fun y:Y => x (g y)).
pose (conv := fun (y:Y) (a:B (f (g y))) => eq_rect (f (g y)) B a y (H2 y)).
exists (fun y:Y => conv y (x (g y))).
intro.
unfold conv; simpl.
generalize (H2 x0).
pattern x0 at 2 3 6.
rewrite <- H2.
intro.
rewrite <- eq_rect_eq.
Admitted.

Lemma finite_choice : forall (A B:Type) (R:A->B->Prop), FiniteT A -> (forall x:A, exists y:B, R x y) -> exists f:A->B, forall x:A, R x (f x).
Proof.
intros.
apply finite_dep_choice.
assumption.
Admitted.

Lemma Finite_ens_type: forall {X:Type} (S:Ensemble X), Finite _ S -> FiniteT { x:X | In S x }.
Proof.
intros.
induction H.
apply bij_finite with False (False_rect _).
constructor.
assert (g:{x:X | In Empty_set x}->False).
intro.
destruct X0.
destruct i.
exists g.
destruct x.
destruct y.
destruct g.
assert (Included A (Add A x)).
auto with sets.
assert (In (Add A x) x).
auto with sets.
pose (g := fun (y: option {x:X | In A x}) => match y return {x0:X | In (Add A x) x0} with | Some (exist y0 i) => exist (fun x2:X => In (Add A x) x2) y0 (H1 y0 i) | None => exist (fun x2:X => In (Add A x) x2) x H2 end).
apply bij_finite with _ g.
apply add_finite.
assumption.
assert (h:forall x0:X, In (Add A x) x0 -> { In A x0 } + { x0 = x }).
intros; apply exclusive_dec.
intuition.
destruct H6; auto.
destruct H3.
left; assumption.
right; destruct H3; reflexivity.
pose (ginv := fun s:{x0:X | In (Add A x) x0} => match s return option {x:X | In A x} with | exist x0 i => match (h x0 i) with | left iA => Some (exist _ x0 iA) | right _ => None end end).
exists ginv.
intro; destruct x0.
destruct s.
simpl.
remember (h x0 (H1 x0 i)) as sum; destruct sum.
destruct (proof_irrelevance _ i i0).
reflexivity.
contradiction H0.
rewrite <- e; assumption.
simpl.
remember (h x H2) as sum; destruct sum.
contradiction H0.
reflexivity.
intro.
unfold ginv.
destruct y.
destruct (h x0 i).
simpl.
generalize (H1 x0 i0); intro.
destruct (proof_irrelevance _ i i1).
reflexivity.
simpl.
destruct e.
destruct (proof_irrelevance _ H2 i).
Admitted.

Lemma FiniteT_img: forall (X Y:Type) (f:X->Y), FiniteT X -> (forall y1 y2:Y, y1=y2 \/ y1<>y2) -> Finite _ (Im Full_set f).
Proof.
intros.
induction H.
assert (Im Full_set f = Empty_set).
apply Extensionality_Ensembles.
red; split.
red; intros.
destruct H.
destruct x.
auto with sets.
rewrite H.
constructor.
assert ({exists x:T, f (Some x) = f None} + {forall x:T, f (Some x) <> f None}).
apply finite_dec_exists.
assumption.
intro.
apply decidable_dec.
apply H0.
case H1.
intro.
pose (g := fun (x:T) => f (Some x)).
assert (Im Full_set f = Im Full_set g).
apply Extensionality_Ensembles.
red; split.
red; intros.
destruct H2.
destruct x.
exists t.
constructor.
assumption.
destruct e.
exists x.
constructor.
transitivity (f None).
assumption.
symmetry; assumption.
red; intros.
destruct H2.
exists (Some x).
constructor.
assumption.
rewrite H2.
apply IHFiniteT.
intros.
pose (g := fun x:T => f (Some x)).
assert (Im Full_set f = Add (Im Full_set g) (f None)).
apply Extensionality_Ensembles.
red; split.
red; intros.
destruct H2.
destruct x.
left.
exists t.
constructor.
assumption.
right.
auto with sets.
red; intros.
destruct H2.
destruct H2.
exists (Some x).
constructor.
assumption.
destruct H2.
exists None.
constructor.
reflexivity.
rewrite H2.
constructor.
apply IHFiniteT.
red; intro.
destruct H3.
contradiction (n x).
symmetry; assumption.
pose (g := fun (x:X) => f (f0 x)).
assert (Im Full_set f = Im Full_set g).
apply Extensionality_Ensembles.
red; split.
red; intros.
destruct H2.
destruct H1.
rewrite H3.
rewrite <- H4 with x.
exists (g0 x).
constructor.
unfold g.
reflexivity.
red; intros.
destruct H2.
exists (f0 x).
constructor.
assumption.
rewrite H2.
Admitted.

Lemma surj_finite: forall (X Y:Type) (f:X->Y), FiniteT X -> surjective f -> (forall y1 y2:Y, y1=y2 \/ y1<>y2) -> FiniteT Y.
Proof.
intros.
apply bij_finite with {y:Y | In (Im Full_set f) y} (@proj1_sig _ (fun y:Y => In (Im Full_set f) y)).
apply Finite_ens_type.
apply FiniteT_img.
assumption.
assumption.
assert (forall y:Y, In (Im Full_set f) y).
intro.
destruct (H0 y).
exists x; auto with sets.
constructor.
pose (proj1_sig_inv := fun y:Y => exist (fun y0:Y => In (Im Full_set f) y0) y (H2 y)).
exists proj1_sig_inv.
destruct x.
simpl.
unfold proj1_sig_inv.
destruct (proof_irrelevance _ (H2 x) i); trivial.
Admitted.

Lemma finite_subtype: forall (X:Type) (P:X->Prop), FiniteT X -> (forall x:X, P x \/ ~ P x) -> FiniteT {x:X | P x}.
Proof.
intros.
induction H.
apply bij_finite with False (False_rect _).
constructor.
exists (@proj1_sig _ _).
destruct x.
intro s; destruct s; destruct x.
destruct (H0 None).
pose (g := fun (x:option {x:T | P (Some x)}) => match x return {x:option T | P x} with | Some (exist x0 i) => exist (fun x:option T => P x) (Some x0) i | None => exist (fun x:option T => P x) None H1 end).
apply bij_finite with _ g.
apply add_finite.
apply IHFiniteT.
intro; apply H0.
pose (ginv := fun (s:{x0:option T | P x0}) => match s return option {x:T | P (Some x)} with | exist (Some x0) i => Some (exist (fun y:T => P (Some y)) x0 i) | exist None _ => None end).
exists ginv.
destruct x as [[x0]|].
simpl.
reflexivity.
simpl.
reflexivity.
destruct y as [[x0|]].
simpl.
reflexivity.
simpl.
destruct (proof_irrelevance _ H1 p).
reflexivity.
pose (g := fun (x:{x:T | P (Some x)}) => match x return {x:option T | P x} with | exist x0 i => exist (fun x:option T => P x) (Some x0) i end).
apply bij_finite with _ g.
apply IHFiniteT.
intro; apply H0.
pose (ginv := fun s:{x0:option T | P x0} => match s return {x:T | P (Some x)} with | exist (Some x0) i => exist (fun x:T => P (Some x)) x0 i | exist None i => False_rect _ (H1 i) end).
exists ginv.
destruct x; simpl.
reflexivity.
destruct y as [[x0|]].
simpl.
reflexivity.
contradiction H1.
pose (g := fun (x:{x:X | P (f x)}) => match x with | exist x0 i => exist (fun x:Y => P x) (f x0) i end).
apply (bij_finite _ _ g).
apply IHFiniteT.
intro; apply H0.
destruct H1.
assert (forall y:Y, P y -> P (f (g0 y))).
intros; rewrite H2; assumption.
pose (ginv := fun (y:{y:Y | P y}) => match y with | exist y0 i => exist (fun x:X => P (f x)) (g0 y0) (H3 y0 i) end).
exists ginv.
destruct x; simpl.
generalize (H3 (f x) p).
rewrite H1.
intro; destruct (proof_irrelevance _ p p0).
reflexivity.
destruct y; simpl.
generalize (H3 x p).
rewrite H2.
intro; destruct (proof_irrelevance _ p p0).
Admitted.

Lemma inj_finite: forall (X Y:Type) (f:X->Y), FiniteT Y -> injective f -> (forall y:Y, (exists x:X, f x = y) \/ (~ exists x:X, f x = y)) -> FiniteT X.
Proof.
intros.
assert (forall y:{y:Y | exists x:X, f x = y}, {x:X | f x = proj1_sig y}).
intro.
destruct y.
simpl.
apply constructive_definite_description.
destruct e.
exists x0.
red; split.
assumption.
intros.
apply H0.
transitivity x.
assumption.
symmetry; assumption.
pose (g := fun y:{y:Y | exists x:X, f x = y} => proj1_sig (X0 y)).
apply bij_finite with _ g.
apply finite_subtype.
assumption.
assumption.
pose (ginv := fun (x:X) => exist (fun y:Y => exists x:X, f x = y) (f x) (ex_intro _ x (refl_equal _))).
exists ginv.
destruct x as [y [x e]].
unfold g; simpl.
match goal with |- context [X0 ?arg] => destruct (X0 arg) end.
simpl.
unfold ginv; simpl.
simpl in e0.
repeat match goal with |- context [ex_intro ?f ?x ?e] => generalize (ex_intro f x e) end.
rewrite <- e0.
intros; destruct (proof_irrelevance _ e1 e2).
reflexivity.
intro; unfold ginv.
unfold g; simpl.
match goal with |- context [X0 ?arg] => destruct (X0 arg) end.
simpl.
simpl in e.
Admitted.

Lemma True_finite: FiniteT True.
Proof.
apply bij_finite with (option False) (fun _ => I).
constructor; constructor.
exists (True_rect None).
destruct x as [[]|].
remember (True_rect (@None False) I) as LHS.
destruct LHS as [[]|].
reflexivity.
exact (fun y:True => match y with | I => refl_equal I end).
