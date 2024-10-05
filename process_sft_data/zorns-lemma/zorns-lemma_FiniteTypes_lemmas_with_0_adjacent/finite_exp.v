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
rewrite H2; reflexivity.
