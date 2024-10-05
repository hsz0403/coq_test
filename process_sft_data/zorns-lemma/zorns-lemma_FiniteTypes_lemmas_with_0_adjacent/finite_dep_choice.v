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
apply H3.
