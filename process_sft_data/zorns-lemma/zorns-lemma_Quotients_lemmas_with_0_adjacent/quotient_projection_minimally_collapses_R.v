Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export Image.
Require Import ImageImplicit.
Require Export Relation_Definitions.
Require Import Relation_Definitions_Implicit.
Require Import Description.
Require Import ProofIrrelevance.
Require Export EnsemblesSpec.
Set Implicit Arguments.
Section Quotient.
Variable A:Type.
Variable R:relation A.
Hypothesis equivR:equivalence R.
Definition equiv_class (x:A) : Ensemble A := [ y:A | R x y ].
Definition equiv_classes : Ensemble (Ensemble A) := Im Full_set equiv_class.
Definition quotient : Type := { S:Ensemble A | In equiv_classes S }.
Definition quotient_projection (x:A) : quotient := exist _ (equiv_class x) (equiv_class_in_quotient x).
End Quotient.
Section InducedFunction.
Variable A B:Type.
Variable R:Relation A.
Variable f:A->B.
Hypothesis equiv:equivalence R.
Hypothesis well_defined: forall x y:A, R x y -> f x = f y.
Definition induced_function (xbar:quotient R) : B := proj1_sig (constructive_definite_description _ (description_of_fbar xbar)).
End InducedFunction.
Section InducedFunction2.
Variable A B:Type.
Variable R:relation A.
Variable S:relation B.
Variable f:A->B.
Hypothesis equivR: equivalence R.
Hypothesis equivS: equivalence S.
Hypothesis well_defined2: forall a1 a2:A, R a1 a2 -> S (f a1) (f a2).
Definition projf (a:A) : quotient S := quotient_projection S (f a).
Definition induced_function2: quotient R -> quotient S := induced_function projf equivR projf_well_defined.
End InducedFunction2.
Section InducedFunction2arg.
Variable A B C:Type.
Variable R:relation A.
Variable S:relation B.
Variable f:A->B->C.
Hypothesis equivR:equivalence R.
Hypothesis equivS:equivalence S.
Hypothesis well_defined_2arg: forall (a1 a2:A) (b1 b2:B), R a1 a2 -> S b1 b2 -> f a1 b1 = f a2 b2.
Definition induced1 (a:A) : quotient S -> C := induced_function (f a) equivS (slices_well_defined a).
Definition eq_fn (f g:quotient S->C) := forall b:quotient S, f b = g b.
Definition induced2 := induced_function2 induced1 equivR eq_fn_equiv well_defined_induced1.
Definition eval (b:quotient S) (f:quotient S->C): C := f b.
Definition induced_eval (b:quotient S) := induced_function (eval b) eq_fn_equiv (well_defined_eval b).
Definition induced_function2arg (a:quotient R) (b:quotient S) : C := induced_eval b (induced2 a).
End InducedFunction2arg.
Section InducedFunction3.
Variable A B C:Type.
Variable R:relation A.
Variable S:relation B.
Variable T:relation C.
Variable f:A->B->C.
Hypothesis equivR:equivalence R.
Hypothesis equivS:equivalence S.
Hypothesis equivT:equivalence T.
Hypothesis well_defined3: forall (a1 a2:A) (b1 b2:B), R a1 a2 -> S b1 b2 -> T (f a1 b1) (f a2 b2).
Definition projf2 (a:A) (b:B) := quotient_projection T (f a b).
Definition induced_function3 : quotient R -> quotient S -> quotient T := induced_function2arg projf2 equivR equivS projf2_well_defined.
End InducedFunction3.

Lemma quotient_projection_minimally_collapses_R: forall x1 x2:A, quotient_projection x1 = quotient_projection x2 -> R x1 x2.
Proof.
intros.
apply equality_of_equiv_class_impl_R.
repeat rewrite <- quotient_projection_correct.
rewrite H.
reflexivity.
