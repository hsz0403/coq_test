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
reflexivity.
