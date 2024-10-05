Require Import Coq.Sets.Ensembles.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Logic.lib.Ensembles_ext.
Section Properties.
Context {A: Type}.
Definition finite_captured (P: Ensemble A -> Prop): Prop := forall (Phi: Ensemble A), (forall xs: list A, Forall Phi xs -> P (fun x => In x xs)) -> P Phi.
Definition finite_witnessed (P: Ensemble A -> Prop): Prop := forall (Phi: Ensemble A), P Phi -> exists xs: list A, Forall Phi xs /\ P (fun x => In x xs).
Definition subset_preserved (P: Ensemble A -> Prop): Prop := forall (Phi Psi: Ensemble A), Included _ Phi Psi -> P Psi -> P Phi.
Definition superset_preserved (P: Ensemble A -> Prop): Prop := forall (Phi Psi: Ensemble A), Included _ Phi Psi -> P Phi -> P Psi.
End Properties.

Lemma not_superset_preserved_subset_preserved: forall P, superset_preserved P -> subset_preserved (fun X => ~ P X).
Proof.
intros.
hnf in H |- *.
firstorder.
