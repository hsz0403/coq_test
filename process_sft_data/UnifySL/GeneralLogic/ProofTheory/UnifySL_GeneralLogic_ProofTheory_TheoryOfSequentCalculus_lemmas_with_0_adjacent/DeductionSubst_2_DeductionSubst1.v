Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Local Open Scope logic_base.
Section PropertiesOfSequentCalculus.
Context (L: Language) (Gamma: Derivable L).
Definition DerivableRefl: Prop := forall x: expr, empty_context;; x |-- x.
Definition DeductionWeaken: Prop := forall (Phi Psi: context) (x: expr), Included _ Phi Psi -> Phi |-- x -> Psi |-- x.
Definition DerivableAssu: Prop := forall (Phi: context) (x: expr), Ensembles.In _ Phi x -> Phi |-- x.
Definition DeductionSubst1: Prop := forall (Phi: context) (x y: expr), Phi |-- x -> Phi;; x |-- y -> Phi |-- y.
Definition DeductionSubst: Prop := forall (Phi Psi: context) (y: expr), (forall x, Psi x -> Phi |-- x) -> Union _ Phi Psi |-- y -> Phi |-- y.
Definition DerivableFiniteWitnessed: Prop := forall (Phi: context) (y: expr), Phi |-- y -> exists xs, Forall Phi xs /\ (fun x => In x xs) |-- y.
Definition ContextualDerivableFiniteWitnessed: Prop := forall (Phi Psi: context) (y: expr), Union _ Phi Psi |-- y -> exists xs, Forall Psi xs /\ Union _ Phi (fun x => In x xs) |-- y.
End PropertiesOfSequentCalculus.
Section TheoryOfSequentCalculus.
Context {L: Language} {Gamma: Derivable L}.
End TheoryOfSequentCalculus.

Lemma DeductionSubst_2_DeductionSubst1: DeductionSubst L Gamma -> DeductionSubst1 L Gamma.
Proof.
intros.
hnf; intros.
apply H with (Singleton _ x); auto.
intros.
inversion H2; subst.
auto.
