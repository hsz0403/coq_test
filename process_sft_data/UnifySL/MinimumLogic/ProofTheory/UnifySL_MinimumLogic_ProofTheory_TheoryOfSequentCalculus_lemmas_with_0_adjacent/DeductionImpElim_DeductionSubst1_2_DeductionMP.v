Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.TheoryOfSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Local Open Scope logic_base.
Local Open Scope syntax.
Section PropertiesOfSequentCalculus.
Context (L: Language) (Gamma: Derivable L) {minL: MinimumLanguage L}.
Definition DeductionMP: Prop := forall (Phi: context) (x y: expr), Phi |-- x -> Phi |-- x --> y -> Phi |-- y.
Definition DeductionImpIntro: Prop := forall (Phi: context) (x y: expr), Phi;; x |-- y -> Phi |-- x --> y.
Definition DeductionImpElim: Prop := forall (Phi: context) (x y: expr), Phi |-- x --> y -> Phi;; x |-- y.
End PropertiesOfSequentCalculus.
Section TheoryOfSequentCalculus.
Context {L: Language} {Gamma: Derivable L} {minL: MinimumLanguage L}.
End TheoryOfSequentCalculus.

Lemma DeductionImpElim_DeductionSubst1_2_DeductionMP: DeductionImpElim L Gamma -> DeductionSubst1 L Gamma -> DeductionMP L Gamma.
Proof.
intros.
intros ? ? ? ? ?.
apply H in H2.
revert H1 H2; apply H0.
