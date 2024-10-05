Require Import Logic.lib.EnsemblesProperties.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Local Open Scope logic_base.
Section ContextProperty.
Context {L: Language} {minL: MinimumLanguage L} {Gamma: Derivable L} {fwSC: FiniteWitnessedSequentCalculus L Gamma}.
End ContextProperty.

Lemma can_derive_finite_witnessed: forall x, finite_witnessed (can_derive x).
Proof.
intros; hnf; intros.
Admitted.

Lemma cannot_derive_finite_captured: forall x, finite_captured (cannot_derive x).
Proof.
intros.
apply (not_finite_witnessed_finite_captured _ (can_derive_finite_witnessed x)).
