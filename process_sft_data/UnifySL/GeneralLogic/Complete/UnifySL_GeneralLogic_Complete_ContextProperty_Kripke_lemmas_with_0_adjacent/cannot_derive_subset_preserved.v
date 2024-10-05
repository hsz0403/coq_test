Require Import Logic.lib.EnsemblesProperties.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Local Open Scope logic_base.
Section ContextProperty.
Context {L: Language} {Gamma: Derivable L} {bSC: BasicSequentCalculus L Gamma}.
End ContextProperty.
Section CanonicalProperties.
Context {L: Language} {Gamma: Derivable L}.
Definition derivable_closed : context -> Prop := fun Phi => forall x, derivable Phi x -> Phi x.
Definition derivable_superset_preserved (P: context -> Prop): Prop := forall Phi Psi, Included _ (derivable Phi) (derivable Psi) -> P Phi -> P Psi.
Definition derivable_subset_preserved (P: context -> Prop): Prop := forall Phi Psi, Included _ (derivable Phi) (derivable Psi) -> P Psi -> P Phi.
Context {bSC: BasicSequentCalculus L Gamma}.
End CanonicalProperties.
Section ContextProperties.
Context {L: Language} {Gamma: Derivable L}.
Definition can_derive (x: expr): context -> Prop := fun Phi => Phi |-- x.
Definition cannot_derive (x: expr): context -> Prop := fun Phi => ~ Phi |-- x.
Context {bSC: BasicSequentCalculus L Gamma}.
End ContextProperties.

Lemma cannot_derive_subset_preserved: forall x, subset_preserved (cannot_derive x).
Proof.
intros.
apply (not_superset_preserved_subset_preserved _ (can_derive_superset_preserved x)).
