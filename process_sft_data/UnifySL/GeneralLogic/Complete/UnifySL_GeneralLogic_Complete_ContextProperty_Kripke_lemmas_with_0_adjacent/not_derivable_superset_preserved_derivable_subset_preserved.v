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

Lemma not_derivable_superset_preserved_derivable_subset_preserved: forall P, derivable_superset_preserved P -> derivable_subset_preserved (fun X => ~ P X).
Proof.
intros.
hnf; intros.
intro; apply H1; clear H1.
eapply H; [| exact H2].
auto.
