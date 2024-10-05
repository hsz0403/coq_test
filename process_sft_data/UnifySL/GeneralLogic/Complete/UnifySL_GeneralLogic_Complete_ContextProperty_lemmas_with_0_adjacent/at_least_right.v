Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Local Open Scope logic_base.
Section ContextProperty.
Context {L: Language}.
Definition at_least (P cP: context -> Prop): Prop := forall (Phi: context), cP Phi -> P Phi.
Definition maximal (P: context -> Prop): context -> Prop := fun Phi => P Phi /\ forall Psi, P Psi -> Included _ Phi Psi -> Included _ Psi Phi.
End ContextProperty.
Ltac solve_at_least := solve [apply at_least_self | auto | apply at_least_left; solve_at_least | apply at_least_right; solve_at_least].

Lemma at_least_right: forall P cP1 cP2, at_least P cP2 -> at_least P (Intersection _ cP1 cP2).
Proof.
intros.
hnf in H |- *; intros.
destruct H0; auto.
