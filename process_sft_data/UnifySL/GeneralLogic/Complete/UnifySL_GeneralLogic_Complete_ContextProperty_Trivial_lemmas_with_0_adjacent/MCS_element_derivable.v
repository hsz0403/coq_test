Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Local Open Scope logic_base.
Section ContextProperty.
Context {L: Language} {Gamma: Derivable L} {bSC: BasicSequentCalculus L Gamma}.
End ContextProperty.

Lemma MCS_element_derivable: forall(Phi: context), maximal consistent Phi -> (forall x: expr, Phi x <-> Phi |-- x).
Proof.
intros.
apply derivable_closed_element_derivable, maximal_consistent_derivable_closed.
auto.
