Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Trivial.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Section ContextProperties.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {Gamma: Derivable L} {bSC: BasicSequentCalculus L Gamma} {minSC: MinimumSequentCalculus L Gamma} {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma} {cpSC: ClassicalPropositionalSequentCalculus L Gamma}.
End ContextProperties.

Lemma DDCS_MCS: forall (Phi: context), derivable_closed Phi -> orp_witnessed Phi -> consistent Phi -> maximal consistent Phi.
Proof.
intros.
split; auto.
intros.
unfold Included, Ensembles.In; intros.
pose proof derivable_excluded_middle Phi x.
apply H in H5.
apply H0 in H5.
destruct H5; auto.
exfalso.
apply H3 in H5; unfold Ensembles.In in H5.
rewrite consistent_spec in H2.
apply H2; clear H2.
apply derivable_assum in H4.
apply derivable_assum in H5.
eapply deduction_modus_ponens.
-
apply H4.
-
apply H5.
