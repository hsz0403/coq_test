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

Lemma MCS_impp_iff: forall (Phi: context), maximal consistent Phi -> (forall x y: expr, Phi (x --> y) <-> (Phi x -> Phi y)).
Proof.
intros.
split; intros.
+
rewrite MCS_element_derivable in H0, H1 |- * by auto.
apply (deduction_modus_ponens _ x y); auto.
+
pose proof derivable_excluded_middle Phi y.
rewrite <- MCS_element_derivable in H1 by auto.
rewrite MCS_orp_iff in H1 by auto.
pose proof derivable_excluded_middle Phi x.
rewrite <- MCS_element_derivable in H2 by auto.
rewrite MCS_orp_iff in H2 by auto.
destruct H1; [| destruct H2].
-
rewrite MCS_element_derivable in H1 |- * by auto.
apply deduction_left_impp_intros; auto.
-
exfalso.
apply H0 in H2.
rewrite MCS_element_derivable in H1, H2 by auto.
pose proof deduction_modus_ponens _ _ _ H2 H1.
destruct H as [? _].
rewrite consistent_spec in H; auto.
-
rewrite MCS_element_derivable in H2 |- * by auto.
unfold negp in H2.
rewrite <- deduction_theorem in H2 |- *.
pose proof deduction_falsep_elim _ y H2.
auto.
