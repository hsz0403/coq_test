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

Lemma MCS_nonelement_inconsistent: forall (Phi: context), maximal consistent Phi -> (forall x: expr, ~ Phi x <-> Phi |-- x --> FF).
Proof.
intros.
split; intros.
+
destruct H.
specialize (H1 (Union _ Phi (Singleton _ x))).
rewrite consistent_spec in H1.
rewrite deduction_theorem in H1.
assert (Included expr Phi (Union expr Phi (Singleton expr x))) by (intros ? ?; left; auto).
assert (~ Included expr (Union expr Phi (Singleton expr x)) Phi) by (intros HH; specialize (HH x); apply H0, HH; right; constructor).
tauto.
+
intro.
pose proof derivable_assum Phi x H1.
pose proof deduction_modus_ponens _ _ _ H2 H0.
destruct H as [? _].
rewrite consistent_spec in H; auto.
