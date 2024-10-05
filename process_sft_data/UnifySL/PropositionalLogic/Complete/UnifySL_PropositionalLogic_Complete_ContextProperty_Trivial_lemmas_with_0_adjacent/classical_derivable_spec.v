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

Lemma classical_derivable_spec: forall (Phi: context) (x: expr), Phi |-- x <-> ~ consistent (Union _ Phi (Singleton _ (~~ x))).
Proof.
intros.
unfold consistent.
AddAxiomatization.
fold (@consistent L Gamma (Phi;; ~~ x)).
rewrite <- (double_negp x) at 1.
unfold negp at 1.
rewrite <- deduction_theorem.
rewrite consistent_spec.
tauto.
