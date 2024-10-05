Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.EnsemblesProperties.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.Canonical_Kripke.
Require Import Logic.GeneralLogic.Complete.Complete_Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimumLogic.Complete.Truth_Kripke.
Require Import Logic.MinimumLogic.Complete.Lindenbaum_Kripke.
Require Logic.MinimumLogic.DeepEmbedded.MinimumLanguage.
Require Logic.MinimumLogic.DeepEmbedded.MinimumLogic.
Require Logic.MinimumLogic.DeepEmbedded.KripkeSemantics.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Local Open Scope kripke_model_class.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Import KripkeModelClass.
Section Complete.
Context (Var: Type) (CV: Countable Var).
Instance L: Language := MinimumLanguage.L Var.
Instance minL: MinimumLanguage L := MinimumLanguage.minL Var.
Instance GP: Provable L := MinimumLogic.GP Var.
Instance GD: Derivable L := MinimumLogic.GD Var.
Instance AX: NormalAxiomatization L GP GD := MinimumLogic.AX Var.
Instance minAX: MinimumAxiomatization L GP := MinimumLogic.minAX Var.
Instance SC: NormalSequentCalculus L GP GD := MinimumLogic.SC Var.
Instance bSC: BasicSequentCalculus L GD := MinimumLogic.bSC Var.
Instance fwSC: FiniteWitnessedSequentCalculus L GD := MinimumLogic.fwSC Var.
Instance minSC: MinimumSequentCalculus L GD := MinimumLogic.minSC Var.
Instance Kripke_MD: Model := KripkeSemantics.MD Var.
Instance Kripke_kMD: KripkeModel Kripke_MD := KripkeSemantics.kMD Var.
Instance Kripke_R (M: Kmodel): Relation (Kworlds M) := KripkeSemantics.R Var M.
Instance Kripke_SM: Semantics L Kripke_MD := KripkeSemantics.SM Var.
Instance Kripke_kminSM (M: Kmodel): KripkeMinimumSemantics L Kripke_MD M Kripke_SM := KripkeSemantics.kminSM Var M.
Definition cP: context -> Prop := derivable_closed.
Definition canonical_frame: KripkeSemantics.frame := KripkeSemantics.Build_frame (sig cP) (fun a b => Included _ (proj1_sig a) (proj1_sig b)).
Definition canonical_eval: Var -> KripkeSemantics.sem canonical_frame := fun p a => proj1_sig a (MinimumLanguage.varp p).
Definition canonical_Kmodel: @Kmodel (KripkeSemantics.MD Var) (KripkeSemantics.kMD Var) := KripkeSemantics.Build_Kmodel Var canonical_frame canonical_eval.
Definition rel: bijection (Kworlds canonical_Kmodel) (sig cP) := bijection_refl.
Definition H_R: forall m n Phi Psi, rel m Phi -> rel n Psi -> (m <= n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).
Proof.
intros.
change (m = Phi) in H.
change (n = Psi) in H0.
subst; reflexivity.
Import Logic.MinimumLogic.DeepEmbedded.KripkeSemantics.
End Complete.

Lemma AL_DC: at_least derivable_closed cP.
Proof.
solve_at_least.
