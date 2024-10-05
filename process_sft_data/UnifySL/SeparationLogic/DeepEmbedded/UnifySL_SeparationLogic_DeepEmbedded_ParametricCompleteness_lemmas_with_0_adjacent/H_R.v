Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.GeneralLogic.Complete.Canonical_Kripke.
Require Import Logic.GeneralLogic.Complete.Complete_Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimumLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.MinimumLogic.Complete.Truth_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.PropositionalLogic.Complete.Truth_Kripke.
Require Import Logic.PropositionalLogic.Complete.Canonical_Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.SeparationLogic.Complete.ContextProperty_Flat.
Require Import Logic.SeparationLogic.Complete.Lindenbaum_Flat.
Require Import Logic.SeparationLogic.Complete.Truth_Flat.
Require Import Logic.SeparationLogic.Complete.Canonical_Flat.
Require Import Logic.SeparationLogic.DeepEmbedded.Parameter.
Require Logic.SeparationLogic.DeepEmbedded.SeparationEmpLanguage.
Require Logic.SeparationLogic.DeepEmbedded.FlatSemantics.
Require Logic.SeparationLogic.DeepEmbedded.ParametricSeparationLogic.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Local Open Scope kripke_model_class.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Import KripkeModelClass.
Section Complete.
Context {Sigma: SeparationEmpLanguage.PropositionalVariables} {CV: Countable SeparationEmpLanguage.Var} (SLP: SL_Parameter).
Existing Instances SeparationEmpLanguage.L SeparationEmpLanguage.minL SeparationEmpLanguage.pL SeparationEmpLanguage.sepconL SeparationEmpLanguage.wandL SeparationEmpLanguage.empL.
Existing Instances ParametricSeparationLogic.GP ParametricSeparationLogic.GD ParametricSeparationLogic.AX ParametricSeparationLogic.minAX ParametricSeparationLogic.ipAX ParametricSeparationLogic.sepconAX ParametricSeparationLogic.wandAX ParametricSeparationLogic.empAX ParametricSeparationLogic.sepcon_orp_AX ParametricSeparationLogic.sepcon_falsep_AX ParametricSeparationLogic.ParAX.
Existing Instances Axiomatization2SequentCalculus_SC Axiomatization2SequentCalculus_bSC Axiomatization2SequentCalculus_fwSC Axiomatization2SequentCalculus_minSC Axiomatization2SequentCalculus_ipSC Axiomatization2SequentCalculus_cpSC.
Existing Instances FlatSemantics.MD FlatSemantics.kMD FlatSemantics.R FlatSemantics.J FlatSemantics.SM FlatSemantics.kminSM FlatSemantics.kpSM FlatSemantics.fsepconSM FlatSemantics.fwandSM FlatSemantics.fempSM.
Definition cP : context -> Prop := Intersection _ (Intersection _ derivable_closed orp_witnessed) consistent.
Definition canonical_frame: FlatSemantics.frame := FlatSemantics.Build_frame (sig cP) (fun a b => Included _ (proj1_sig a) (proj1_sig b)) (fun a b c => Included _ (context_sepcon (proj1_sig a) (proj1_sig b)) (proj1_sig c)).
Definition canonical_eval: SeparationEmpLanguage.Var -> FlatSemantics.sem canonical_frame := fun p a => proj1_sig a (SeparationEmpLanguage.varp p).
Definition canonical_Kmodel: @Kmodel FlatSemantics.MD FlatSemantics.kMD := FlatSemantics.Build_Kmodel canonical_frame canonical_eval.
Definition rel: bijection (Kworlds canonical_Kmodel) (sig cP) := bijection_refl.
Definition H_R: forall m n Phi Psi, rel m Phi -> rel n Psi -> (m <= n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).
Proof.
intros.
change (m = Phi) in H.
change (n = Psi) in H0.
subst; reflexivity.
Definition H_J: forall m1 m2 m Phi1 Phi2 Phi, rel m1 Phi1 -> rel m2 Phi2 -> rel m Phi -> (join m1 m2 m <-> Included _ (context_sepcon (proj1_sig Phi1) (proj1_sig Phi2)) (proj1_sig Phi)).
Proof.
intros.
change (m = Phi) in H1.
change (m1 = Phi1) in H.
change (m2 = Phi2) in H0.
subst; reflexivity.
Context (SAP: SA_Parameter).
Hypothesis PC: Parameter_coincide SLP SAP.
End Complete.

Definition H_R: forall m n Phi Psi, rel m Phi -> rel n Psi -> (m <= n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).
Proof.
intros.
change (m = Phi) in H.
change (n = Psi) in H0.
subst; reflexivity.
