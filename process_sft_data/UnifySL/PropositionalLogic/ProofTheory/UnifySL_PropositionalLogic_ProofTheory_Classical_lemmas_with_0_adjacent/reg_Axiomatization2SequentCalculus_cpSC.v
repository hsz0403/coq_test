Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Class ClassicalPropositionalLogic (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} := { excluded_middle: forall x, |-- x || ~~ x }.
Class ClassicalPropositionalSequentCalculus (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} (Gamma: Derivable L) {bSC: BasicSequentCalculus L Gamma} {minSC: MinimumSequentCalculus L Gamma} {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma} := { derivable_excluded_middle: forall Phi x, Phi |-- x || ~~ x }.
Section Axiomatization2SequentCalculus.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {GammaP: Provable L} {GammaD: Derivable L} {minAX: MinimumAxiomatization L GammaP} {ipAX: IntuitionisticPropositionalLogic L GammaP} {cpAX: ClassicalPropositionalLogic L GammaP} {SC: NormalSequentCalculus L GammaP GammaD} {bSC: BasicSequentCalculus L GammaD} {minSC: MinimumSequentCalculus L GammaD} {ipSC: IntuitionisticPropositionalSequentCalculus L GammaD}.
End Axiomatization2SequentCalculus.
Instance reg_Axiomatization2SequentCalculus_cpSC: RegisterClass P2D_reg (fun cpSC: unit => @Axiomatization2SequentCalculus_cpSC) 5.
Section SequentCalculus2Axiomatization.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {GammaP: Provable L} {GammaD: Derivable L} {SC: NormalSequentCalculus L GammaP GammaD} {bSC: BasicSequentCalculus L GammaD} {minSC: MinimumSequentCalculus L GammaD} {ipSC: IntuitionisticPropositionalSequentCalculus L GammaD} {cpSC: ClassicalPropositionalSequentCalculus L GammaD} {minAX: MinimumAxiomatization L GammaP} {ipAX: IntuitionisticPropositionalLogic L GammaP}.
End SequentCalculus2Axiomatization.
Instance reg_SequentCalculus2Axiomatization_cpAX: RegisterClass D2P_reg (fun cpAX: unit => @SequentCalculus2Axiomatization_cpAX) 3.
Section DerivableRulesFromAxiomatization1.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {ipAX: IntuitionisticPropositionalLogic L Gamma} {cpAX: ClassicalPropositionalLogic L Gamma}.
Instance Classical2GodelDummett: GodelDummettPropositionalLogic L Gamma.
Proof.
constructor.
AddSequentCalculus.
intros.
rewrite provable_derivable.
set (Phi := empty_context).
clearbody Phi.
pose proof excluded_middle x.
apply deduction_weaken0 with (Phi0 := Phi) in H.
eapply deduction_modus_ponens; [exact H |].
apply deduction_orp_elim'.
+
rewrite <- deduction_theorem.
apply deduction_orp_intros2.
rewrite deduction_theorem.
apply derivable_axiom1.
+
rewrite <- deduction_theorem.
apply deduction_orp_intros1.
rewrite deduction_theorem.
apply deduction_impp_arg_switch.
apply derivable_contradiction_elim.
End DerivableRulesFromAxiomatization1.
Section DerivableRulesFromSequentCalculus.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {Gamma: Derivable L} {bSC: BasicSequentCalculus L Gamma} {minSC: MinimumSequentCalculus L Gamma} {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma} {cpSC: ClassicalPropositionalSequentCalculus L Gamma}.
End DerivableRulesFromSequentCalculus.
Section DerivableRulesFromAxiomatization2.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {ipAX: IntuitionisticPropositionalLogic L Gamma} {cpAX: ClassicalPropositionalLogic L Gamma}.
End DerivableRulesFromAxiomatization2.

Instance reg_Axiomatization2SequentCalculus_cpSC: RegisterClass P2D_reg (fun cpSC: unit => @Axiomatization2SequentCalculus_cpSC) 5.
