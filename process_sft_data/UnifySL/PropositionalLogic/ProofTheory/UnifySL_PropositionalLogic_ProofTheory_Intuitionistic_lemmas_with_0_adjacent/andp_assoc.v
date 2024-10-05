Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Class IntuitionisticPropositionalLogic (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} := { andp_intros: forall x y, |-- x --> y --> x && y; andp_elim1: forall x y, |-- x && y --> x; andp_elim2: forall x y, |-- x && y --> y; orp_intros1: forall x y, |-- x --> x || y; orp_intros2: forall x y, |-- y --> x || y; orp_elim: forall x y z, |-- (x --> z) --> (y --> z) --> (x || y --> z); falsep_elim: forall x, |-- FF --> x }.
Class IntuitionisticPropositionalSequentCalculus (L: Language) {pL: PropositionalLanguage L} (Gamma: Derivable L) := { deduction_andp_intros: forall Phi x y, Phi |-- x -> Phi |-- y -> Phi |-- x && y; deduction_andp_elim1: forall Phi x y, Phi |-- x && y -> Phi |-- x; deduction_andp_elim2: forall Phi x y, Phi |-- x && y -> Phi |-- y; deduction_orp_intros1: forall Phi x y, Phi |-- x -> Phi |-- x || y; deduction_orp_intros2: forall Phi x y, Phi |-- y -> Phi |-- x || y; deduction_orp_elim: forall Phi x y z, Phi;; x |-- z -> Phi ;; y |-- z -> Phi;; x || y |-- z; deduction_falsep_elim: forall Phi x, Phi |-- FF -> Phi |-- x }.
Section DerivableRulesFromSequentCalculus1.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {Gamma: Derivable L} {bSC: BasicSequentCalculus L Gamma} {minSC: MinimumSequentCalculus L Gamma} {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}.
End DerivableRulesFromSequentCalculus1.
Section SequentCalculus2Axiomatization.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {GammaP: Provable L} {GammaD: Derivable L} {SC: NormalSequentCalculus L GammaP GammaD} {bSC: BasicSequentCalculus L GammaD} {minSC: MinimumSequentCalculus L GammaD} {ipSC: IntuitionisticPropositionalSequentCalculus L GammaD} {minAX: MinimumAxiomatization L GammaP}.
End SequentCalculus2Axiomatization.
Instance reg_SequentCalculus2Axiomatization_ipAX: RegisterClass D2P_reg (fun ipAX: unit => @SequentCalculus2Axiomatization_ipAX) 2.
Section Axiomatization2SequentCalculus.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {GammaP: Provable L} {GammaD: Derivable L} {AX: NormalAxiomatization L GammaP GammaD} {bSC: BasicSequentCalculus L GammaD} {minSC: MinimumSequentCalculus L GammaD} {minAX: MinimumAxiomatization L GammaP} {ipGamma: IntuitionisticPropositionalLogic L GammaP}.
End Axiomatization2SequentCalculus.
Instance reg_Axiomatization2SequentCalculus_ipSC: RegisterClass P2D_reg (fun ipSC: unit => @Axiomatization2SequentCalculus_ipSC) 4.
Section DerivableRulesFromAxiomatization1.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma}.
End DerivableRulesFromAxiomatization1.
Section DerivableRulesFromSequentCalculus2.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {Gamma: Derivable L} {bSC: BasicSequentCalculus L Gamma} {minSC: MinimumSequentCalculus L Gamma} {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}.
End DerivableRulesFromSequentCalculus2.
Section DerivableRulesFromAxiomatization2.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma}.
End DerivableRulesFromAxiomatization2.

Lemma andp_assoc: forall (x y z: expr), |-- x && y && z <--> x && (y && z).
Proof.
AddSequentCalculus.
intros.
rewrite provable_derivable.
apply deduction_andp_intros.
+
rewrite <- deduction_theorem.
apply deduction_andp_intros; [| apply deduction_andp_intros].
-
eapply deduction_andp_elim1.
eapply deduction_andp_elim1.
apply derivable_assum1.
-
eapply deduction_andp_elim2.
eapply deduction_andp_elim1.
apply derivable_assum1.
-
eapply deduction_andp_elim2.
apply derivable_assum1.
+
rewrite <- deduction_theorem.
apply deduction_andp_intros; [apply deduction_andp_intros |].
-
eapply deduction_andp_elim1.
apply derivable_assum1.
-
eapply deduction_andp_elim1.
eapply deduction_andp_elim2.
apply derivable_assum1.
-
eapply deduction_andp_elim2.
eapply deduction_andp_elim2.
apply derivable_assum1.
