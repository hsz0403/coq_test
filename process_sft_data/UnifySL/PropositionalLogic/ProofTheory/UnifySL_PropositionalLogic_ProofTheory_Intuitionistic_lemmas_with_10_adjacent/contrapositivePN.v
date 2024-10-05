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

Lemma solve_andp_elim1: forall x y: expr, |-- x && y -> |-- x.
Proof.
AddSequentCalculus.
intros.
rewrite provable_derivable in H |- *.
Admitted.

Lemma solve_andp_elim2: forall x y: expr, |-- x && y -> |-- y.
Proof.
AddSequentCalculus.
intros.
rewrite provable_derivable in H |- *.
Admitted.

Lemma solve_impp_elim_left: forall x y: expr, |-- y -> |-- x --> y.
Proof.
intros.
eapply modus_ponens.
+
apply axiom1.
+
Admitted.

Lemma solve_orp_impp: forall x y z: expr, |-- x --> z -> |-- y --> z -> |-- x || y --> z.
Proof.
intros.
eapply modus_ponens; [| exact H0].
eapply modus_ponens; [| exact H].
Admitted.

Lemma solve_orp_intros1: forall x y: expr, |-- x -> |-- x || y.
Proof.
intros.
eapply modus_ponens; [| exact H].
Admitted.

Lemma solve_orp_intros2: forall x y: expr, |-- y -> |-- x || y.
Proof.
intros.
eapply modus_ponens; [| exact H].
Admitted.

Lemma solve_impp_andp: forall x y z: expr, |-- x --> y -> |-- x --> z -> |-- x --> y && z.
Proof.
AddSequentCalculus.
intros.
rewrite provable_derivable in H, H0 |- *.
rewrite <- deduction_theorem in H, H0 |- *.
Admitted.

Lemma double_negp_intros: forall (x: expr), |-- x --> ~~ ~~ x.
Proof.
AddSequentCalculus.
intros.
rewrite provable_derivable.
Admitted.

Lemma provable_iffp_refl: forall (x: expr), |-- x <--> x.
Proof.
AddSequentCalculus.
intros.
Admitted.

Lemma contrapositivePP: forall (x y: expr), |-- (y --> x) --> ~~ x --> ~~ y.
Proof.
intros.
eapply modus_ponens; [apply provable_impp_arg_switch |].
Admitted.

Lemma deduction_contrapositivePP: forall Phi (x y: expr), Phi |-- y --> x -> Phi |-- ~~ x --> ~~ y.
Proof.
AddAxiomatization.
intros.
eapply deduction_modus_ponens; eauto.
apply deduction_weaken0.
Admitted.

Lemma deduction_contrapositivePN: forall Phi (x y: expr), Phi |-- y --> ~~ x -> Phi |-- x --> ~~ y.
Proof.
AddAxiomatization.
intros.
eapply deduction_modus_ponens; eauto.
apply deduction_weaken0.
Admitted.

Lemma demorgan_orp_negp: forall (x y: expr), |-- ~~ x || ~~ y --> ~~ (x && y).
Proof.
AddSequentCalculus.
intros.
rewrite provable_derivable.
unfold negp at 3.
rewrite <- !deduction_theorem.
apply (deduction_modus_ponens _ (~~ x || ~~ y)).
+
apply deduction_weaken1.
apply derivable_assum1.
+
apply deduction_orp_elim'.
-
rewrite <- deduction_theorem.
apply (deduction_modus_ponens _ x); [| apply derivable_assum1].
apply deduction_weaken1.
eapply deduction_andp_elim1.
apply derivable_assum1.
-
rewrite <- deduction_theorem.
apply (deduction_modus_ponens _ y); [| apply derivable_assum1].
apply deduction_weaken1.
eapply deduction_andp_elim2.
Admitted.

Lemma demorgan_negp_orp: forall (x y: expr), |-- ~~ (x || y) <--> (~~ x && ~~ y).
Proof.
AddSequentCalculus.
intros.
rewrite provable_derivable.
apply deduction_andp_intros.
+
rewrite <- deduction_theorem.
apply deduction_andp_intros.
-
rewrite deduction_theorem.
apply deduction_contrapositivePP.
rewrite <- provable_derivable.
apply orp_intros1.
-
rewrite deduction_theorem.
apply deduction_contrapositivePP.
rewrite <- provable_derivable.
apply orp_intros2.
+
rewrite <- deduction_theorem.
apply deduction_orp_elim'.
-
eapply deduction_andp_elim1.
apply derivable_assum1.
-
eapply deduction_andp_elim2.
Admitted.

Lemma provable_truep: |-- TT.
Proof.
Admitted.

Lemma andp_comm: forall (x y: expr), |-- x && y <--> y && x.
Proof.
AddSequentCalculus.
intros.
rewrite provable_derivable.
apply deduction_andp_intros.
+
rewrite <- deduction_theorem.
apply deduction_andp_intros.
-
eapply deduction_andp_elim2.
apply derivable_assum1.
-
eapply deduction_andp_elim1.
apply derivable_assum1.
+
rewrite <- deduction_theorem.
apply deduction_andp_intros.
-
eapply deduction_andp_elim2.
apply derivable_assum1.
-
eapply deduction_andp_elim1.
Admitted.

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
Admitted.

Lemma orp_comm: forall (x y: expr), |-- x || y <--> y || x.
Proof.
AddSequentCalculus.
intros.
rewrite provable_derivable.
apply deduction_andp_intros.
+
apply deduction_orp_elim'; rewrite <- provable_derivable.
-
apply orp_intros2.
-
apply orp_intros1.
+
apply deduction_orp_elim'; rewrite <- provable_derivable.
-
apply orp_intros2.
-
Admitted.

Lemma orp_assoc: forall (x y z: expr), |-- x || y || z <--> x || (y || z).
Proof.
AddSequentCalculus.
intros.
rewrite provable_derivable.
apply deduction_andp_intros.
+
apply deduction_orp_elim'; [apply deduction_orp_elim' |]; rewrite <- deduction_theorem.
-
apply deduction_orp_intros1.
apply derivable_assum1.
-
apply deduction_orp_intros2.
apply deduction_orp_intros1.
apply derivable_assum1.
-
apply deduction_orp_intros2.
apply deduction_orp_intros2.
apply derivable_assum1.
+
apply deduction_orp_elim'; [| apply deduction_orp_elim']; rewrite <- deduction_theorem.
-
apply deduction_orp_intros1.
apply deduction_orp_intros1.
apply derivable_assum1.
-
apply deduction_orp_intros1.
apply deduction_orp_intros2.
apply derivable_assum1.
-
apply deduction_orp_intros2.
Admitted.

Lemma andp_truep: forall (x: expr), |-- x && TT <--> x.
Proof.
AddSequentCalculus.
intros.
rewrite provable_derivable.
apply deduction_andp_intros.
+
apply derivable_andp_elim1.
+
rewrite <- deduction_theorem.
apply deduction_andp_intros.
-
apply derivable_assum1.
-
Admitted.

Lemma contrapositivePN: forall (x y: expr), |-- (y --> ~~ x) --> (x --> ~~ y).
Proof.
intros.
apply provable_impp_arg_switch.
