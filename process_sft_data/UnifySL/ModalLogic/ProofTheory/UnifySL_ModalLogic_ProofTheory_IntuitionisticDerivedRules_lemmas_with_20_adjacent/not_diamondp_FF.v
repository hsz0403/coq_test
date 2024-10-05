Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.ModalLogic.ProofTheory.ModalLogic.
Require Import Logic.ModalLogic.ProofTheory.RewriteClass.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.
Section IntuitionisticDerivedRules.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {ipAX: IntuitionisticPropositionalLogic L Gamma} {KmAX: SystemK L Gamma}.
End IntuitionisticDerivedRules.

Lemma boxp_andp: forall x y, |-- boxp (x && y) <--> (boxp x && boxp y).
Proof.
intros.
apply solve_andp_intros.
+
rewrite <- (andp_elim1 x y) at 2.
rewrite <- (andp_elim2 x y) at 3.
rewrite andp_dup.
apply provable_impp_refl.
+
rewrite <- impp_curry_uncurry.
rewrite <- axiom_K.
rewrite <- axiom_K.
apply rule_N.
Admitted.

Lemma orp_boxp: forall x y, |-- boxp x || boxp y --> boxp (x || y).
Proof.
intros.
apply solve_orp_impp.
+
rewrite <- axiom_K.
apply rule_N.
apply orp_intros1.
+
rewrite <- axiom_K.
apply rule_N.
Admitted.

Lemma boxp_TT: |-- boxp TT.
Proof.
apply rule_N.
Admitted.

Lemma impp_diamondp: forall x y, |-- boxp (x --> y) --> (diamondp x --> diamondp y).
Proof.
intros.
unfold diamondp.
rewrite <- contrapositivePP.
rewrite <- axiom_K.
rewrite <- axiom_K.
apply rule_N.
Admitted.

Lemma diamondp_andp: forall x y, |-- diamondp (x && y) --> (diamondp x && diamondp y).
Proof.
intros.
apply solve_impp_andp.
+
rewrite <- impp_diamondp.
apply rule_N.
apply andp_elim1.
+
rewrite <- impp_diamondp.
apply rule_N.
Admitted.

Lemma orp_diamondp: forall x y, |-- diamondp x || diamondp y --> diamondp (x || y).
Proof.
intros.
apply solve_orp_impp.
+
rewrite <- impp_diamondp.
apply rule_N.
apply orp_intros1.
+
rewrite <- impp_diamondp.
apply rule_N.
Admitted.

Lemma P_diamondp_P {TmGamma: SystemT L Gamma}: forall x, |-- x --> diamondp x.
Proof.
intros.
unfold diamondp.
rewrite <- contrapositivePN.
Admitted.

Lemma not_diamondp_FF: |-- ~~ diamondp FF.
Proof.
intros.
unfold diamondp.
rewrite <- double_negp_intros.
apply rule_N.
apply provable_impp_refl.
