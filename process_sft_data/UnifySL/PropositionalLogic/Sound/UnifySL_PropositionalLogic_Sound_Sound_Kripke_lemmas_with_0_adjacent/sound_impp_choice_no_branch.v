Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Section Sound_Kripke.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {kminSM: KripkeMinimumSemantics L MD M SM} {kpSM: KripkePropositionalSemantics L MD M SM}.
End Sound_Kripke.

Lemma sound_impp_choice_no_branch {nkiM: NoBranchKripkeIntuitionisticModel (Kworlds M)}: forall x y: expr, forall m, KRIPKE: M, m |= (x --> y) || (y --> x).
Proof.
intros.
rewrite sat_orp, !sat_impp.
apply Classical_Prop.NNPP; intro.
apply not_or_and in H; destruct H.
apply not_all_ex_not in H.
apply not_all_ex_not in H0.
destruct H as [n1 ?], H0 as [n2 ?].
apply imply_to_and in H.
apply imply_to_and in H0.
destruct H, H0.
apply imply_to_and in H1.
apply imply_to_and in H2.
destruct H1, H2.
destruct (Korder_no_branch n1 n2 m H H0).
+
pose proof (sat_mono _ _ x H5).
tauto.
+
pose proof (sat_mono _ _ y H5).
tauto.
