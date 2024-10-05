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

Lemma sound_weak_excluded_middle_branch_join {bkiM: BranchJoinKripkeIntuitionisticModel (Kworlds M)}: forall x: expr, forall m, KRIPKE: M, m |= ~~ x || ~~ ~~ x.
Proof.
intros.
unfold negp.
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
destruct H1 as [? _], H2 as [? _].
destruct (Korder_branch_join n1 n2 m H H0) as [n [? ?]].
eapply sat_mono in H2; [| eassumption].
eapply sat_mono in H1; [| eassumption].
rewrite sat_impp in H2.
apply (H2 n) in H1; [| reflexivity].
apply sat_falsep in H1; auto.
