Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.ModalLogic.Model.OrderedKripkeModel.
Require Import Logic.ModalLogic.Semantics.Flat.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Section Sound_Flat.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {po_R1: PreOrder KI.Krelation} {R2: KM.Relation (Kworlds M)} {ukmM: UpwardsClosedOrderedKripkeModel (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {kminSM: KripkeMinimumSemantics L MD M SM} {kpSM: KripkePropositionalSemantics L MD M SM} {fmSM: FlatModalSemantics L MD M SM}.
End Sound_Flat.

Lemma sound_boxp_orp {pf_R2: PartialFunctional KM.Krelation}: forall x y (m: Kworlds M), KRIPKE: M, m |= boxp (x || y) <--> (boxp x || boxp y).
Proof.
intros.
unfold iffp.
rewrite sat_andp, !sat_impp.
split; intros ? ?.
+
clear m H.
rewrite sat_orp.
rewrite !sat_boxp.
intros; apply NNPP.
intro.
apply not_or_and in H0; destruct H0.
apply not_all_ex_not in H0; destruct H0 as [n1 ?].
apply not_all_ex_not in H1; destruct H1 as [n2 ?].
apply imply_to_and in H0; destruct H0.
apply imply_to_and in H1; destruct H1.
pose proof partial_functionality _ _ _ H0 H1.
subst n2; clear H1.
specialize (H _ H0).
rewrite sat_orp in H.
tauto.
+
rewrite sat_orp, !sat_boxp.
intros; rewrite sat_orp.
destruct H0; [left | right]; auto.
