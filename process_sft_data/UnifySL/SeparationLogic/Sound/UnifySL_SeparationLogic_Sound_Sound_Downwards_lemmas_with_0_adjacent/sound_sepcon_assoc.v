Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Semantics.DownwardsSemantics.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Section Sound_Downwards.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {wandL: WandLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {J: Join (Kworlds M)} {SA: SeparationAlgebra (Kworlds M)} {dSA: DownwardsClosedSeparationAlgebra (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {kminSM: KripkeMinimumSemantics L MD M SM} {kpSM: KripkePropositionalSemantics L MD M SM} {dsepconSM: DownwardsSemantics.SepconSemantics L MD M SM} {dwandSM: DownwardsSemantics.WandSemantics L MD M SM}.
Context {empL: EmpLanguage L} {dempSM: DownwardsSemantics.EmpSemantics L MD M SM}.
End Sound_Downwards.

Lemma sound_sepcon_assoc: forall x y z: expr, forall m, KRIPKE: M, m |= x * (y * z) <--> (x * y) * z.
Proof.
intros.
unfold iffp.
rewrite sat_andp.
split; intros.
+
rewrite sat_impp; intros.
rewrite sat_sepcon in H0.
destruct H0 as [n' [mx' [myz' [? [? [? ?]]]]]].
rewrite sat_sepcon in H3.
destruct H3 as [myz'' [my'' [mz'' [? [? [? ?]]]]]].
apply join_comm in H1.
apply join_comm in H4.
assert (mx' <= mx') by reflexivity.
destruct (join_Korder_down _ _ _ _ _ H1 H3 H7) as [n'' [? ?]].
destruct (join_assoc mz'' my'' mx' myz'' n'' H4 H8) as [mxy'' [? ?]].
apply join_comm in H10.
apply join_comm in H11.
rewrite sat_sepcon.
exists n'', mxy'', mz''.
split; [| split; [| split]]; auto.
-
etransitivity; eauto.
-
rewrite sat_sepcon.
exists mxy'', mx', my''.
split; [| split; [| split]]; auto.
reflexivity.
+
rewrite sat_impp; intros.
rewrite sat_sepcon in H0.
destruct H0 as [n' [mxy' [mz' [? [? [? ?]]]]]].
rewrite sat_sepcon in H2.
destruct H2 as [mxy'' [mx'' [my'' [? [? [? ?]]]]]].
assert (mz' <= mz') by reflexivity.
destruct (join_Korder_down _ _ _ _ _ H1 H2 H7) as [n'' [? ?]].
destruct (join_assoc mx'' my'' mz' mxy'' n'' H4 H8) as [myz'' [? ?]].
rewrite sat_sepcon.
exists n'', mx'', myz''.
split; [| split; [| split]]; auto.
-
etransitivity; eauto.
-
rewrite sat_sepcon.
exists myz'', my'', mz'.
split; [| split; [| split]]; auto.
reflexivity.
