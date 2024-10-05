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
Require Import Logic.SeparationLogic.Semantics.UpwardsSemantics.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Section Sound_Upwards.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {wandL: WandLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {J: Join (Kworlds M)} {SA: SeparationAlgebra (Kworlds M)} {dSA: DownwardsClosedSeparationAlgebra (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {kminSM: KripkeMinimumSemantics L MD M SM} {kpSM: KripkePropositionalSemantics L MD M SM} {usepconSM: UpwardsSemantics.SepconSemantics L MD M SM} {uwandSM: UpwardsSemantics.WandSemantics L MD M SM}.
Context {empL: EmpLanguage L} {uempSM: UpwardsSemantics.EmpSemantics L MD M SM}.
End Sound_Upwards.

Lemma sound_wand_sepcon_adjoint: forall x y z: expr, (forall m, KRIPKE: M, m |= x * y --> z) <-> (forall m, KRIPKE: M, m |= x --> (y -* z)).
Proof.
intros.
split; intro.
+
assert (ASSU: forall m1 m2 m, join m1 m2 m -> KRIPKE: M, m1 |= x -> KRIPKE: M, m2 |= y -> KRIPKE: M, m |= z).
{
intros.
specialize (H m).
rewrite sat_impp in H.
apply (H m); [reflexivity |].
rewrite sat_sepcon.
exists m1, m2; auto.
}
clear H.
intros.
rewrite sat_impp; intros.
rewrite sat_wand; intros.
apply (ASSU m0 m1 m2); auto.
eapply sat_mono; eauto.
+
assert (ASSU: forall m0 m1 m2 m, m <= m0 -> join m0 m1 m2 -> KRIPKE: M, m |= x -> KRIPKE: M, m1 |= y -> KRIPKE: M, m2 |= z).
{
intros.
specialize (H m).
rewrite sat_impp in H.
revert m0 m1 m2 H0 H1 H3.
rewrite <- sat_wand.
apply (H m); [reflexivity | auto].
}
intros.
rewrite sat_impp; intros.
rewrite sat_sepcon in H1.
destruct H1 as [m1 [m2 [? [? ?]]]].
apply (ASSU m1 m2 n m1); auto.
reflexivity.
