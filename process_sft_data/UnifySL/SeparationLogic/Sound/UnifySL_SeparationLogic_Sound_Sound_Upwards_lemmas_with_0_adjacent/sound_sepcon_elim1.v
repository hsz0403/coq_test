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

Lemma sound_sepcon_elim1 {incrSA: IncreasingSeparationAlgebra (Kworlds M)}: forall x y: expr, forall m, KRIPKE: M, m |= x * y --> x.
Proof.
intros.
rewrite sat_impp; intros.
rewrite sat_sepcon in H0.
destruct H0 as [m1 [m2 [? [? ?]]]].
apply join_comm in H0.
apply all_increasing in H0.
eapply sat_mono; eauto.
