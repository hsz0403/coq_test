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

Lemma sound_rule_N: forall x, (forall (m: Kworlds M), KRIPKE: M, m |= x) -> (forall (m: Kworlds M), KRIPKE: M, m |= boxp x).
Proof.
intros.
rewrite sat_boxp.
intros; apply H; auto.
