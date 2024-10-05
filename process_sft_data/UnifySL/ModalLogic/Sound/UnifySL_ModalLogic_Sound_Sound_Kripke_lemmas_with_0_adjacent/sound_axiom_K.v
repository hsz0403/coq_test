Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.ModalLogic.Model.OrderedKripkeModel.
Require Import Logic.ModalLogic.Semantics.Kripke.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.
Import KripkeModelFamilyNotation.
Section Sound_Kripke.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {SM: Semantics L MD} {tminSM: TrivialMinimumSemantics L MD SM} {tpSM: TrivialPropositionalSemantics L MD SM} {kmSM: KripkeModalSemantics L MD M SM}.
End Sound_Kripke.

Lemma sound_axiom_K: forall x y (m: Kworlds M), KRIPKE: M, m |= boxp (x --> y) --> (boxp x --> boxp y).
Proof.
intros.
rewrite !sat_impp, !sat_boxp.
intros.
specialize (H _ H1).
specialize (H0 _ H1).
rewrite sat_impp in H.
auto.
