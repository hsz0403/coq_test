Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Section Sound.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {MD: Model} {SM: Semantics L MD} {tminSM: TrivialMinimumSemantics L MD SM} {tpSM: TrivialPropositionalSemantics L MD SM}.
End Sound.

Lemma sound_orp_elim: forall x y z m, m |= (x --> z) --> (y --> z) --> (x || y --> z).
Proof.
intros.
rewrite !sat_impp, sat_orp.
tauto.
