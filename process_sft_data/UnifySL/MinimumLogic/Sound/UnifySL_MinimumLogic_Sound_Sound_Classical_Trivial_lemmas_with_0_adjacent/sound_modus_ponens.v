Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Local Open Scope logic_base.
Local Open Scope syntax.
Section Sound.
Context {L: Language} {minL: MinimumLanguage L} {MD: Model} {SM: Semantics L MD} {tminSM: TrivialMinimumSemantics L MD SM}.
End Sound.

Lemma sound_modus_ponens: forall x y m, m |= (x --> y) -> m |= x -> m |= y.
Proof.
intros.
rewrite sat_impp in H.
apply H; auto.
