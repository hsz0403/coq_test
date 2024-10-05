Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Syntax.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Module Semantics.
Definition andp {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model := fun m => X m /\ Y m.
Definition orp {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model := fun m => X m \/ Y m.
Definition falsep {model: Type}: Ensemble model := fun m => False.
End Semantics.
Class TrivialPropositionalSemantics (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} (MD: Model) (SM: Semantics L MD): Type := { denote_andp: forall x y, Same_set _ (denotation (x && y)) (Semantics.andp (denotation x) (denotation y)); denote_orp: forall x y, Same_set _ (denotation (x || y)) (Semantics.orp (denotation x) (denotation y)); denote_falsep: Same_set _ (denotation FF) Semantics.falsep }.
Section Trivial.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {MD: Model} {SM: Semantics L MD} {tpSM: TrivialPropositionalSemantics L MD SM}.
End Trivial.

Lemma sat_falsep: forall m, m |= FF <-> False.
Proof.
intros; simpl.
unfold satisfies.
destruct denote_falsep.
split; auto; [apply H | apply H0].
