Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Class GodelDummettPropositionalLogic (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {ipAX: IntuitionisticPropositionalLogic L Gamma} := { impp_choice: forall x y, |-- (x --> y) || (y --> x) }.
Section GodelDummett.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {ipAX: IntuitionisticPropositionalLogic L Gamma} {gdpAX: GodelDummettPropositionalLogic L Gamma}.
Instance GodelDummett2DeMorgan: DeMorganPropositionalLogic L Gamma.
Proof.
constructor.
AddSequentCalculus.
intros.
rewrite provable_derivable.
set (Phi := empty_context).
clearbody Phi.
pose proof impp_choice x (~~ x).
apply deduction_weaken0 with (Phi0 := Phi) in H.
assert (Phi |-- (x --> ~~ x) --> (x --> FF)).
{
rewrite <- deduction_theorem.
rewrite <- deduction_theorem.
eapply deduction_weaken with (Union _ (Union _ (Union _ Phi (Singleton _ (x --> ~~ x))) (Singleton _ x)) (Singleton _ x)).
+
intros y ?.
destruct H0; [| right; auto].
destruct H0; [| right; auto].
left; auto.
+
rewrite deduction_theorem.
rewrite deduction_theorem.
apply derivable_assum1.
}
assert (Phi |-- (~~ x --> x) --> (~~ x --> FF)).
{
rewrite <- deduction_theorem.
pose proof derivable_assum1 Phi (~~ x --> x).
set (Psi := Union expr Phi (Singleton expr (~~ x --> x))) in H1 |- *; clearbody Psi.
rewrite <- deduction_theorem in H1 |- *.
pose proof derivable_assum1 Psi (~~ x).
pose proof deduction_modus_ponens _ _ _ H1 H2.
auto.
}
rewrite <- deduction_theorem in H0, H1.
apply (deduction_orp_intros1 _ _ (~~ x --> FF)) in H0.
apply (deduction_orp_intros2 _ (x --> FF)) in H1.
rewrite deduction_theorem in H0, H1.
pose proof deduction_orp_elim' _ _ _ _ H0 H1.
pose proof deduction_modus_ponens _ _ _ H H2.
auto.
End GodelDummett.

Instance GodelDummett2DeMorgan: DeMorganPropositionalLogic L Gamma.
Proof.
constructor.
AddSequentCalculus.
intros.
rewrite provable_derivable.
set (Phi := empty_context).
clearbody Phi.
pose proof impp_choice x (~~ x).
apply deduction_weaken0 with (Phi0 := Phi) in H.
assert (Phi |-- (x --> ~~ x) --> (x --> FF)).
{
rewrite <- deduction_theorem.
rewrite <- deduction_theorem.
eapply deduction_weaken with (Union _ (Union _ (Union _ Phi (Singleton _ (x --> ~~ x))) (Singleton _ x)) (Singleton _ x)).
+
intros y ?.
destruct H0; [| right; auto].
destruct H0; [| right; auto].
left; auto.
+
rewrite deduction_theorem.
rewrite deduction_theorem.
apply derivable_assum1.
}
assert (Phi |-- (~~ x --> x) --> (~~ x --> FF)).
{
rewrite <- deduction_theorem.
pose proof derivable_assum1 Phi (~~ x --> x).
set (Psi := Union expr Phi (Singleton expr (~~ x --> x))) in H1 |- *; clearbody Psi.
rewrite <- deduction_theorem in H1 |- *.
pose proof derivable_assum1 Psi (~~ x).
pose proof deduction_modus_ponens _ _ _ H1 H2.
auto.
}
rewrite <- deduction_theorem in H0, H1.
apply (deduction_orp_intros1 _ _ (~~ x --> FF)) in H0.
apply (deduction_orp_intros2 _ (x --> FF)) in H1.
rewrite deduction_theorem in H0, H1.
pose proof deduction_orp_elim' _ _ _ _ H0 H1.
pose proof deduction_modus_ponens _ _ _ H H2.
auto.
