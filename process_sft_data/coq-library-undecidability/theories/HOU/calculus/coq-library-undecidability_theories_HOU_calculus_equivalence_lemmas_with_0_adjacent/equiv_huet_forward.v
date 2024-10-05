Set Implicit Arguments.
Require Import Morphisms Lia FinFun.
From Undecidability.HOU Require Import std.std.
From Undecidability.HOU.calculus Require Import prelim terms syntax semantics confluence.
Set Default Proof Using "Type".
Section Equivalence.
Context {X: Const}.
Notation "s ≡ t" := (equiv (@step X) s t) (at level 70).
Section CompatibilityProperties.
Global Instance equiv_lam_proper: Proper (equiv step ++> equiv step) (@lam X).
Proof.
intros ? ? (v & H1 & H2) % church_rosser; eauto.
rewrite H1, H2.
reflexivity.
Global Instance equiv_app_proper: Proper (equiv step ++> equiv step ++> equiv step) (@app X).
Proof.
intros ? ? (v & H1 & H2) % church_rosser ? ? (v' & H3 & H4) % church_rosser; eauto.
rewrite H1, H2, H3, H4.
reflexivity.
Global Instance ren_equiv_proper: Proper (eq ++> equiv step ++> equiv step) (@ren X).
Proof.
intros ? zeta -> s t H; now eapply ren_equiv.
Global Instance subst_equiv_proper: Proper (eq ++> equiv step ++> equiv step) (@subst_exp X).
Proof.
intros ? zeta -> s t H; now eapply subst_equiv.
End CompatibilityProperties.
Section InjectivityProperties.
End InjectivityProperties.
Section DisjointnessProperties.
End DisjointnessProperties.
Section HuetDefinition.
Variable (s t v1 v2: exp X).
Hypothesis (E1: s ▷ v1) (E2: t ▷ v2).
End HuetDefinition.
End Equivalence.
Notation "s ≡ t" := (equiv step s t) (at level 70).
Hint Resolve equiv_neq_var_app equiv_neq_var_lambda equiv_neq_var_const equiv_neq_const_app equiv_neq_const_lam equiv_neq_lambda_app : core.
Ltac ClearRefl H := let T := type of H in match T with | ?X ≡ ?X => clear H | _ => idtac end.
Ltac Injection H := let T := type of H in let H1 := fresh "H" in let H2 := fresh "H" in match T with | var _ ≡ var _ => eapply equiv_var_eq in H as H1; ClearRefl H1 | const _ ≡ const _ => eapply equiv_const_eq in H as H1; ClearRefl H1 | lambda _ ≡ lambda _ => eapply equiv_lam_elim in H as H1; ClearRefl H1 | app _ _ ≡ app _ _ => eapply equiv_app_elim in H as [H1 H2]; [| atom..]; ClearRefl H1; ClearRefl H2 end.
Ltac Discriminate := match goal with | [H: var _ ≡ const _ |- _] => eapply equiv_neq_var_const in H as [] | [H: const _ ≡ var _ |- _] => symmetry in H; eapply equiv_neq_var_const in H as [] | [H: var _ ≡ app _ _ |- _] => solve [eapply equiv_neq_var_app in H as []; atom] | [H: app _ _ ≡ var _ |- _] => solve [symmetry in H; eapply equiv_neq_var_app in H as []; atom] | [H: var _ ≡ lambda _ |- _] => eapply equiv_neq_var_lambda in H as [] | [H: lambda _ ≡ var _ |- _] => symmetry in H; eapply equiv_neq_var_lambda in H as [] | [H: const _ ≡ lambda _ |- _] => eapply equiv_neq_const_lam in H as [] | [H: lambda _ ≡ const _ |- _] => symmetry in H; eapply equiv_neq_const_lam in H as [] | [H: const _ ≡ app _ _ |- _] => solve [eapply equiv_neq_const_app in H as []; atom] | [H: app _ _ ≡ const _ |- _] => solve [symmetry in H; eapply equiv_neq_const_app in H as []; atom] | [H: lambda _ ≡ app _ _ |- _] => solve [eapply equiv_neq_lambda_app in H as []; atom] | [H: app _ _ ≡ lambda _ |- _] => solve [symmetry in H; eapply equiv_neq_lambda_app in H as []; atom] | [H: var _ ≡ var _ |- _] => solve [eapply equiv_var_eq in H as ?; discriminate] | [H: const _ ≡ const _ |- _] => solve [eapply equiv_const_eq in H as ?; discriminate] end.

Lemma equiv_huet_forward: s ≡ t -> v1 = v2.
Proof using E1 E2.
destruct E1 as [H1 N1], E2 as [H2 N2].
intros H; eapply equiv_unique_normal_forms; eauto.
now rewrite <-H1, <-H2.
