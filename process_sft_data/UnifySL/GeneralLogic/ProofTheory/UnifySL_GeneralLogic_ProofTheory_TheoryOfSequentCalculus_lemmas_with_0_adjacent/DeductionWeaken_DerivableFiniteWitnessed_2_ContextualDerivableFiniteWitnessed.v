Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Local Open Scope logic_base.
Section PropertiesOfSequentCalculus.
Context (L: Language) (Gamma: Derivable L).
Definition DerivableRefl: Prop := forall x: expr, empty_context;; x |-- x.
Definition DeductionWeaken: Prop := forall (Phi Psi: context) (x: expr), Included _ Phi Psi -> Phi |-- x -> Psi |-- x.
Definition DerivableAssu: Prop := forall (Phi: context) (x: expr), Ensembles.In _ Phi x -> Phi |-- x.
Definition DeductionSubst1: Prop := forall (Phi: context) (x y: expr), Phi |-- x -> Phi;; x |-- y -> Phi |-- y.
Definition DeductionSubst: Prop := forall (Phi Psi: context) (y: expr), (forall x, Psi x -> Phi |-- x) -> Union _ Phi Psi |-- y -> Phi |-- y.
Definition DerivableFiniteWitnessed: Prop := forall (Phi: context) (y: expr), Phi |-- y -> exists xs, Forall Phi xs /\ (fun x => In x xs) |-- y.
Definition ContextualDerivableFiniteWitnessed: Prop := forall (Phi Psi: context) (y: expr), Union _ Phi Psi |-- y -> exists xs, Forall Psi xs /\ Union _ Phi (fun x => In x xs) |-- y.
End PropertiesOfSequentCalculus.
Section TheoryOfSequentCalculus.
Context {L: Language} {Gamma: Derivable L}.
End TheoryOfSequentCalculus.

Lemma DeductionWeaken_DerivableFiniteWitnessed_2_ContextualDerivableFiniteWitnessed: DeductionWeaken L Gamma -> DerivableFiniteWitnessed L Gamma -> ContextualDerivableFiniteWitnessed L Gamma.
Proof.
intros.
hnf; intros.
apply H0 in H1; clear H0.
destruct H1 as [xs [? ?]].
assert (exists xs', (forall x, In x xs -> Phi x \/ In x xs') /\ forall x, In x xs' -> Psi x).
+
clear H1.
induction H0.
-
exists nil.
split; simpl; intros; tauto.
-
destruct IHForall as [xs' [? ?]].
rewrite Union_spec in H0; destruct H0; [exists xs' | exists (x :: xs')]; split; intros.
*
destruct H4; [subst; auto |].
apply H2; auto.
*
apply H3; auto.
*
destruct H4; [simpl; auto |].
apply H2 in H4.
simpl; tauto.
*
destruct H4; [subst; auto |].
apply H3; auto.
+
destruct H2 as [xs' [? ?]].
exists xs'.
split.
-
rewrite Forall_forall; auto.
-
eapply H; eauto.
unfold Included, Ensembles.In; intro; rewrite Union_spec; auto.
