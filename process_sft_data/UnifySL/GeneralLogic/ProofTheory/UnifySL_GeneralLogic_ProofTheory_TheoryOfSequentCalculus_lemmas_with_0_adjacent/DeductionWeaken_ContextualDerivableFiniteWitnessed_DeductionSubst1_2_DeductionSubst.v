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

Lemma DeductionWeaken_ContextualDerivableFiniteWitnessed_DeductionSubst1_2_DeductionSubst: DeductionWeaken L Gamma -> ContextualDerivableFiniteWitnessed L Gamma -> DeductionSubst1 L Gamma -> DeductionSubst L Gamma.
Proof.
intros; hnf; intros.
apply H0 in H3.
destruct H3 as [xs [? ?]].
eapply Forall_impl in H3; [| exact H2]; clear H2.
induction H3.
+
eapply H; eauto.
unfold Included, Ensembles.In; intro; rewrite Union_spec; simpl; tauto.
+
apply IHForall.
apply H1 with x.
-
eapply H; eauto.
unfold Included, Ensembles.In; intro; rewrite Union_spec; simpl; tauto.
-
eapply H; eauto.
unfold Included, Ensembles.In; intro; rewrite !Union_spec; simpl.
intros [? | [? | ?]]; auto.
right; subst; constructor.
