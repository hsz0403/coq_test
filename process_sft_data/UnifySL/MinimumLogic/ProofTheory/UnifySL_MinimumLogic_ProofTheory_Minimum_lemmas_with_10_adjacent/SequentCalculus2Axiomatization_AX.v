Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.TheoryOfSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfSequentCalculus.
Local Open Scope logic_base.
Local Open Scope syntax.
Definition multi_imp {L: Language} {minL: MinimumLanguage L} (xs: list expr) (y: expr): expr := fold_right impp y xs.
Class NormalAxiomatization (L: Language) {minL: MinimumLanguage L} (GammaP: Provable L) (GammaD: Derivable L): Type := { derivable_provable: forall Phi y, derivable Phi y <-> exists xs, Forall (fun x => Phi x) xs /\ provable (multi_imp xs y) }.
Class MinimumAxiomatization (L: Language) {minL: MinimumLanguage L} (Gamma: Provable L) := { modus_ponens: forall x y, |-- (x --> y) -> |-- x -> |-- y; axiom1: forall x y, |-- (x --> (y --> x)); axiom2: forall x y z, |-- ((x --> y --> z) --> (x --> y) --> (x --> z)) }.
Class MinimumSequentCalculus (L: Language) {minL: MinimumLanguage L} (Gamma: Derivable L) := { deduction_modus_ponens: forall Phi x y, Phi |-- x -> Phi |-- x --> y -> Phi |-- y; deduction_impp_intros: forall Phi x y, Phi;; x |-- y -> Phi |-- x --> y }.
Section DerivableRulesFromAxiomatization.
Context {L: Language} {minL: MinimumLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma}.
End DerivableRulesFromAxiomatization.
Section DerivableRules_multi_impp.
Context {L: Language} {minL: MinimumLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma}.
End DerivableRules_multi_impp.
Section Axiomatization2SequentCalculus.
Context {L: Language} {minL: MinimumLanguage L} {GammaP: Provable L} {GammaD: Derivable L} {AX: NormalAxiomatization L GammaP GammaD}.
Context {minAX: MinimumAxiomatization L GammaP}.
End Axiomatization2SequentCalculus.
Section DerivableRulesFromSequentCalculus.
Context {L: Language} {GammaD: Derivable L} {bSC: BasicSequentCalculus L GammaD}.
Context {minL: MinimumLanguage L} {minSC: MinimumSequentCalculus L GammaD}.
End DerivableRulesFromSequentCalculus.
Section SequentCalculus2Axiomatization.
Context {L: Language} {GammaP: Provable L} {GammaD: Derivable L} {minL: MinimumLanguage L} {SC: NormalSequentCalculus L GammaP GammaD} {bSC: BasicSequentCalculus L GammaD} {minSC: MinimumSequentCalculus L GammaD}.
End SequentCalculus2Axiomatization.
Section Transformation.
Context {L: Language} {minL: MinimumLanguage L}.
Definition Provable2Derivable {GammaP: Provable L}: Derivable L := Build_Derivable L (fun Phi y => exists xs, Forall (fun x => Phi x) xs /\ |-- multi_imp xs y).
Definition Provable2Derivable_Normal {GammaP: Provable L}: NormalAxiomatization L GammaP Provable2Derivable := Build_NormalAxiomatization L minL GammaP Provable2Derivable (fun _ _ => iff_refl _).
Definition Derivable2Provable {GammaD: Derivable L}: Provable L := Build_Provable L (fun x => (Empty_set _) |-- x).
Definition Derivable2Provable_Normal {GammaD: Derivable L}: NormalSequentCalculus L Derivable2Provable GammaD := Build_NormalSequentCalculus L Derivable2Provable GammaD (fun _ => iff_refl _).
End Transformation.

Theorem deduction_theorem: forall (Phi: context) (x y: expr), Union _ Phi (Singleton _ x) |-- y <-> Phi |-- x --> y.
Proof.
intros; split.
+
apply deduction_impp_intros; auto.
+
Admitted.

Theorem deduction_theorem_multi_imp: forall (Phi: context) (xs: list expr) (y: expr), Union _ Phi (fun x => In x xs) |-- y <-> Phi |-- multi_imp xs y.
Proof.
intros.
revert Phi; induction xs; intros.
+
simpl.
split; apply deduction_weaken; unfold Included, Ensembles.In; intros.
-
rewrite Union_spec in H.
tauto.
-
rewrite Union_spec.
tauto.
+
simpl.
rewrite <- deduction_theorem, <- IHxs.
split; apply deduction_weaken; unfold Included, Ensembles.In; intros.
-
rewrite Union_spec in H.
rewrite !Union_spec, Singleton_spec.
tauto.
-
rewrite !Union_spec, Singleton_spec in H.
rewrite !Union_spec.
Admitted.

Lemma derivable_impp_refl: forall (Phi: context) (x: expr), Phi |-- x --> x.
Proof.
intros.
apply deduction_theorem.
Admitted.

Lemma deduction_left_impp_intros: forall (Phi: context) (x y: expr), Phi |-- x -> Phi |-- y --> x.
Proof.
intros.
apply deduction_theorem.
Admitted.

Lemma derivable_axiom1: forall (Phi: context) (x y: expr), Phi |-- x --> y --> x.
Proof.
intros.
rewrite <- !deduction_theorem.
Admitted.

Lemma derivable_axiom2: forall (Phi: context) (x y z: expr), Phi |-- (x --> y --> z) --> (x --> y) --> (x --> z).
Proof.
intros.
rewrite <- !deduction_theorem.
apply deduction_modus_ponens with y.
+
apply deduction_modus_ponens with x; solve_assum.
+
Admitted.

Lemma derivable_modus_ponens: forall (Phi: context) (x y: expr), Phi |-- x --> (x --> y) --> y.
Proof.
intros.
rewrite <- !deduction_theorem.
Admitted.

Lemma deduction_impp_trans: forall (Phi: context) (x y z: expr), Phi |-- x --> y -> Phi |-- y --> z -> Phi |-- x --> z.
Proof.
intros.
rewrite <- deduction_theorem in H |- *.
Admitted.

Lemma deduction_impp_arg_switch: forall (Phi: context) (x y z: expr), Phi |-- x --> y --> z -> Phi |-- y --> x --> z.
Proof.
intros.
rewrite <- !deduction_theorem in *.
eapply deduction_weaken; [| exact H].
intros ? ?.
destruct H0; [destruct H0 |].
+
left; left; auto.
+
right; auto.
+
Admitted.

Theorem SequentCalculus2Axiomatization_minAX: MinimumAxiomatization L GammaP.
Proof.
constructor.
+
intros x y.
rewrite !provable_derivable.
intros.
eapply deduction_modus_ponens; eauto.
+
intros x y.
rewrite provable_derivable.
apply derivable_axiom1.
+
intros x y z.
rewrite provable_derivable.
Admitted.

Theorem SequentCalculus2Axiomatization_AX {fwSC: FiniteWitnessedSequentCalculus L GammaD}: NormalAxiomatization L GammaP GammaD.
Proof.
constructor; intros.
split; intros.
+
apply derivable_finite_witnessed in H.
destruct H as [xs [? ?]]; exists xs.
split; auto.
apply provable_derivable.
apply deduction_theorem_multi_imp.
eapply deduction_weaken; eauto.
apply right_Included_Union.
+
destruct H as [xs [? ?]].
apply provable_derivable in H0.
apply deduction_theorem_multi_imp in H0.
eapply deduction_weaken; eauto.
unfold Included, Ensembles.In; intros.
rewrite Union_spec in H1.
destruct H1 as [[] |].
revert x H1.
rewrite Forall_forall in H; auto.
