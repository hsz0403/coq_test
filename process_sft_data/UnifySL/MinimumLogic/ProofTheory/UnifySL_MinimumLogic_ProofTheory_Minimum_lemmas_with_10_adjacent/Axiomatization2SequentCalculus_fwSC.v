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

Lemma provable_impp_trans: forall (x y z: expr), |-- (x --> y) --> (y --> z) --> (x --> z).
Proof.
intros.
pose proof provable_impp_arg_switch (y --> z) (x --> y) (x --> z).
eapply modus_ponens; eauto.
clear H.
Admitted.

Lemma provable_multi_imp_shrink: forall (xs: list expr) (x y: expr), |-- (x --> multi_imp xs (x --> y)) --> multi_imp xs (x --> y).
Proof.
intros.
induction xs.
+
simpl.
apply aux_minimun_theorem04.
+
simpl.
apply aux_minimun_rule01 with (z := a) in IHxs.
eapply aux_minimun_rule02; [| eauto].
Admitted.

Lemma provable_multi_imp_arg_switch1: forall (xs: list expr) (x y: expr), |-- (x --> multi_imp xs y) --> multi_imp xs (x --> y).
Proof.
intros.
induction xs.
+
simpl.
apply provable_impp_refl.
+
simpl.
apply aux_minimun_rule02 with (a --> x --> multi_imp xs y).
-
apply provable_impp_arg_switch.
-
Admitted.

Lemma provable_multi_imp_arg_switch2: forall (xs: list expr) (x y: expr), |-- multi_imp xs (x --> y) --> (x --> multi_imp xs y).
Proof.
intros.
induction xs.
+
simpl.
apply provable_impp_refl.
+
simpl.
apply aux_minimun_rule02 with (a --> x --> multi_imp xs y).
-
apply aux_minimun_rule01; auto.
-
Admitted.

Lemma provable_multi_imp_weaken: forall (xs: list expr) (x y: expr), |-- x --> y -> |-- multi_imp xs x --> multi_imp xs y.
Proof.
intros.
induction xs.
+
auto.
+
Admitted.

Lemma provable_multi_imp_split: forall Phi1 Phi2 (xs: list expr) (y: expr), Forall (Union _ Phi1 Phi2) xs -> |-- multi_imp xs y -> exists xs1 xs2, Forall Phi1 xs1 /\ Forall Phi2 xs2 /\ |-- multi_imp xs1 (multi_imp xs2 y).
Proof.
intros.
revert y H0; induction H.
+
exists nil, nil.
split; [| split]; [constructor .. | auto].
+
intros.
specialize (IHForall (x --> y)).
eapply modus_ponens in H1; [| simpl; apply provable_multi_imp_arg_switch1].
specialize (IHForall H1); clear H1.
destruct IHForall as [xs1 [xs2 [? [? ?]]]].
destruct H.
-
exists (x :: xs1), xs2.
split; [constructor | split]; auto.
simpl; eapply modus_ponens; [apply provable_multi_imp_arg_switch2 |].
eapply modus_ponens; [apply provable_multi_imp_weaken | exact H3].
apply provable_multi_imp_arg_switch2.
-
exists xs1, (x :: xs2).
split; [| split; [constructor | ]]; auto.
eapply modus_ponens; [apply provable_multi_imp_weaken | exact H3].
Admitted.

Lemma provable_add_multi_imp_left_head: forall xs1 xs2 y, |-- multi_imp xs2 y --> multi_imp (xs1 ++ xs2) y.
Proof.
intros.
induction xs1.
+
apply provable_impp_refl.
+
eapply aux_minimun_rule02; eauto.
Admitted.

Lemma provable_add_multi_imp_left_tail: forall xs1 xs2 y, |-- multi_imp xs1 y --> multi_imp (xs1 ++ xs2) y.
Proof.
intros.
induction xs1; simpl.
+
pose proof (provable_add_multi_imp_left_head xs2 nil y).
rewrite app_nil_r in H; auto.
+
Admitted.

Lemma provable_multi_imp_modus_ponens: forall xs y z, |-- multi_imp xs y --> multi_imp xs (y --> z) --> multi_imp xs z.
Proof.
intros.
induction xs; simpl.
+
apply aux_minimun_theorem02.
+
eapply aux_minimun_rule02; [| apply provable_impp_arg_switch].
eapply aux_minimun_rule02; [| apply aux_minimun_theorem04].
apply aux_minimun_rule01.
eapply aux_minimun_rule02; [eauto |].
eapply aux_minimun_rule02; [| apply provable_impp_arg_switch].
Admitted.

Lemma Axiomatization2SequentCalculus_SC: NormalSequentCalculus L GammaP GammaD.
Proof.
constructor.
intros.
rewrite derivable_provable.
split; intros.
+
exists nil; split; auto.
+
destruct H as [xs [? ?]].
destruct xs; [auto |].
inversion H; subst.
Admitted.

Lemma Axiomatization2SequentCalculus_minSC: MinimumSequentCalculus L GammaD.
Proof.
constructor.
+
intros.
rewrite derivable_provable in H, H0 |- *.
destruct H as [xs1 [? ?]], H0 as [xs2 [? ?]].
exists (xs1 ++ xs2); split.
-
rewrite Forall_app_iff; auto.
-
pose proof modus_ponens _ _ (provable_add_multi_imp_left_tail xs1 xs2 _) H1.
pose proof modus_ponens _ _ (provable_add_multi_imp_left_head xs1 xs2 _) H2.
pose proof provable_multi_imp_modus_ponens (xs1 ++ xs2) x y.
pose proof modus_ponens _ _ H5 H3.
pose proof modus_ponens _ _ H6 H4.
auto.
+
intros.
rewrite derivable_provable in H |- *.
destruct H as [xs [? ?]].
pose proof provable_multi_imp_split _ _ _ _ H H0 as [xs1 [xs2 [? [? ?]]]].
exists xs1.
split; auto.
eapply modus_ponens; [| exact H3].
apply provable_multi_imp_weaken.
clear - H2 minAX.
induction H2.
-
apply axiom1.
-
inversion H; subst x0; clear H.
simpl.
pose proof aux_minimun_theorem04 x y.
pose proof aux_minimun_rule01 _ _ x IHForall.
Admitted.

Lemma Axiomatization2SequentCalculus_bSC: BasicSequentCalculus L GammaD.
Proof.
assert (DW: DeductionWeaken L GammaD).
{
hnf; intros.
rewrite derivable_provable in H0 |- *.
destruct H0 as [xs [? ?]].
exists xs; split; auto.
revert H0; apply Forall_impl.
auto.
}
constructor; auto.
+
intros.
rewrite derivable_provable.
exists (x :: nil); split.
-
constructor; auto.
-
simpl.
apply provable_impp_refl.
+
apply DeductionWeaken_ContextualDerivableFiniteWitnessed_DeductionSubst1_2_DeductionSubst.
-
exact DW.
-
apply DeductionWeaken_DerivableFiniteWitnessed_2_ContextualDerivableFiniteWitnessed.
*
exact DW.
*
exact (@derivable_finite_witnessed _ _ Axiomatization2SequentCalculus_fwSC).
-
apply DeductionImpIntro_DeductionMP_2_DeductionSubst1.
*
exact (@deduction_impp_intros _ _ _ Axiomatization2SequentCalculus_minSC).
*
Admitted.

Lemma deduction_impp_elim: forall Phi x y, Phi |-- impp x y -> Union _ Phi (Singleton _ x) |-- y.
Proof.
intros.
Admitted.

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

Lemma Axiomatization2SequentCalculus_fwSC: FiniteWitnessedSequentCalculus L GammaD.
Proof.
constructor.
hnf; intros.
rewrite derivable_provable in H.
destruct H as [xs [? ?]].
exists xs.
split; auto.
rewrite derivable_provable.
exists xs.
split; auto.
rewrite Forall_forall; auto.
