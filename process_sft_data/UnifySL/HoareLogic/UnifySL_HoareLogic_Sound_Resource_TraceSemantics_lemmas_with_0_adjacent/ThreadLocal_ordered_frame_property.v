Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.OSAExamples.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.BigStepSemantics.
Require Import Logic.HoareLogic.TraceSemantics.
Require Import Logic.HoareLogic.HoareTriple_BigStepSemantics.
Require Import Logic.HoareLogic.GuardedHoareTriple_TraceSemantics.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelSingleNotation.
Import KripkeModelNotation_Intuitionistic.
Section soundness.
Existing Instance unit_kMD.
Context {P: ProgrammingLanguage} {MD: Model} {J: Join model} {SA: SeparationAlgebra model} {R: Relation model} {po_R: PreOrder Krelation} {DCSA: DownwardsClosedSeparationAlgebra model} {UCSA: UpwardsClosedSeparationAlgebra model} {Res: Resource} {Ac: Action} {Acr: Action_resource Ac Res} {nAcr: NormalAction_resource Ac Res} {TS: TraceSemantics P (resources * model) Ac} {AIr: ActionInterpret_resource model Ac Res ac_sem} {SAAIr: @SAActionInterpret_resource (resources * model) Ac ac_sem (@prod_Join _ _ (Pred_Join resource) J) (fun a => ~ is_resources_action a)} {KAIr: @KActionInterpret_resource (resources * model) Ac ac_sem (RelProd (discPred_R resource) R)}.
Instance KSAAIr: @KSAActionInterpret_resource (resources * model) Ac ac_sem (@prod_Join _ _ (Pred_Join resource) J) (RelProd (discPred_R resource) R) (fun a => ~ is_resources_action a) := ordered_and_frame_AIr _ _ _.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD tt SM} {fsepconSM: FlatSemantics.SepconSemantics L MD tt SM}.
Class LegalInvariants (Inv: resource * (model -> Prop) -> Prop): Prop := { at_most_one_invariant: forall r I1 I2, Inv (r, I1) -> Inv (r, I2) -> I1 = I2; invariant_mono: forall r I, Inv (r, I) -> forall s1 s2, I s1 -> s1 <= s2 -> I s2; invariant_precise: forall r I, Inv (r, I) -> forall s, (exists s', (fun s' => exists f, I f /\ join s' f s) s') -> (exists s', greatest (fun s' => exists f, I f /\ join s' f s) s') }.
End soundness.

Lemma ThreadLocal_ordered_frame_property (Inv: resource * (model -> Prop) -> Prop) {INV: LegalInvariants Inv}: forall (a: action) (m1 f n1' n1: resources * model) (n2: MetaState (resources * model)) fst_m2 (ASSU: res_enable a (fst m1) fst_m2 (fst f) (*forall r, a = Arelease_res r -> ~ fst f r*)), @join _ (prod_Join _ _) m1 f n1' -> (RelProd (discPred_R _) R) n1' n1 -> thread_local_state_enable Inv a n1 n2 -> exists m2 n2', @lift_join _ (prod_Join _ _) m2 (Terminating f) n2' /\ @Partial.forward _ (RelProd (discPred_R _) R) n2' n2 /\ match m2 with Terminating m2 => fst m2 = fst_m2 | _ => True end /\ thread_local_state_enable Inv a m1 m2.
Proof.
intros.
destruct (classic (is_resources_action a)) as [[?r [? | ?]] | ?].
+
subst a.
inversion H1; subst; solve_resource_action.
rename m into n1, n into n2.
destruct n1' as [A1' n1'], f as [Af f], m1 as [B1 m1].
hnf in H; simpl in H; destruct H.
hnf in H0; simpl in H0.
destruct H0.
hnf in H0, H7; simpl in H0, H7.
pose proof join_Korder_down _ _ _ _ _ H6 H7 ltac:(reflexivity) as [n2' [? ?]].
pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ H2) H8 as [m2 [? ?]].
assert (A1 = A1').
{
extensionality r0; apply prop_ext.
apply iff_sym, H0.
}
subst A1'.
pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ H) H3 as [B2 [? ?]].
exists (Terminating (B2, m2)), (Terminating (A2, n2')).
split; [| split; [| split]].
-
constructor.
split; apply join_comm; auto.
-
constructor; split; auto; simpl.
hnf; intro; simpl; hnf; tauto.
-
apply res_enable_acq_inv in ASSU.
simpl in ASSU; destruct ASSU as [? _].
simpl; clear - H14 H12.
extensionality r0; apply prop_ext.
specialize (H12 r0); specialize (H14 r0); destruct H12, H14; tauto.
-
simpl.
eapply thread_local_state_enable_acq; eauto.
+
subst a.
destruct n1 as [A1 n1], n1' as [A1' n1'], f as [Af f], m1 as [B1 m1].
hnf in H; simpl in H; destruct H.
hnf in H0; unfold RelCompFun in H0; simpl in H0; destruct H0.
assert (A1' = A1).
{
extensionality r0; apply prop_ext.
apply H0.
}
subst A1'; clear H0.
destruct (classic (forall I, Inv (r, I) -> exists m2, (fun m2 => exists f, I f /\ join m2 f m1) m2)).
-
inversion H1; subst; solve_resource_action.
2: {
exfalso.
specialize (H0 _ H8).
destruct H0 as [m2 [f0 [? ?]]].
pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ H4) H2 as [n2' [? ?]].
pose proof join_Korder_up _ _ _ _ H6 H3 as [_f0 [n2 [? [? ?]]]].
apply (H10 n2); clear H10.
exists _f0; split; [eapply (invariant_mono _ _ H8); eauto | apply join_comm; auto].
}
specialize (H0 _ H8).
apply (invariant_precise _ _ H8) in H0.
destruct H0 as [m2 ?].
destruct (proj1 H0) as [f0 [? ?]].
pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ H5) H2 as [n2' [? ?]].
pose proof join_Korder_up _ _ _ _ H9 H3 as [_f0 [_n2 [? [? ?]]]].
assert ((fun n : model => exists f : model, I f /\ join n f n1) _n2).
{
exists _f0; split; [eapply (invariant_mono _ _ H8); eauto | apply join_comm; auto].
}
apply (proj2 H10) in H14.
apply res_enable_rel_inv in ASSU; simpl in ASSU.
rename fst_m2 into B2.
exists (Terminating (B2, m2)), (Terminating (A2, n2')).
split; [| split; [| split]].
*
constructor.
split; auto.
simpl.
clear - ASSU H H7.
intros r0; specialize (ASSU r0); specialize (H r0); specialize (H7 r0).
destruct ASSU, H, H7; split; tauto.
*
constructor.
split; [hnf; intros ?; hnf; tauto | change (n2' <= n); etransitivity; eauto].
*
auto.
*
simpl.
eapply thread_local_state_enable_rel_succ; eauto.
-
exists Error, n2.
split; [| split; [| split]].
*
constructor.
*
destruct n2; constructor.
destruct p as [A2 n2].
split; [hnf; intros ?; hnf; tauto | change (n2 <= n2); reflexivity].
*
auto.
*
apply Classical_Pred_Type.not_all_ex_not in H0; destruct H0 as [I ?].
apply imply_to_and in H0; destruct H0.
apply res_enable_rel_inv in ASSU; simpl in ASSU.
eapply thread_local_state_enable_rel_fail; eauto.
+
rewrite <- (thread_local_state_enable_non_resource_action Inv) in H1 by auto.
change ((fun a => ~ is_resources_action a) a) in H2.
pose proof ordered_frame_property _ _ _ _ _ _ H2 H H0 H1 as [m2 [n2' [? [? ?]]]].
exists m2, n2'.
split; [| split; [| split]]; auto.
-
apply res_enable_not_res_inv in ASSU; auto.
destruct m1 as [A1 m1], m2 as [| | [A2 m2]]; auto.
simpl in H5.
apply state_enable_non_resource_action1 in H5; auto.
subst; auto.
-
simpl.
rewrite <- (thread_local_state_enable_non_resource_action Inv) by auto.
auto.
