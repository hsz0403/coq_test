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

Lemma hoare_parallel_partial_sound {CPP: ConcurrentProgrammingLanguage_Sparallel P} {AcP: Action_Parallel Ac} {nAcPr: NormalAction_Parallel_resource Ac Res} {c2tP: Command2Traces_Sparallel_resource P model Ac Res c2t} {AIPr: ActionInterpret_Parallel_resource model Ac Res ac_sem}: forall Inv c1 P1 Q1 c2 P2 Q2 (INV: LegalInvariants Inv), guarded_triple_partial_valid Inv P1 c1 Q1 -> guarded_triple_partial_valid Inv P2 c2 Q2 -> guarded_triple_partial_valid Inv (P1 * P2) (Sparallel c1 c2) (Q1 * Q2).
Proof.
intros.
rename H into LEFT_ASSU, H0 into RIGHT_ASSU.
hnf in LEFT_ASSU, RIGHT_ASSU |- *; intros.
unfold access, ThreadLocal_BSS in LEFT_ASSU, RIGHT_ASSU, H0; simpl in LEFT_ASSU, RIGHT_ASSU, H0.
inversion H0; subst; clear H0.
rewrite Sparallel_denote in H1.
set (Tr1 := cmd_denote c1) in LEFT_ASSU, H1.
set (Tr2 := cmd_denote c2) in RIGHT_ASSU, H1.
clearbody Tr1 Tr2; clear c1 c2.
inversion H1; subst; clear H1.
set (A1 := fun _: resource => False) in LEFT_ASSU at 1, H4 at 1.
set (A2 := fun _: resource => False) in RIGHT_ASSU at 1, H4 at 1.
set (A := fun _: resource => False) in H2 at 1.
rewrite sat_sepcon in H.
destruct H as [s1 [s2 [? [? ?]]]].
set (s0 := s_pre) in H.
assert (STATE_JOIN: @join _ (prod_Join resources model) (A1, s1) (A2, s2) (A, s0)).
{
split; auto.
hnf; intros r0.
simpl; subst A1 A2 A; split; tauto.
}
assert (STATE_LE: @Krelation _ (RelProd (discPred_R resource) R) (A, s0) (A, s_pre)).
{
split; hnf; simpl.
+
intros; hnf; tauto.
+
change (s_pre <= s_pre).
reflexivity.
}
clearbody A1 A2 A s0.
clear H.
specialize (fun ms_post HH => LEFT_ASSU s1 ms_post H1 (traces_access_intro tr1 _ _ _ H0 HH)).
specialize (fun ms_post HH => RIGHT_ASSU s2 ms_post H5 (traces_access_intro tr2 _ _ _ H3 HH)).
clear P1 P2 H1 H5 Tr1 Tr2 H0 H3.
rename H2 into TRACE_ACC.
revert s0 s1 s2 s_pre A LEFT_ASSU RIGHT_ASSU STATE_JOIN STATE_LE TRACE_ACC; induction H4; intros.
+
inversion TRACE_ACC; subst.
destruct ms_post; subst; inversion H.
subst m A.
assert (A2 = fun _ => False).
{
extensionality r; apply prop_ext.
destruct STATE_JOIN as [? _].
hnf in H0.
specialize (H0 r).
simpl in H0; destruct H0.
tauto.
}
assert (A1 = fun _ => False).
{
extensionality r; apply prop_ext.
destruct STATE_JOIN as [? _].
hnf in H1.
specialize (H1 r).
simpl in H1; destruct H1.
tauto.
}
subst A1 A2.
specialize (LEFT_ASSU (Terminating s1) (trace_access_nil _)); simpl in LEFT_ASSU.
specialize (RIGHT_ASSU (Terminating s2) (trace_access_nil _)); simpl in RIGHT_ASSU.
eapply sat_mono; [exact (proj2 STATE_LE) |].
rewrite sat_sepcon.
exists s1, s2.
split; [| split]; auto.
exact (proj2 STATE_JOIN).
+
exfalso.
destruct (res_actions_no_race _ _ H).
apply (state_enable_race_actions_spec a1 a2 A1 A2 s1 s2 s0); auto.
-
intro.
rewrite (thread_local_state_enable_non_resource_action Inv) in H2 by auto.
specialize (LEFT_ASSU Error (@trace_access_Error _ _ (ThreadLocal_ActionInterpret_resource _ Inv) _ _ _ H2)).
inversion LEFT_ASSU.
-
intro.
rewrite (thread_local_state_enable_non_resource_action Inv) in H2 by auto.
specialize (RIGHT_ASSU Error (@trace_access_Error _ _ (ThreadLocal_ActionInterpret_resource _ Inv) _ _ _ H2)).
inversion RIGHT_ASSU.
-
exact (proj2 STATE_JOIN).
+
change (res_enable a1 (fst (A1, s1)) A1' (fst (A2, s2))) in H.
inversion TRACE_ACC; subst.
-
destruct ms_post; inversion H5; clear H5; auto.
-
pose proof ThreadLocal_ordered_frame_property Inv _ _ _ _ _ Error A1' H STATE_JOIN STATE_LE H3 as [Error' [Error'' [? [? [_ ?]]]]].
inversion H1; subst; clear H1.
inversion H0; subst; clear H0.
simpl lift_function in H2.
exfalso.
apply (LEFT_ASSU Error).
apply trace_access_Error; auto.
-
pose proof ThreadLocal_ordered_frame_property Inv _ _ _ _ _ (Terminating s') A1' H STATE_JOIN STATE_LE H2 as [m2 [n2' [? [? [? ?]]]]].
destruct n2' as [| | n2']; inversion H1; subst.
destruct m2 as [| | m2]; inversion H0; subst.
*
exfalso.
apply (LEFT_ASSU Error).
apply trace_access_Error; auto.
*
destruct s' as [A' s'], m2 as [A1' s1'], n2' as [A0' s0'].
assert (A0' = A').
{
clear - H9.
destruct H9 as [? _]; hnf in H; simpl in H.
extensionality r0; apply prop_ext; apply H.
}
subst A0'.
apply (IHtrace_interleave s0' s1' s2 s' A'); auto.
intros.
apply LEFT_ASSU.
eapply trace_access_Terminating; eauto.
+
change (res_enable a2 (fst (A2, s2)) A2' (fst (A1, s1))) in H.
inversion TRACE_ACC; subst.
-
destruct ms_post; inversion H5; clear H5; auto.
-
pose proof ThreadLocal_ordered_frame_property Inv _ _ _ _ _ Error A2' H (@join_comm _ _ (prod_SA _ _) _ _ _ STATE_JOIN) STATE_LE H3 as [Error' [Error'' [? [? [_ ?]]]]].
inversion H1; subst; clear H1.
inversion H0; subst; clear H0.
simpl lift_function in H2.
exfalso.
apply (RIGHT_ASSU Error).
apply trace_access_Error; auto.
-
pose proof ThreadLocal_ordered_frame_property Inv _ _ _ _ _ (Terminating s') A2' H (@join_comm _ _ (prod_SA _ _) _ _ _ STATE_JOIN) STATE_LE H2 as [m2 [n2' [? [? [? ?]]]]].
destruct n2' as [| | n2']; inversion H1; subst.
destruct m2 as [| | m2]; inversion H0; subst.
*
exfalso.
apply (RIGHT_ASSU Error).
apply trace_access_Error; auto.
*
destruct s' as [A' s'], m2 as [A2' s2'], n2' as [A0' s0'].
assert (A0' = A').
{
clear - H9.
destruct H9 as [? _]; hnf in H; simpl in H.
extensionality r0; apply prop_ext; apply H.
}
subst A0'.
apply (IHtrace_interleave s0' s1 s2' s' A'); auto.
intros.
apply RIGHT_ASSU.
eapply trace_access_Terminating; eauto.
apply (@join_comm _ _ (prod_SA _ _)); auto.
