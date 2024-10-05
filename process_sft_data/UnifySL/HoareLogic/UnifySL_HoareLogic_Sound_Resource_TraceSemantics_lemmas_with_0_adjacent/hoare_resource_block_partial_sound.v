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

Lemma hoare_resource_block_partial_sound {CPP: ConcurrentProgrammingLanguage_Sresource P Res} {c2tR: Command2Traces_Sresource P Ac Res c2t} {c2tSRA: StructuralResourceAccess P Ac Res c2t}: forall Inv0 Inv1 r P1 P2 c I dI (INV: LegalInvariants Inv1), @join _ (Pred_Join _) Inv0 (eq (r, dI)) Inv1 -> (dI = fun m => KRIPKE: m |= I) -> resource_no_occur r (cmd_denote c) -> guarded_triple_partial_valid Inv0 (P1 * I) c (P2 * I) -> guarded_triple_partial_valid Inv1 P1 (Sresource r c) P2.
Proof.
intros.
subst dI.
rewrite SRA_triple_spec in H2 |- *.
rename H into INV_CONS, H1 into NO_OCCUR.
rename H2 into ASSU; intros.
unfold access, ThreadLocal_BSS in ASSU, H0; simpl in ASSU, H0.
inversion H0; subst; clear H0.
rewrite Sresource_denote in H1.
set (Tr := cmd_denote c) in ASSU, H1, NO_OCCUR.
clearbody Tr; clear c.
inversion H1; subst; clear H1.
inversion H3; subst; clear H3.
unfold singleton_traces, singleton_trace in H0, H4.
subst tr1 tr3; rename tr0 into tr.
specialize (fun s A_post ms_post _H HH => ASSU s A_post ms_post _H (traces_access_intro tr _ _ _ H1 HH)).
specialize (NO_OCCUR _ H1).
clear Tr H1.
unfold trace_app in H2; simpl app in H2; inversion H2; subst; clear H2.
{
exfalso; inversion H4; subst; solve_resource_action.
}
{
exfalso; inversion H4; subst; solve_resource_action.
}
inversion H3; subst; clear H3; solve_resource_action.
assert (I0 = fun m => KRIPKE: m |= I).
{
clear - INV_CONS INV H7.
apply (at_most_one_invariant r); auto.
specialize (INV_CONS (r, fun m => m |= I)).
destruct INV_CONS; simpl in *.
tauto.
}
subst I0.
assert (KRIPKE: n |= P1 * I).
{
rewrite sat_sepcon.
exists s_pre, f; auto.
}
clear f s_pre H8 H9 H.
rename n into s.
specialize (fun A_post ms_post => ASSU s A_post ms_post H0); clear H0 P1.
set (A1 := fun _ => False) in H5, ASSU at 1.
clearbody A1.
rename H5 into JOIN_RES, H6 into TRACE_ACC, H7 into Inv_r.
revert A1 A2 s JOIN_RES TRACE_ACC ASSU; induction tr; intros.
+
simpl in TRACE_ACC.
specialize (ASSU A1 (Terminating s) (trace_access_nil _)).
change (KRIPKE: s |= P2 * I) in ASSU.
rewrite sat_sepcon in ASSU.
destruct ASSU as [s' [f [? [? ?]]]].
assert ((fun n : model => exists f : model, KRIPKE: f |= I /\ join n f s) s') by (exists f; auto).
inversion TRACE_ACC; subst.
-
inversion H6; subst; solve_resource_action.
-
inversion H6; subst; solve_resource_action.
pose proof at_most_one_invariant _ _ _ H9 Inv_r; subst I0; clear H9.
exfalso; apply (H10 s').
exists f; auto.
-
inversion H5; subst; solve_resource_action.
pose proof at_most_one_invariant _ _ _ H10 Inv_r; subst I0; clear H10.
apply (proj2 H11) in H2.
eapply sat_mono in H0; [| exact H2].
inversion H8; subst.
destruct ms_post; inversion H3; subst.
auto.
+
simpl in TRACE_ACC.
assert (forall ms, thread_local_state_enable Inv1 a (A2, s) ms -> match ms with | Error => thread_local_state_enable Inv0 a (A1, s) Error | NonTerminating => thread_local_state_enable Inv0 a (A1, s) NonTerminating | Terminating (A2', s') => exists A1', join A1' (eq r) A2' /\ thread_local_state_enable Inv0 a (A1, s) (Terminating (A1', s')) end).
{
clear - INV_CONS INV NO_OCCUR JOIN_RES AIr.
intros.
assert (~ is_resource_action r a).
{
intros [? | ?].
+
subst; apply (proj1 NO_OCCUR).
left; auto.
+
subst; apply (proj2 NO_OCCUR).
left; auto.
}
clear NO_OCCUR; rename H0 into NO_OCCUR.
inversion H; subst; solve_resource_action.
+
assert (Inv0 (r0, I0)).
{
specialize (INV_CONS (r0, I0)).
assert ((r, fun m : model => KRIPKE: m |= I) <> (r0, I0)) by congruence.
destruct INV_CONS; tauto.
}
rename A3 into A2'.
pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ JOIN_RES) H2 as [A1' [? ?]].
apply join_comm in H4.
exists A1'; split; auto.
eapply (thread_local_state_enable_acq _ _ _ _ _ _ _ _ H1 H0 H5 H7).
+
assert (Inv0 (r0, I0)).
{
specialize (INV_CONS (r0, I0)).
assert ((r, fun m : model => KRIPKE: m |= I) <> (r0, I0)) by congruence.
destruct INV_CONS; tauto.
}
rename A3 into A2'.
set (A1' := fun rr => A2' rr /\ r <> rr).
assert (join A1' (eq r) A2').
{
subst A1'; intros rr; specialize (H2 rr); specialize (JOIN_RES rr).
assert (r0 = rr -> r = rr -> False) by (intros; congruence).
destruct H2, JOIN_RES; split; tauto.
}
assert (join A1' (eq r0) A1).
{
subst A1'; intros rr; specialize (H2 rr); specialize (JOIN_RES rr).
assert (r0 = rr -> r = rr -> False) by (intros; congruence).
destruct H2, JOIN_RES; split; tauto.
}
exists A1'; split; auto.
eapply (thread_local_state_enable_rel_succ _ _ _ _ _ _ _ H3 H0 H6).
+
assert (Inv0 (r0, I0)).
{
specialize (INV_CONS (r0, I0)).
assert ((r, fun m : model => KRIPKE: m |= I) <> (r0, I0)) by congruence.
destruct INV_CONS; tauto.
}
rename A3 into A2'.
set (A1' := fun rr => A2' rr /\ r <> rr).
assert (join A1' (eq r) A2').
{
subst A1'; intros rr; specialize (H2 rr); specialize (JOIN_RES rr).
assert (r0 = rr -> r = rr -> False) by (intros; congruence).
destruct H2, JOIN_RES; split; tauto.
}
assert (join A1' (eq r0) A1).
{
subst A1'; intros rr; specialize (H2 rr); specialize (JOIN_RES rr).
assert (r0 = rr -> r = rr -> False) by (intros; congruence).
destruct H2, JOIN_RES; split; tauto.
}
eapply (thread_local_state_enable_rel_fail _ _ _ _ _ _ H3 H0 H6).
+
destruct ms as [| | [A2' s']].
-
eapply thread_local_state_enable_non_resource; auto.
change Error with (lift_function (pair A1) (@Error model)).
change Error with (lift_function (pair A2) (@Error model)) in H1.
apply (state_enable_non_resource_action2 _ _ _ _ _ H0 H1).
-
eapply thread_local_state_enable_non_resource; auto.
change NonTerminating with (lift_function (pair A1) (@NonTerminating model)).
change NonTerminating with (lift_function (pair A2) (@NonTerminating model)) in H1.
apply (state_enable_non_resource_action2 _ _ _ _ _ H0 H1).
-
pose proof state_enable_non_resource_action1 _ _ _ _ _ H0 H1; subst A2'.
exists A1.
split; auto.
eapply thread_local_state_enable_non_resource; auto.
change (Terminating (A2, s')) with (lift_function (pair A2) (Terminating s')) in H1.
apply (state_enable_non_resource_action2 _ _ _ _ _ H0 H1).
}
inversion TRACE_ACC; subst.
-
destruct ms_post; inversion H4; auto.
-
simpl in H3.
apply H in H3.
specialize (ASSU A1 Error (@trace_access_Error _ _ (ThreadLocal_ActionInterpret_resource _ Inv0) _ _ _ H3)).
inversion ASSU.
-
simpl in H2.
apply H in H2.
destruct s' as [A2' s'].
destruct H2 as [A1' [? ?]].
assert (~ In (Aacquire_res r) tr /\ ~ In (Arelease_res r) tr) by (simpl in NO_OCCUR; tauto).
apply (IHtr H2 A1' A2' s'); auto; clear H2 ms_post IHtr TRACE_ACC H5 A_post.
intros.
apply (ASSU A_post ms_post).
eapply trace_access_Terminating; eauto.
