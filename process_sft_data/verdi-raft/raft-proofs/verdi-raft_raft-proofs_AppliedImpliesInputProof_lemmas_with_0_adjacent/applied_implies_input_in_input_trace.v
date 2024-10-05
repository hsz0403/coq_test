Require Import Verdi.InverseTraceRelations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.TraceUtil.
Require Import VerdiRaft.OutputImpliesAppliedInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.AppliedImpliesInputInterface.
Section AppliedImpliesInputProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {oiai : output_implies_applied_interface}.
Section inner.
Variable client : clientId.
Variable id : nat.
Variable i : input.
Definition aiis_host (net : network) : Prop := exists h e, correct_entry client id i e /\ In e (log (nwState net h)).
Instance aiii : applied_implies_input_interface.
Proof using.
split.
exact applied_implies_input.
End AppliedImpliesInputProof.

Lemma applied_implies_input_in_input_trace : forall net failed net' failed' tr, raft_intermediate_reachable net -> @step_failure _ _ failure_params (failed, net) (failed', net') tr -> ~ applied_implies_input_state client id i net -> applied_implies_input_state client id i net' -> in_input_trace client id i tr.
Proof using.
intros.
match goal with | [ H : context [step_failure _ _ _ ] |- _ ] => invcs H end.
-
unfold RaftNetHandler in *.
repeat break_let.
subst.
find_inversion.
find_apply_lem_hyp applied_implies_input_update_split.
break_exists.
intuition; break_exists.
+
find_erewrite_lem doGenericServer_log.
find_erewrite_lem doLeader_same_log.
exfalso.
eauto using aiis_intro_state, handleMessage_aais.
+
exfalso.
eauto using aiis_intro_state.
+
intuition.
do_in_app.
intuition.
*
do_in_map.
subst.
simpl in *.
{
repeat (do_in_app; intuition).
-
exfalso.
eauto using aiis_intro_state, handleMessage_sends_log.
-
find_eapply_lem_hyp doLeader_messages; eauto.
exfalso.
eauto using aiis_intro_state, handleMessage_aais.
-
exfalso.
eauto using doGenericServer_packets.
}
*
exfalso.
eauto using aiis_intro_packet.
-
unfold RaftInputHandler in *.
repeat break_let.
subst.
find_inversion.
find_apply_lem_hyp applied_implies_input_update_split.
break_exists.
intuition; break_exists.
+
find_erewrite_lem doGenericServer_log.
find_erewrite_lem doLeader_same_log.
eauto using handleInputs_aais.
+
exfalso.
eauto using aiis_intro_state.
+
intuition.
do_in_app.
intuition.
*
do_in_map.
subst.
simpl in *.
{
repeat (do_in_app; intuition).
-
destruct inp; simpl in *.
+
exfalso.
eapply handleTimeout_not_is_append_entries; eauto.
eauto using mEntries_some_is_applied_entries.
+
exfalso.
eauto using handleClientRequest_no_messages.
-
find_eapply_lem_hyp doLeader_messages; eauto.
eauto using handleInputs_aais.
-
exfalso.
eauto using doGenericServer_packets.
}
*
exfalso.
eauto using aiis_intro_packet.
-
unfold applied_implies_input_state in H2.
break_exists.
intuition; break_exists; simpl in *.
+
exfalso; eauto using aiis_intro_state.
+
break_and.
simpl in *.
exfalso.
eauto using aiis_intro_packet.
-
unfold applied_implies_input_state in H2.
break_exists.
intuition; break_exists; simpl in *.
+
exfalso; eauto using aiis_intro_state.
+
intuition.
*
subst.
exfalso.
eauto using aiis_intro_packet.
*
exfalso.
apply H1.
eapply aiis_intro_packet; eauto.
congruence.
-
congruence.
-
unfold applied_implies_input_state in H2.
break_exists.
intuition; break_exists; simpl in *.
+
update_destruct_max_simplify; exfalso; eauto using aiis_intro_state.
+
intuition.
exfalso.
eauto using aiis_intro_packet.
