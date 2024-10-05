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

Lemma in_input_trace_or_app : forall c id i tr1 tr2, in_input_trace c id i tr1 \/ in_input_trace c id i tr2 -> in_input_trace c id i (tr1 ++ tr2).
Proof using.
unfold in_input_trace.
Admitted.

Lemma applied_implies_input_update_split : forall client id i net h d ps, applied_implies_input_state client id i (mkNetwork ps (update name_eq_dec (nwState net) h d)) -> exists e, correct_entry client id i e /\ (In e (log d) \/ (exists h, In e (log (nwState net h))) \/ (exists p es, In p ps /\ mEntries (pBody p) = Some es /\ In e es)).
Proof using.
unfold applied_implies_input_state.
intros.
break_exists_exists.
intuition.
break_exists.
simpl in *.
Admitted.

Lemma aiis_intro_state : forall client id i net e h, In e (log (nwState net h)) -> correct_entry client id i e -> applied_implies_input_state client id i net.
Proof using.
unfold applied_implies_input_state.
Admitted.

Lemma aiis_intro_packet : forall client id i net e p es, mEntries (pBody p) = Some es -> In p (nwPackets net) -> correct_entry client id i e -> In e es -> applied_implies_input_state client id i net.
Proof using.
unfold applied_implies_input_state.
Admitted.

Lemma doGenericServer_log : forall h st os st' ps, doGenericServer h st = (os, st', ps) -> log st' = log st.
Proof using.
intros.
unfold doGenericServer in *.
Admitted.

Theorem handleTimeout_log : forall h st out st' ps, handleTimeout h st = (out, st', ps) -> log st' = log st.
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Theorem handleClientRequest_no_messages : forall h st client id c out st' ps p, handleClientRequest h st client id c = (out, st', ps) -> In p ps -> False.
Proof using.
unfold handleClientRequest.
intros.
Admitted.

Lemma mEntries_some_is_applied_entries : forall m es, mEntries m = Some es -> is_append_entries m.
Proof using.
unfold mEntries.
intros.
break_match; try discriminate.
find_inversion.
Admitted.

Lemma doGenericServer_packets : forall h st os st' ps p, doGenericServer h st = (os, st', ps) -> In p ps -> False.
Proof using.
intros.
unfold doGenericServer in *.
Admitted.

Lemma doLeader_messages : forall d h os d' ms m es e, doLeader d h = (os, d', ms) -> In m ms -> mEntries (snd m) = Some es -> In e es -> In e (log d).
Proof using.
unfold doLeader.
intros.
repeat break_match; repeat find_inversion; simpl in *; intuition.
do_in_map.
subst.
simpl in *.
find_inversion.
Admitted.

Lemma handleInputs_aais : forall client id h inp i net os d' ms e o, ~ applied_implies_input_state client id i net -> handleInput h inp (nwState net h) = (os, d', ms) -> correct_entry client id i e -> In e (log d') -> in_input_trace client id i [(h, inl inp); o].
Proof using.
intros.
destruct inp; simpl in *.
-
find_erewrite_lem handleTimeout_log.
exfalso.
eauto using aiis_intro_state.
-
destruct (log d') using (handleClientRequest_log_ind ltac:(eauto)).
+
exfalso.
eauto using aiis_intro_state.
+
simpl in *.
break_or_hyp.
*
subst.
unfold in_input_trace.
unfold correct_entry in *.
break_and.
subst.
simpl.
eauto.
*
exfalso.
Admitted.

Lemma handleMessage_aais : forall client id i net p d' ms e, ~ applied_implies_input_state client id i net -> In p (nwPackets net) -> handleMessage (pSrc p) (pDst p) (pBody p) (nwState net (pDst p)) = (d', ms) -> correct_entry client id i e -> In e (log d') -> False.
Proof using.
intros.
destruct (pBody p) eqn:?; simpl in *; repeat break_let; repeat find_inversion.
-
find_erewrite_lem handleRequestVote_same_log.
eauto using aiis_intro_state.
-
find_erewrite_lem handleRequestVoteReply_same_log.
eauto using aiis_intro_state.
-
find_apply_lem_hyp handleAppendEntries_log.
intuition; find_rewrite.
+
eauto using aiis_intro_state.
+
subst.
eauto using mEntries_intro, aiis_intro_packet.
+
do_in_app.
intuition.
*
eauto using mEntries_intro, aiis_intro_packet.
*
find_apply_lem_hyp removeAfterIndex_in.
eauto using aiis_intro_state.
-
find_erewrite_lem handleAppendEntriesReply_same_log.
Admitted.

Lemma handleRequestVote_doesn't_send_AE : forall h st t n lli llt d m, handleRequestVote h st t n lli llt = (d, m) -> ~ is_append_entries m.
Proof using.
intros.
unfold handleRequestVote in *.
Admitted.

Lemma handleAppendEntriesReply_doesn't_send_AE : forall n st src t es b st' l, handleAppendEntriesReply n st src t es b = (st', l) -> forall x, In x l -> ~ is_append_entries (snd x).
Proof using.
intros.
unfold handleAppendEntriesReply in *.
Admitted.

Lemma handleAppendEntries_doesn't_send_AE : forall n st t i l t' l' l'' st' m, handleAppendEntries n st t i l t' l' l'' = (st', m) -> ~ is_append_entries m.
Proof using.
unfold handleAppendEntries.
intros.
Admitted.

Lemma handleMessage_sends_log : forall client id i net p d' ms m es e, In p (nwPackets net) -> handleMessage (pSrc p) (pDst p) (pBody p) (nwState net (pDst p)) = (d', ms) -> correct_entry client id i e -> In m ms -> mEntries (snd m) = Some es -> In e es -> In e (log (nwState net (pDst p))).
Proof using.
intros.
destruct (pBody p) eqn:?; simpl in *; repeat break_let; repeat find_inversion; simpl in *; intuition; subst; simpl in *.
-
exfalso.
eapply handleRequestVote_doesn't_send_AE; eauto using mEntries_some_is_applied_entries.
-
exfalso.
eapply handleAppendEntries_doesn't_send_AE; eauto using mEntries_some_is_applied_entries.
-
exfalso.
Admitted.

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
Admitted.

Lemma name_dec : forall (P : name -> Prop) (P_dec : forall x, {P x} + {~P x}), {exists x, P x} + {~ exists x, P x}.
Proof.
intros.
destruct (find (fun x => if P_dec x then true else false) nodes) eqn:?.
-
find_apply_lem_hyp find_some.
intuition.
break_if; try discriminate.
eauto.
-
right.
intro.
break_exists.
eapply find_none with (x := x) in Heqo; auto using all_names_nodes.
Admitted.

Definition correct_entry_dec (e : entry) : {correct_entry client id i e} + {~ correct_entry client id i e}.
unfold correct_entry.
Admitted.

Definition exists_dec : forall A (P : A -> Prop) (P_dec : forall x, {P x} + {~ P x}) l, {exists x, P x /\ In x l} + {~ exists x, P x /\ In x l}.
intros.
destruct (find (fun e => if P_dec e then true else false) l) eqn:?.
-
find_apply_lem_hyp find_some.
intuition.
break_if; try discriminate.
eauto.
-
right.
intro.
break_exists.
intuition.
eapply find_none with (x := x) in Heqo; eauto.
Admitted.

Definition aiis_host_dec (net : network) : {aiis_host net} + {~aiis_host net}.
unfold aiis_host.
simpl.
apply name_dec.
intros.
apply exists_dec.
Admitted.

Definition aiis_packet_dec (net : network) : {aiis_packet net} + {~aiis_packet net}.
unfold aiis_packet.
apply exists_dec.
intros.
destruct (pBody x); try solve [right; intro; break_exists; intuition; discriminate].
simpl.
destruct (exists_dec _ _ correct_entry_dec l0); eauto.
right.
intro.
break_exists.
break_and.
find_inversion.
Admitted.

Definition applied_implies_input_state_dec (net : network) : {applied_implies_input_state client id i net} + {~ applied_implies_input_state client id i net}.
unfold applied_implies_input_state.
destruct (aiis_host_dec net).
-
unfold aiis_host in *.
left.
repeat (break_exists; intuition).
eauto 10.
-
destruct (aiis_packet_dec net).
+
unfold aiis_packet in *.
left.
repeat (break_exists; intuition).
eauto 10.
+
unfold aiis_host, aiis_packet in *.
right.
intro.
Admitted.

Lemma applied_implies_input : forall client id failed net tr e, @step_failure_star _ _ failure_params step_failure_init (failed, net) tr -> eClient e = client -> eId e = id -> applied_implies_input_state client id (eInput e) net -> in_input_trace client id (eInput e) tr.
Proof using.
intros.
pose proof @inverse_trace_relations_work _ _ step_failure (ITR client id (eInput e)) (failed, net) tr.
unfold step_failure_star in *.
simpl in *.
Admitted.

Instance aiii : applied_implies_input_interface.
Proof using.
split.
Admitted.

Lemma mEntries_intro : forall m t n l t' es l', m = AppendEntries t n l t' es l' -> mEntries m = Some es.
Proof using.
unfold mEntries.
intros.
subst.
auto.
