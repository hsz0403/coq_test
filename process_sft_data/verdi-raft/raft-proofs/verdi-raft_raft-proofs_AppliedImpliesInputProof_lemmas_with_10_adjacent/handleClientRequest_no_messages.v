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

Lemma mEntries_intro : forall m t n l t' es l', m = AppendEntries t n l t' es l' -> mEntries m = Some es.
Proof using.
unfold mEntries.
intros.
subst.
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

Theorem handleClientRequest_no_messages : forall h st client id c out st' ps p, handleClientRequest h st client id c = (out, st', ps) -> In p ps -> False.
Proof using.
unfold handleClientRequest.
intros.
break_match; find_inversion; simpl in *; intuition.
