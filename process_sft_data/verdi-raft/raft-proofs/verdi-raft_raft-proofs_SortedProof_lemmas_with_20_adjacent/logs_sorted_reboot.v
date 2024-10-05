Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.SortedInterface.
Section SortedProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {tsi : term_sanity_interface}.
Ltac find_eapply_hyp_goal := match goal with | H : _ |- _ => eapply H end.
Instance si : sorted_interface.
Proof.
split.
eauto using handleAppendEntries_logs_sorted.
eauto using handleClientRequest_logs_sorted.
auto using logs_sorted_invariant.
End SortedProof.

Theorem packets_ge_prevTerm_not_append_entries : forall net ps' p' st', packets_ge_prevTerm net -> (forall p, In p ps' -> In p (nwPackets net) \/ p = p') -> ~ is_append_entries (pBody p') -> packets_ge_prevTerm (mkNetwork ps' st').
Proof using.
intros.
unfold packets_ge_prevTerm.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
-
unfold packets_ge_prevTerm in *.
eauto.
-
subst.
exfalso.
match goal with H : _ |- _ => apply H end.
Admitted.

Theorem handleTimeout_not_is_append_entries : forall h st st' ps p, handleTimeout h st = (st', ps) -> In p (send_packets h ps) -> ~ is_append_entries (pBody p).
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Theorem logs_sorted_timeout : raft_net_invariant_timeout logs_sorted.
Proof using.
unfold raft_net_invariant_timeout.
unfold logs_sorted.
intuition.
-
unfold logs_sorted_host in *.
simpl in *.
intros.
find_apply_lem_hyp handleTimeout_log.
find_higher_order_rewrite.
break_match; repeat find_rewrite; eauto.
-
eapply logs_sorted_nw_no_append_entries; eauto.
intros.
eauto using handleTimeout_not_is_append_entries.
-
eapply packets_gt_prevIndex_no_append_entries; eauto.
intros.
eauto using handleTimeout_not_is_append_entries.
-
eapply packets_ge_prevTerm_no_append_entries; eauto.
intros.
Admitted.

Theorem sorted_append : forall l l', sorted l -> sorted l' -> (forall e e', In e l -> In e' l' -> eIndex e > eIndex e') -> (forall e e', In e l -> In e' l' -> eTerm e >= eTerm e') -> sorted (l ++ l').
Proof using.
induction l; intros; simpl in *; auto.
Admitted.

Theorem sorted_index_term : forall l e e', eIndex e <= eIndex e' -> sorted l -> In e l -> In e' l -> eTerm e <= eTerm e'.
Proof using.
induction l; intros; simpl in *; intuition.
-
subst_max.
intuition.
-
subst.
find_apply_hyp_hyp.
intuition.
-
subst.
find_apply_hyp_hyp.
Admitted.

Lemma handleAppendEntries_logs_sorted : forall net p t n pli plt es ci st' m, raft_intermediate_reachable net -> logs_sorted net -> handleAppendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci = (st', m) -> pBody p = AppendEntries t n pli plt es ci -> In p (nwPackets net) -> sorted (log st').
Proof using.
intros.
unfold logs_sorted in *.
intuition.
find_apply_lem_hyp handleAppendEntries_log.
intuition.
-
find_rewrite; eauto.
-
subst.
unfold logs_sorted_nw in *.
simpl in *.
find_eapply_hyp_goal; eauto.
-
find_rewrite.
apply sorted_append; eauto using removeAfterIndex_sorted.
+
intros.
find_apply_lem_hyp removeAfterIndex_In_le; eauto.
unfold packets_gt_prevIndex in *.
eapply gt_le_trans; [|eauto].
find_eapply_hyp_goal; [in_crush|eauto|eauto].
simpl in *.
eauto.
+
intros.
find_copy_apply_lem_hyp removeAfterIndex_In_le; eauto.
find_apply_lem_hyp removeAfterIndex_in.
break_exists.
intuition.
subst.
match goal with | H : eIndex ?x <= eIndex ?x', _ : In ?x ?ll |- _ => apply sorted_index_term with (l := ll) (e := x) (e' := x') in H end; eauto.
match goal with |- ?a >= ?b => cut (b <= a); [omega|] end.
eapply le_trans; eauto.
unfold packets_ge_prevTerm in *.
Admitted.

Theorem logs_sorted_append_entries : raft_net_invariant_append_entries logs_sorted.
Proof using.
unfold raft_net_invariant_append_entries.
intros.
unfold logs_sorted.
intuition.
-
unfold logs_sorted_host.
simpl in *.
intros.
repeat find_higher_order_rewrite.
break_match; repeat find_rewrite; eauto; [|unfold logs_sorted in *; intuition eauto].
subst.
eauto using handleAppendEntries_logs_sorted.
-
unfold logs_sorted in *.
intuition.
simpl in *.
eapply logs_sorted_nw_not_append_entries; eauto.
+
intros.
find_apply_hyp_hyp.
intuition eauto.
+
simpl.
eauto using handleAppendEntries_not_append_entries.
-
unfold logs_sorted in *.
intuition.
simpl in *.
eapply packets_gt_prevIndex_not_append_entries; eauto.
+
intros.
find_apply_hyp_hyp.
intuition eauto.
+
simpl.
eauto using handleAppendEntries_not_append_entries.
-
unfold logs_sorted in *.
intuition.
simpl in *.
eapply packets_ge_prevTerm_not_append_entries; eauto.
+
intros.
find_apply_hyp_hyp.
intuition eauto.
+
simpl.
Admitted.

Lemma handleAppendEntriesReply_log : forall h st from t es s st' ps, handleAppendEntriesReply h st from t es s = (st', ps) -> log st' = log st.
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Lemma handleAppendEntriesReply_packets : forall h st from t es s st' ps, handleAppendEntriesReply h st from t es s = (st', ps) -> ps = [].
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Theorem logs_sorted_append_entries_reply : raft_net_invariant_append_entries_reply logs_sorted.
Proof using.
unfold raft_net_invariant_append_entries_reply.
unfold logs_sorted.
intuition; simpl in *.
-
unfold logs_sorted_host in *.
simpl in *.
intros.
find_apply_lem_hyp handleAppendEntriesReply_log.
repeat find_higher_order_rewrite.
break_match; try find_rewrite; eauto.
-
find_apply_lem_hyp handleAppendEntriesReply_packets.
subst.
simpl in *.
eapply logs_sorted_nw_packets_unchanged; eauto.
intros.
find_apply_hyp_hyp.
find_rewrite.
in_crush.
-
find_apply_lem_hyp handleAppendEntriesReply_packets.
subst.
simpl in *.
eapply packets_gt_prevIndex_packets_unchanged; eauto.
intros.
find_apply_hyp_hyp.
find_rewrite.
in_crush.
-
find_apply_lem_hyp handleAppendEntriesReply_packets.
subst.
simpl in *.
eapply packets_ge_prevTerm_packets_unchanged; eauto.
intros.
find_apply_hyp_hyp.
find_rewrite.
Admitted.

Lemma handleRequestVote_packets : forall h st t candidate lli llt st' m, handleRequestVote h st t candidate lli llt = (st', m) -> ~ is_append_entries m.
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
Admitted.

Theorem logs_sorted_request_vote : raft_net_invariant_request_vote logs_sorted.
Proof using.
unfold raft_net_invariant_request_vote.
unfold logs_sorted.
intuition; simpl in *.
-
unfold logs_sorted_host in *.
simpl in *.
intros.
find_apply_lem_hyp handleRequestVote_log.
repeat find_higher_order_rewrite.
break_match; try find_rewrite; eauto.
-
find_apply_lem_hyp handleRequestVote_packets.
subst.
simpl in *.
eapply logs_sorted_nw_not_append_entries; eauto.
+
intros.
find_apply_hyp_hyp.
find_rewrite.
in_crush.
+
simpl.
auto.
-
find_apply_lem_hyp handleRequestVote_packets.
subst.
simpl in *.
eapply packets_gt_prevIndex_not_append_entries; eauto.
+
intros.
find_apply_hyp_hyp.
find_rewrite.
in_crush.
+
simpl.
auto.
-
find_apply_lem_hyp handleRequestVote_packets.
subst.
simpl in *.
eapply packets_ge_prevTerm_not_append_entries; eauto.
+
intros.
find_apply_hyp_hyp.
find_rewrite.
in_crush.
+
simpl.
Admitted.

Lemma handleRequestVoteReply_log : forall h st src t vg st', handleRequestVoteReply h st src t vg = st' -> log st' = log st.
Proof using.
intros.
unfold handleRequestVoteReply, advanceCurrentTerm in *.
Admitted.

Theorem logs_sorted_request_vote_reply : raft_net_invariant_request_vote_reply logs_sorted.
Proof using.
unfold raft_net_invariant_request_vote_reply.
unfold logs_sorted.
intuition; simpl in *.
-
unfold logs_sorted_host in *.
simpl in *.
intros.
find_apply_lem_hyp handleRequestVoteReply_log.
repeat find_higher_order_rewrite.
break_match; try find_rewrite; eauto.
-
eauto using logs_sorted_nw_packets_unchanged.
-
eauto using packets_gt_prevIndex_packets_unchanged.
-
Admitted.

Lemma doLeader_log : forall h st os st' ps, doLeader st h = (os, st', ps) -> log st' = log st.
Proof using.
intros.
unfold doLeader in *.
Admitted.

Lemma doLeader_messages : forall h st os st' ms m t n pli plt entries c, doLeader st h = (os, st', ms) -> sorted (log st) -> In m ms -> snd m = AppendEntries t n pli plt entries c -> subseq entries (log st) /\ (forall e, In e entries -> eIndex e > pli) /\ (forall e, In e entries -> eTerm e >= plt).
Proof using.
intros.
unfold doLeader in *.
repeat break_match; find_inversion; subst; simpl in *; intuition.
-
unfold replicaMessage in *.
do_in_map.
simpl in *.
subst.
simpl in *.
find_inversion.
apply subseq_findGtIndex.
-
unfold replicaMessage in *.
do_in_map.
simpl in *.
subst.
simpl in *.
find_inversion.
find_apply_lem_hyp findGtIndex_necessary; intuition.
-
unfold replicaMessage in *.
do_in_map.
simpl in *.
subst.
simpl in *.
find_inversion.
break_match; intuition.
find_apply_lem_hyp findGtIndex_necessary; intuition.
find_apply_lem_hyp findAtIndex_elim.
simpl in *.
intuition.
repeat find_rewrite.
eapply sorted_index_term; eauto.
Admitted.

Theorem logs_sorted_do_leader : raft_net_invariant_do_leader logs_sorted.
Proof using.
unfold raft_net_invariant_do_leader.
unfold logs_sorted.
intuition; simpl in *.
-
unfold logs_sorted_host in *.
simpl in *.
intros.
find_apply_lem_hyp doLeader_log.
repeat find_higher_order_rewrite.
break_match; subst; try find_rewrite; eauto.
-
unfold logs_sorted_nw.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
do_in_map.
subst.
simpl in *.
find_eapply_lem_hyp doLeader_messages; intuition; eauto using sorted_subseq.
-
unfold packets_gt_prevIndex.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
do_in_map.
subst.
simpl in *.
find_eapply_lem_hyp doLeader_messages; [idtac|idtac|idtac|eauto]; intuition eauto.
-
unfold packets_ge_prevTerm.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
do_in_map.
subst.
simpl in *.
Admitted.

Lemma doGenericServer_packets : forall h st os st' ps, doGenericServer h st = (os, st', ps) -> ps = [].
Proof using.
intros.
unfold doGenericServer in *.
Admitted.

Theorem logs_sorted_do_generic_server : raft_net_invariant_do_generic_server logs_sorted.
Proof using.
unfold raft_net_invariant_do_generic_server.
unfold logs_sorted.
intuition; simpl in *.
-
subst.
unfold logs_sorted_host in *.
simpl in *.
intros.
find_apply_lem_hyp doGenericServer_log.
repeat find_higher_order_rewrite.
break_match; try find_rewrite; eauto.
-
find_apply_lem_hyp doGenericServer_packets.
subst.
simpl in *.
eauto using logs_sorted_nw_packets_unchanged.
-
find_apply_lem_hyp doGenericServer_packets.
subst.
simpl in *.
eauto using packets_gt_prevIndex_packets_unchanged.
-
find_apply_lem_hyp doGenericServer_packets.
subst.
simpl in *.
Admitted.

Theorem logs_sorted_state_same_packet_subset : raft_net_invariant_state_same_packet_subset logs_sorted.
Proof using.
unfold raft_net_invariant_state_same_packet_subset, logs_sorted.
intuition; simpl in *.
-
unfold logs_sorted_host in *.
intros.
find_reverse_higher_order_rewrite.
eauto.
-
eapply logs_sorted_nw_packets_unchanged with (st' := (nwState net')); eauto.
-
eapply packets_gt_prevIndex_packets_unchanged with (st' := (nwState net')); eauto.
-
Admitted.

Theorem logs_sorted_invariant : forall net, raft_intermediate_reachable net -> logs_sorted net.
Proof using tsi.
intros.
eapply raft_net_invariant; eauto.
-
apply logs_sorted_init.
-
apply logs_sorted_client_request.
-
apply logs_sorted_timeout.
-
apply logs_sorted_append_entries.
-
apply logs_sorted_append_entries_reply.
-
apply logs_sorted_request_vote.
-
apply logs_sorted_request_vote_reply.
-
apply logs_sorted_do_leader.
-
apply logs_sorted_do_generic_server.
-
apply logs_sorted_state_same_packet_subset.
-
Admitted.

Instance si : sorted_interface.
Proof.
split.
eauto using handleAppendEntries_logs_sorted.
eauto using handleClientRequest_logs_sorted.
Admitted.

Theorem logs_sorted_reboot : raft_net_invariant_reboot logs_sorted.
Proof using.
unfold raft_net_invariant_reboot, logs_sorted, reboot.
intuition; simpl in *.
-
unfold logs_sorted_host in *.
intros.
repeat find_higher_order_rewrite.
simpl in *.
break_match; subst; eauto.
-
subst.
eapply logs_sorted_nw_packets_unchanged with (st' := nwState net') (ps' := nwPackets net') ; eauto.
find_rewrite.
intuition.
-
subst.
eapply packets_gt_prevIndex_packets_unchanged with (st' := nwState net') (ps' := nwPackets net') ; eauto.
find_rewrite.
intuition.
-
subst.
eapply packets_ge_prevTerm_packets_unchanged with (st' := nwState net') (ps' := nwPackets net') ; eauto.
find_rewrite.
intuition.
