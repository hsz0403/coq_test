Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LeaderLogsSublogInterface.
Require Import VerdiRaft.LeaderLogsContiguousInterface.
Require Import VerdiRaft.TermsAndIndicesFromOneInterface.
Require Import VerdiRaft.LeaderLogsLogMatchingInterface.
Section LeaderLogsLogMatching.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {lmi : log_matching_interface}.
Context {lltsi : leaderLogs_term_sanity_interface}.
Context {llsi : leaderLogs_sorted_interface}.
Context {si : sorted_interface}.
Context {llsli : leaderLogs_sublog_interface}.
Context {llci : leaderLogs_contiguous_interface}.
Context {taifoi : terms_and_indices_from_one_interface}.
Definition leaderLogs_entries_match_nw (net : network) : Prop := forall h llt ll p t src pli plt es ci, In (llt, ll) (leaderLogs (fst (nwState net h))) -> In p (nwPackets net) -> pBody p = AppendEntries t src pli plt es ci -> (forall e1 e2, eIndex e1 = eIndex e2 -> eTerm e1 = eTerm e2 -> In e1 es -> In e2 ll -> (forall e3, eIndex e3 <= eIndex e1 -> In e3 es -> In e3 ll) /\ (pli <> 0 -> exists e4, eIndex e4 = pli /\ eTerm e4 = plt /\ In e4 ll)).
Definition leaderLogs_entries_match (net : network) : Prop := leaderLogs_entries_match_host net /\ leaderLogs_entries_match_nw net.
Ltac use_log_matching_nw := pose proof (lifted_log_matching_nw _ ltac:(eauto)); match goal with | [ H : _ |- _ ] => eapply H; [|eauto]; repeat find_rewrite; intuition end.
Instance lllmi : leaderLogs_entries_match_interface : Prop.
Proof.
split.
apply leaderLogs_entries_match_invariant.
End LeaderLogsLogMatching.

Lemma leaderLogs_entries_match_append_entries : refined_raft_net_invariant_append_entries leaderLogs_entries_match.
Proof using taifoi si llsi lmi rri.
unfold refined_raft_net_invariant_append_entries, leaderLogs_entries_match.
intuition.
-
unfold leaderLogs_entries_match_host in *.
intros.
{
intros.
simpl in *.
repeat find_higher_order_rewrite.
find_rewrite_lem update_fun_comm.
simpl in *.
find_rewrite_lem update_fun_comm.
find_rewrite_lem update_elections_data_appendEntries_leaderLogs.
find_erewrite_lem update_nop_ext'.
update_destruct_simplify; rewrite_update; try rewrite update_elections_data_appendEntries_leaderLogs in *; eauto.
destruct (log d) using (handleAppendEntries_log_ind ltac:(eauto)); eauto.
+
subst.
eapply entries_match_scratch with (plt0 := plt).
*
eauto using lifted_logs_sorted_nw.
*
apply sorted_uniqueIndices.
eapply leaderLogs_sorted_invariant; eauto.
*
eapply_prop leaderLogs_entries_match_nw; eauto.
*
use_log_matching_nw.
*
use_log_matching_nw.
*
match goal with | [ H : In _ (leaderLogs _) |- _ ] => eapply terms_and_indices_from_one_invariant in H; [|solve[auto]] end.
unfold terms_and_indices_from_one in *.
intros.
find_apply_hyp_hyp.
intuition.
+
eapply entries_match_append; eauto.
*
eauto using lifted_logs_sorted_host.
*
eapply leaderLogs_sorted_invariant; eauto.
*
eauto using lifted_logs_sorted_nw.
*
use_log_matching_nw.
*
use_log_matching_nw.
*
eapply findAtIndex_intro; eauto using lifted_logs_sorted_host, sorted_uniqueIndices.
}
-
unfold leaderLogs_entries_match_nw in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
find_rewrite_lem update_fun_comm.
simpl in *.
find_rewrite_lem update_fun_comm.
find_rewrite_lem update_elections_data_appendEntries_leaderLogs.
find_erewrite_lem update_nop_ext'.
find_apply_hyp_hyp.
break_or_hyp.
+
intuition; match goal with | [ H : _ |- _ ] => solve [eapply H with (p0 := p0); eauto with *] end.
+
simpl in *.
find_copy_apply_lem_hyp handleAppendEntries_doesn't_send_AE.
exfalso.
Admitted.

Lemma leaderLogs_entries_match_append_entries_reply : refined_raft_net_invariant_append_entries_reply leaderLogs_entries_match.
Proof using.
unfold refined_raft_net_invariant_append_entries_reply, leaderLogs_entries_match.
intuition.
-
eapply leaderLogs_entries_match_host_state_same; eauto; simpl; intros; repeat find_higher_order_rewrite; update_destruct_simplify; rewrite_update; auto.
erewrite handleAppendEntriesReply_same_log by eauto.
auto.
-
eapply leaderLogs_entries_match_nw_packet_set; eauto; simpl.
+
intros.
find_apply_hyp_hyp.
repeat find_rewrite.
intuition; [eauto with *|].
find_apply_lem_hyp handleAppendEntriesReply_packets.
subst.
simpl in *.
intuition.
+
intros.
Admitted.

Lemma handleRequestVote_packets : forall h st t candidate lli llt st' m, handleRequestVote h st t candidate lli llt = (st', m) -> ~ is_append_entries m.
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
Admitted.

Lemma leaderLogs_entries_match_request_vote : refined_raft_net_invariant_request_vote leaderLogs_entries_match.
Proof using.
unfold refined_raft_net_invariant_request_vote, leaderLogs_entries_match.
intuition.
-
eapply leaderLogs_entries_match_host_state_same; eauto; simpl; intros; repeat find_higher_order_rewrite; update_destruct_simplify; rewrite_update; auto.
+
now rewrite leaderLogs_update_elections_data_requestVote.
+
erewrite handleRequestVote_log; eauto.
-
eapply leaderLogs_entries_match_nw_packet_set; eauto; simpl.
+
intros.
find_apply_hyp_hyp.
repeat find_rewrite.
intuition; [eauto with *|].
find_apply_lem_hyp handleRequestVote_packets.
subst.
simpl in *.
intuition.
+
intros.
repeat find_higher_order_rewrite; update_destruct_simplify; rewrite_update; auto.
Admitted.

Lemma leaderLogs_entries_match_request_vote_reply : refined_raft_net_invariant_request_vote_reply leaderLogs_entries_match.
Proof using lmi rri.
unfold refined_raft_net_invariant_request_vote_reply, leaderLogs_entries_match.
intuition.
-
unfold leaderLogs_entries_match_host in *.
intros.
simpl in *.
subst.
repeat find_higher_order_rewrite.
rewrite update_fun_comm.
simpl.
rewrite update_fun_comm.
simpl.
rewrite update_nop_ext' by now rewrite handleRequestVoteReply_same_log.
find_rewrite_lem update_fun_comm.
simpl in *.
update_destruct_simplify; rewrite_update; eauto.
find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto.
intuition eauto.
subst.
rewrite handleRequestVoteReply_same_log.
apply lifted_log_matching_host.
auto.
-
unfold leaderLogs_entries_match_nw in *.
intros.
simpl in *.
subst.
repeat find_higher_order_rewrite.
find_rewrite_lem update_fun_comm.
simpl in *.
find_rewrite_lem update_fun_comm.
update_destruct_simplify; rewrite_update.
+
find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto.
break_or_hyp.
*
repeat find_reverse_rewrite.
eauto.
*
break_and.
subst.
rewrite handleRequestVoteReply_same_log.
find_rewrite_lem handleRequestVoteReply_same_log.
pose proof (lifted_log_matching_nw _ ltac:(eauto)).
repeat find_reverse_rewrite.
match goal with | [ H : _, pkt : packet |- _ ] => solve [eapply H with (p := pkt); eauto] end.
+
repeat find_reverse_rewrite.
Admitted.

Lemma doLeader_messages : forall st h os st' ms, doLeader st h = (os, st', ms) -> ms = [] \/ ms = map (replicaMessage st' h) (filter (fun h' : name => if name_eq_dec h h' then false else true) nodes).
Proof using.
unfold doLeader.
intros.
Admitted.

Lemma leaderLogs_entries_match_do_leader : refined_raft_net_invariant_do_leader leaderLogs_entries_match.
Proof using llci si llsi rri.
unfold refined_raft_net_invariant_do_leader, leaderLogs_entries_match.
intuition.
-
eapply leaderLogs_entries_match_host_state_same; eauto; simpl; intros; find_higher_order_rewrite; update_destruct_simplify; rewrite_update; auto.
+
find_rewrite.
auto.
+
erewrite doLeader_same_log by eauto.
find_rewrite.
auto.
-
unfold leaderLogs_entries_match_nw in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
find_rewrite_lem update_fun_comm.
simpl in *.
match goal with | [ H : _ |- _ ] => rewrite update_nop_ext' in H by (find_rewrite; auto) end.
find_apply_hyp_hyp.
break_or_hyp.
+
find_reverse_rewrite.
eauto.
+
do_in_map.
subst.
simpl in *.
find_copy_apply_lem_hyp doLeader_messages.
break_or_hyp.
*
simpl in *.
intuition.
*
do_in_map.
find_apply_lem_hyp filter_In.
break_and.
break_if; try discriminate.
unfold replicaMessage in *.
subst.
simpl in *.
find_inversion.
{
intuition.
-
repeat find_erewrite_lem doLeader_same_log.
eapply_prop leaderLogs_entries_match_host; eauto.
+
match goal with | [ H : _ |- _ ] => rewrite H end.
simpl.
eauto using findGtIndex_in.
+
auto with *.
+
find_rewrite.
simpl.
eauto using findGtIndex_in.
-
find_copy_apply_lem_hyp leaderLogs_contiguous_invariant; auto.
unfold contiguous_range_exact_lo in *.
break_and.
match goal with | [ H : forall _, _ < _ <= _ -> _ |- context [eIndex _ = ?x]] => remember (x) as index; specialize (H index); forward H end.
+
intuition; auto using neq_0_lt.
find_apply_lem_hyp findGtIndex_necessary.
break_and.
eapply le_trans.
*
apply lt_le_weak.
eauto.
*
repeat find_rewrite.
eapply maxIndex_is_max; auto.
eapply leaderLogs_sorted_invariant; eauto.
+
concludes.
break_exists_exists.
intuition.
match goal with | [ H : context [leaderLogs_entries_match_host], H' : context [leaderLogs] |- _ ] => eapply H with (h := src)(e := e1)(e' := e2)(e'' := x) in H'; auto end.
*
pose proof lifted_logs_sorted_host net src ltac:(auto).
repeat find_rewrite.
simpl in *.
repeat find_erewrite_lem doLeader_same_log.
erewrite doLeader_same_log by eauto.
erewrite findAtIndex_intro; eauto using sorted_uniqueIndices.
*
find_apply_lem_hyp findGtIndex_necessary.
break_and.
repeat find_erewrite_lem doLeader_same_log.
repeat find_rewrite.
simpl in *.
auto.
*
find_apply_lem_hyp findGtIndex_necessary.
break_and.
omega.
Admitted.

Lemma doGenericServer_packets : forall h st os st' ps, doGenericServer h st = (os, st', ps) -> ps = [].
Proof using.
intros.
unfold doGenericServer in *.
Admitted.

Lemma leaderLogs_entries_match_do_generic_server : refined_raft_net_invariant_do_generic_server leaderLogs_entries_match.
Proof using.
unfold refined_raft_net_invariant_do_generic_server, leaderLogs_entries_match.
intuition.
-
eapply leaderLogs_entries_match_host_state_same; eauto; simpl; intros; find_higher_order_rewrite; update_destruct_simplify; rewrite_update; auto.
+
find_rewrite.
auto.
+
erewrite doGenericServer_log by eauto.
find_rewrite.
auto.
-
eapply leaderLogs_entries_match_nw_packet_set; eauto; simpl.
+
intros.
find_apply_hyp_hyp.
intuition.
find_apply_lem_hyp doGenericServer_packets.
subst.
simpl in *.
intuition.
+
intros.
Admitted.

Lemma leaderLogs_entries_match_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset leaderLogs_entries_match.
Proof using.
unfold refined_raft_net_invariant_state_same_packet_subset, leaderLogs_entries_match.
intuition.
-
eapply leaderLogs_entries_match_host_state_same; eauto; intros; find_higher_order_rewrite; auto.
-
Admitted.

Lemma leaderLogs_entries_match_invariant : forall net, refined_raft_intermediate_reachable net -> leaderLogs_entries_match net.
Proof using taifoi llci llsli si llsi lltsi lmi rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply leaderLogs_entries_match_init.
-
apply leaderLogs_entries_match_client_request.
-
apply leaderLogs_entries_match_timeout.
-
apply leaderLogs_entries_match_append_entries.
-
apply leaderLogs_entries_match_append_entries_reply.
-
apply leaderLogs_entries_match_request_vote.
-
apply leaderLogs_entries_match_request_vote_reply.
-
apply leaderLogs_entries_match_do_leader.
-
apply leaderLogs_entries_match_do_generic_server.
-
apply leaderLogs_entries_match_state_same_packet_subset.
-
Admitted.

Instance lllmi : leaderLogs_entries_match_interface : Prop.
Proof.
split.
Admitted.

Lemma leaderLogs_entries_match_reboot : refined_raft_net_invariant_reboot leaderLogs_entries_match.
Proof using.
unfold refined_raft_net_invariant_reboot, leaderLogs_entries_match, reboot.
intuition.
-
eapply leaderLogs_entries_match_host_state_same; eauto; intros; find_higher_order_rewrite; update_destruct_simplify; rewrite_update; auto; find_rewrite; auto.
-
eapply leaderLogs_entries_match_nw_packet_set; eauto; try find_rewrite; intuition.
find_higher_order_rewrite; update_destruct_simplify; rewrite_update; try find_rewrite; auto.
