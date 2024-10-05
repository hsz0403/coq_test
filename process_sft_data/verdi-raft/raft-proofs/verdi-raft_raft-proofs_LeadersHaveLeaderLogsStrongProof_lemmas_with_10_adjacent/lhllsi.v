Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Section LeadersHaveLeaderLogsStrong.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Ltac start := red; unfold leaders_have_leaderLogs_strong; intros; subst; simpl in *; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *.
Instance lhllsi : leaders_have_leaderLogs_strong_interface.
Proof.
split.
intros.
eapply refined_raft_net_invariant; eauto.
-
apply leaders_have_leaderLogs_strong_init.
-
apply leaders_have_leaderLogs_strong_clientRequest.
-
apply leaders_have_leaderLogs_strong_timeout.
-
apply leaders_have_leaderLogs_strong_appendEntries.
-
apply leaders_have_leaderLogs_strong_appendEntriesReply.
-
apply leaders_have_leaderLogs_strong_requestVote.
-
apply leaders_have_leaderLogs_strong_requestVoteReply.
-
apply leaders_have_leaderLogs_strong_doLeader.
-
apply leaders_have_leaderLogs_strong_doGenericServer.
-
apply leaders_have_leaderLogs_strong_state_same_packets_subset.
-
apply leaders_have_leaderLogs_strong_reboot.
End LeadersHaveLeaderLogsStrong.

Lemma leaders_have_leaderLogs_strong_appendEntriesReply : refined_raft_net_invariant_append_entries_reply leaders_have_leaderLogs_strong.
Proof using.
start.
find_apply_lem_hyp handleAppendEntriesReply_type.
intuition; try congruence.
repeat find_rewrite.
Admitted.

Lemma leaders_have_leaderLogs_strong_requestVote : refined_raft_net_invariant_request_vote leaders_have_leaderLogs_strong.
Proof using.
start.
find_apply_lem_hyp handleRequestVote_type.
intuition; try congruence.
rewrite update_elections_data_requestVote_leaderLogs.
repeat find_rewrite.
Admitted.

Lemma leaders_have_leaderLogs_strong_requestVoteReply : refined_raft_net_invariant_request_vote_reply leaders_have_leaderLogs_strong.
Proof using.
start.
unfold update_elections_data_requestVoteReply.
break_match; unfold raft_data in *; try solve [repeat find_rewrite; congruence].
simpl in *.
match goal with | |- context [ handleRequestVoteReply ?h ?st ?s ?t ?v ] => pose proof handleRequestVoteReply_spec h st s t v (handleRequestVoteReply h st s t v) end.
intuition; break_if; intuition; simpl in *; repeat find_rewrite; eauto; try congruence.
eexists.
exists [].
intuition eauto.
simpl in *.
Admitted.

Lemma leaders_have_leaderLogs_strong_clientRequest : refined_raft_net_invariant_client_request leaders_have_leaderLogs_strong.
Proof using.
start.
find_copy_apply_lem_hyp handleClientRequest_type.
intuition; try congruence; rewrite update_elections_data_client_request_leaderLogs.
-
repeat find_rewrite.
eauto.
-
break_exists.
intuition.
repeat find_rewrite.
match goal with | h : name, H : forall _, type _ = type _ -> _ |- _ => specialize (H h); concludes end.
break_exists.
match goal with | _ : context [log _ = ?l1 ++ ?l2] |- _ => exists l2, (x :: l1) end.
intuition.
+
repeat find_rewrite.
eauto.
+
simpl in *.
Admitted.

Lemma leaders_have_leaderLogs_strong_timeout : refined_raft_net_invariant_timeout leaders_have_leaderLogs_strong.
Proof using.
start.
find_apply_lem_hyp handleTimeout_type.
intuition; try congruence.
rewrite update_elections_data_timeout_leaderLogs.
repeat find_rewrite.
Admitted.

Lemma leaders_have_leaderLogs_strong_doGenericServer : refined_raft_net_invariant_do_generic_server leaders_have_leaderLogs_strong.
Proof using.
start.
find_apply_lem_hyp doGenericServer_type.
intuition; try congruence.
match goal with | [ H : forall _, _ -> exists _, _, h : name |- _ ] => specialize (H h) end.
repeat find_rewrite.
Admitted.

Lemma leaders_have_leaderLogs_strong_doLeader : refined_raft_net_invariant_do_leader leaders_have_leaderLogs_strong.
Proof using.
start.
find_apply_lem_hyp doLeader_type.
intuition; try congruence.
match goal with | [ H : forall _, _ -> exists _, _, h : name |- _ ] => specialize (H h) end.
repeat find_rewrite.
Admitted.

Lemma leaders_have_leaderLogs_strong_init : refined_raft_net_invariant_init leaders_have_leaderLogs_strong.
Proof using.
red.
unfold leaders_have_leaderLogs_strong, step_async_init.
intros.
simpl in *.
Admitted.

Lemma leaders_have_leaderLogs_strong_state_same_packets_subset : refined_raft_net_invariant_state_same_packet_subset leaders_have_leaderLogs_strong.
Proof using.
red.
unfold leaders_have_leaderLogs_strong.
intros.
repeat find_reverse_higher_order_rewrite.
Admitted.

Lemma leaders_have_leaderLogs_strong_reboot : refined_raft_net_invariant_reboot leaders_have_leaderLogs_strong.
Proof using.
start.
Admitted.

Instance lhllsi : leaders_have_leaderLogs_strong_interface.
Proof.
split.
intros.
eapply refined_raft_net_invariant; eauto.
-
apply leaders_have_leaderLogs_strong_init.
-
apply leaders_have_leaderLogs_strong_clientRequest.
-
apply leaders_have_leaderLogs_strong_timeout.
-
apply leaders_have_leaderLogs_strong_appendEntries.
-
apply leaders_have_leaderLogs_strong_appendEntriesReply.
-
apply leaders_have_leaderLogs_strong_requestVote.
-
apply leaders_have_leaderLogs_strong_requestVoteReply.
-
apply leaders_have_leaderLogs_strong_doLeader.
-
apply leaders_have_leaderLogs_strong_doGenericServer.
-
apply leaders_have_leaderLogs_strong_state_same_packets_subset.
-
apply leaders_have_leaderLogs_strong_reboot.
