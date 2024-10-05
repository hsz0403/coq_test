Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeadersHaveLeaderLogsInterface.
Section LeadersHaveLeaderLogs.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Ltac start := red; unfold leaders_have_leaderLogs; intros; subst; simpl in *; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *.
Instance lhlli : leaders_have_leaderLogs_interface.
Proof.
split.
intros.
eapply refined_raft_net_invariant; eauto.
-
apply leaders_have_leaderLogs_init.
-
apply leaders_have_leaderLogs_clientRequest.
-
apply leaders_have_leaderLogs_timeout.
-
apply leaders_have_leaderLogs_appendEntries.
-
apply leaders_have_leaderLogs_appendEntriesReply.
-
apply leaders_have_leaderLogs_requestVote.
-
apply leaders_have_leaderLogs_requestVoteReply.
-
apply leaders_have_leaderLogs_doLeader.
-
apply leaders_have_leaderLogs_doGenericServer.
-
apply leaders_have_leaderLogs_state_same_packets_subset.
-
apply leaders_have_leaderLogs_reboot.
End LeadersHaveLeaderLogs.

Lemma leaders_have_leaderLogs_clientRequest : refined_raft_net_invariant_client_request leaders_have_leaderLogs.
Proof using.
start.
find_apply_lem_hyp handleClientRequest_type.
intuition; try congruence.
rewrite update_elections_data_client_request_leaderLogs.
repeat find_rewrite.
eauto.
