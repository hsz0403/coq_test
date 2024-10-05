Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Require Import VerdiRaft.NextIndexSafetyInterface.
Section AppendEntriesRequestLeaderLogs.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
Context {rri : raft_refinement_interface}.
Context {si : sorted_interface}.
Context {lmi : log_matching_interface}.
Context {nisi : nextIndex_safety_interface}.
Ltac start := red; unfold append_entries_leaderLogs; intros; subst; simpl in *; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *.
Ltac prove_in := match goal with | [ _ : nwPackets ?net = _, _ : In (?p : packet) _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition) | [ _ : nwPackets ?net = _, _ : pBody ?p = _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; intuition) end.
Instance aerlli : append_entries_leaderLogs_interface.
split.
exact append_entries_leaderLogs_invariant.
End AppendEntriesRequestLeaderLogs.

Theorem append_entries_leaderLogs_invariant : forall net, refined_raft_intermediate_reachable net -> append_entries_leaderLogs net.
Proof using nisi lmi si rri lhllsi.
intros.
apply refined_raft_net_invariant; auto.
-
apply append_entries_leaderLogs_init.
-
apply append_entries_leaderLogs_clientRequest.
-
apply append_entries_leaderLogs_timeout.
-
apply append_entries_leaderLogs_appendEntries.
-
apply append_entries_leaderLogs_appendEntriesReply.
-
apply append_entries_leaderLogs_requestVote.
-
apply append_entries_leaderLogs_requestVoteReply.
-
apply append_entries_leaderLogs_doLeader.
-
apply append_entries_leaderLogs_doGenericServer.
-
apply append_entries_leaderLogs_state_same_packets_subset.
-
apply append_entries_leaderLogs_reboot.
