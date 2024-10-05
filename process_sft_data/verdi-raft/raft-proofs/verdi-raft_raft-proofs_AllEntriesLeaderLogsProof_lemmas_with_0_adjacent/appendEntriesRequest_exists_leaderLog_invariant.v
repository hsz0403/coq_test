Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.AppendEntriesRequestsCameFromLeadersInterface.
Require Import VerdiRaft.AllEntriesLogInterface.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Require Import VerdiRaft.AllEntriesLeaderLogsInterface.
Section AllEntriesLeaderLogs.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {aerlli : append_entries_leaderLogs_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {llsi : leaderLogs_sorted_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Context {aercfli : append_entries_came_from_leaders_interface}.
Context {aeli : allEntries_log_interface}.
Context {lsi : leader_sublog_interface}.
Context {lhsi : leaders_have_leaderLogs_strong_interface}.
Instance aelli : all_entries_leader_logs_interface.
Proof.
split.
intros.
red.
intuition.
-
auto using leader_without_missing_entry_invariant.
-
auto using appendEntriesRequest_exists_leaderLog_invariant.
-
auto using appendEntriesRequest_leaderLog_not_in_invariant.
-
auto using leaderLogs_leader_invariant.
End AllEntriesLeaderLogs.

Lemma appendEntriesRequest_exists_leaderLog_invariant : forall net, refined_raft_intermediate_reachable net -> appendEntriesRequest_exists_leaderLog net.
Proof using aercfli.
intros.
unfold appendEntriesRequest_exists_leaderLog.
apply append_entries_came_from_leaders_invariant; auto.
