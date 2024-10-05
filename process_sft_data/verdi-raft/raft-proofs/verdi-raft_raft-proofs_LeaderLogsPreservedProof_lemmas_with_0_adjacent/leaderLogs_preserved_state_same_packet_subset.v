Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RefinementCommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeaderLogsPreservedInterface.
Require Import VerdiRaft.LogsLeaderLogsInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.LeaderLogsCandidateEntriesInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Section LeaderLogsPreserved.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {llli : logs_leaderLogs_interface}.
Context {lltsi : leaderLogs_term_sanity_interface}.
Context {llcei : leaderLogs_candidate_entries_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Instance llpi : leaderLogs_preserved_interface.
split.
eauto using leaderLogs_preserved_invariant.
Defined.
End LeaderLogsPreserved.

Lemma leaderLogs_preserved_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset leaderLogs_preserved.
Proof using.
red.
unfold leaderLogs_preserved.
intros.
simpl in *.
repeat find_reverse_higher_order_rewrite.
eauto.
