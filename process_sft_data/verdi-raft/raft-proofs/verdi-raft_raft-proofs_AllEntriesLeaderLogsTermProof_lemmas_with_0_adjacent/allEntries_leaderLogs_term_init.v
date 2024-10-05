Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.AllEntriesLeaderLogsTermInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Section AllEntriesLeaderLogsTerm.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {aerlli : append_entries_leaderLogs_interface}.
Instance aellti : allEntries_leaderLogs_term_interface.
split.
exact allEntries_leaderLogs_term_invariant.
End AllEntriesLeaderLogsTerm.

Lemma allEntries_leaderLogs_term_init : refined_raft_net_invariant_init allEntries_leaderLogs_term.
Proof using.
unfold refined_raft_net_invariant_init, allEntries_leaderLogs_term.
simpl.
intuition.
