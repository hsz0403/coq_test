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

Lemma update_elections_data_appendEntries_leaderLogs : forall h st t h' pli plt es ci, leaderLogs (update_elections_data_appendEntries h st t h' pli plt es ci) = leaderLogs (fst st).
Proof using.
intros.
unfold update_elections_data_appendEntries.
repeat break_match; subst; simpl in *; auto.
