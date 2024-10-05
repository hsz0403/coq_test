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

Lemma update_elections_data_requestVoteReply_leaderLogs' : forall h h' t st t' ll' r, In (t', ll') (leaderLogs (update_elections_data_requestVoteReply h h' t r st)) -> In (t', ll') (leaderLogs (fst st)) \/ (r = true /\ t = currentTerm (snd st) /\ ll' = log (snd st) /\ t' = currentTerm (snd st) /\ type (snd st) = Candidate /\ wonElection (dedup name_eq_dec (h' :: votesReceived (snd st))) = true).
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
repeat break_match; auto.
simpl in *.
intuition.
find_inversion.
right.
unfold handleRequestVoteReply in *.
repeat break_match; simpl in *; intuition; try congruence; break_if; try congruence; do_bool; eauto using le_antisym.
