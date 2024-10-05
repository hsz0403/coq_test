Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.AllEntriesVotesWithLogInterface.
Require Import VerdiRaft.AllEntriesLogInterface.
Require Import VerdiRaft.VotesWithLogTermSanityInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.VotesVotesWithLogCorrespondInterface.
Section AllEntriesVotesWithLog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {aeli : allEntries_log_interface}.
Context {vwltsi : votesWithLog_term_sanity_interface}.
Context {vvwlci : votes_votesWithLog_correspond_interface}.
Context {vci : votes_correct_interface}.
Definition currentTerm_votedFor_votesWithLog net := forall h t n, (currentTerm (snd (nwState net h)) = t /\ votedFor (snd (nwState net h)) = Some n) -> exists l, In (t, n, l) (votesWithLog (fst (nwState net h))).
Instance aevwli : allEntries_votesWithLog_interface.
split.
eauto using allEntries_votesWithLog_invariant.
Defined.
End AllEntriesVotesWithLog.

Lemma allEntries_votesWithLog_request_vote : refined_raft_net_invariant_request_vote allEntries_votesWithLog.
Proof using aeli.
red.
unfold allEntries_votesWithLog.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *.
-
find_rewrite_lem update_elections_data_requestVote_allEntries.
find_copy_apply_lem_hyp handleRequestVote_currentTerm.
find_copy_eapply_lem_hyp votesWithLog_update_elections_data_request_vote; eauto.
intuition.
+
eapply_prop_hyp votesWithLog votesWithLog; eauto; intuition; right; break_exists_exists; intuition; find_higher_order_rewrite; destruct_update; simpl in *; auto.
rewrite leaderLogs_update_elections_data_requestVote.
auto.
+
subst.
find_apply_lem_hyp handleRequestVote_log.
repeat find_rewrite.
find_copy_eapply_lem_hyp allEntries_log_invariant; eauto.
intuition.
right.
break_exists_exists.
repeat find_higher_order_rewrite.
simpl in *.
destruct_update; simpl in *; intuition; try rewrite leaderLogs_update_elections_data_requestVote; eauto.
+
subst.
find_apply_lem_hyp handleRequestVote_log.
repeat find_rewrite.
find_copy_eapply_lem_hyp allEntries_log_invariant; eauto.
intuition.
right.
break_exists_exists.
repeat find_higher_order_rewrite.
simpl in *.
destruct_update; simpl in *; intuition; try rewrite leaderLogs_update_elections_data_requestVote; eauto.
-
eapply_prop_hyp votesWithLog votesWithLog; eauto; intuition; right; break_exists_exists; intuition; find_higher_order_rewrite; destruct_update; simpl in *; auto.
rewrite leaderLogs_update_elections_data_requestVote.
auto.
