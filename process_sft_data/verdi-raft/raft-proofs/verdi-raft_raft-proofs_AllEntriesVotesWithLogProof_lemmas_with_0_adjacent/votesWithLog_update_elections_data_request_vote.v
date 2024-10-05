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

Lemma votesWithLog_update_elections_data_request_vote : forall net h t src lli llt st' m t' h' l', refined_raft_intermediate_reachable net -> handleRequestVote h (snd (nwState net h)) t src lli llt = (st', m) -> In (t', h', l') (votesWithLog (update_elections_data_requestVote h src t src lli llt (nwState net h))) -> In (t', h', l') (votesWithLog (fst (nwState net h))) \/ (t' = currentTerm st' /\ l' = log st' /\ (leaderId (snd (nwState net h)) = None \/ currentTerm (snd (nwState net h)) < currentTerm st')).
Proof using.
unfold update_elections_data_requestVote.
intros.
repeat break_match; repeat tuple_inversion; intuition; simpl in *; intuition; tuple_inversion; intuition; repeat (do_bool; intuition); try congruence; unfold raft_data, ghost_data in *; simpl in *; repeat find_rewrite; repeat find_inversion; find_copy_apply_lem_hyp handleRequestVote_currentTerm_leaderId; intuition; find_apply_lem_hyp handleRequestVote_currentTerm_leaderId'; repeat find_rewrite; try congruence; intuition.
