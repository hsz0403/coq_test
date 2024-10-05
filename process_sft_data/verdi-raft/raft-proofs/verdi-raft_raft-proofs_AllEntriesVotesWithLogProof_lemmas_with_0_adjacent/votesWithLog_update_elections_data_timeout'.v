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

Lemma votesWithLog_update_elections_data_timeout' : forall net h out st' ps t' h' l', refined_raft_intermediate_reachable net -> handleTimeout h (snd (nwState net h)) = (out, st', ps) -> In (t', h', l') (votesWithLog (update_elections_data_timeout h (nwState net h))) -> In (t', h', l') (votesWithLog (fst (nwState net h))) \/ (t' = currentTerm st' /\ l' = log st' /\ currentTerm (snd (nwState net h)) < currentTerm st').
Proof using.
unfold update_elections_data_timeout.
intros.
repeat break_match; simpl in *; intuition; repeat tuple_inversion; intuition.
-
unfold handleTimeout, tryToBecomeLeader in *.
repeat break_match; repeat find_inversion; simpl in *; intuition.
-
unfold handleTimeout, tryToBecomeLeader in *.
repeat break_match; repeat find_inversion; simpl in *; congruence.
