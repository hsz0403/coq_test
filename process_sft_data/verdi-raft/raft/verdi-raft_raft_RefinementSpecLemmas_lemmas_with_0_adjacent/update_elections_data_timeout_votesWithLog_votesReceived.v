Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Section SpecLemmas.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
End SpecLemmas.

Lemma update_elections_data_timeout_votesWithLog_votesReceived : forall h st out st' ps, handleTimeout h (snd st) = (out, st', ps) -> (votesReceived st' = votesReceived (snd st) /\ votesWithLog (update_elections_data_timeout h st) = votesWithLog (fst st) /\ type st' = Leader) \/ (votesReceived st' = [h] /\ votesWithLog (update_elections_data_timeout h st) = (currentTerm st', h, (log st')) :: votesWithLog (fst st) /\ currentTerm st' = S (currentTerm (snd st))).
Proof using.
unfold update_elections_data_timeout, handleTimeout, tryToBecomeLeader in *.
intros.
repeat break_match; simpl in *; intuition; repeat tuple_inversion; intuition; simpl in *; repeat find_inversion; intuition; try congruence.
