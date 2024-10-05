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

Lemma update_elections_data_timeout_votedFor : forall h cid st out st' m, handleTimeout h (snd st) = (out, st', m) -> votedFor st' = Some cid -> (votedFor (snd st) = Some cid /\ currentTerm st' = currentTerm (snd st) /\ type st' = type (snd st) /\ votesWithLog (update_elections_data_timeout h st) = votesWithLog (fst st)) \/ (cid = h /\ currentTerm st' = S (currentTerm (snd st)) /\ votesWithLog (update_elections_data_timeout h st) = (currentTerm st', cid, (log st')) :: votesWithLog (fst st)).
Proof using.
intros.
unfold update_elections_data_timeout.
repeat find_rewrite.
unfold handleTimeout, tryToBecomeLeader in *.
repeat break_match; repeat find_inversion; simpl in *; auto; try congruence; find_inversion; auto.
