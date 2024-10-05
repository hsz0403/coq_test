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

Lemma update_elections_data_timeout_votes_intro_new : forall h st out st' ps t' h', handleTimeout h (snd st) = (out, st', ps) -> (forall t h, t = currentTerm (snd st) -> votedFor (snd st) = Some h -> In (t, h) (votes (fst st))) -> t' = currentTerm st' -> votedFor st' = Some h' -> In (t', h') (votes (update_elections_data_timeout h st)).
Proof using.
unfold update_elections_data_timeout, handleTimeout, tryToBecomeLeader.
intros.
repeat break_match; simpl in *; intuition; repeat tuple_inversion; intuition (auto; congruence).
