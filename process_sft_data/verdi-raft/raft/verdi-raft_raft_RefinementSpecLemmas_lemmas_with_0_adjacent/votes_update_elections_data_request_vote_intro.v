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

Lemma votes_update_elections_data_request_vote_intro : forall h st t src lli llt st' m h', handleRequestVote h (snd st) t src lli llt = (st', m) -> votedFor st' = Some h' -> currentTerm (snd st) < currentTerm st' \/ votedFor (snd st) = None -> In (currentTerm st', h') (votes (update_elections_data_requestVote h src t src lli llt st)).
Proof using.
unfold update_elections_data_requestVote.
intros.
repeat break_match; repeat tuple_inversion; do_bool; intuition; simpl in *; intuition; do_bool; try discriminate; intuition try congruence.
omega.
