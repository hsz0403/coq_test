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

Lemma votes_update_elections_data_request_vote_reply_eq : forall h st src t r st', handleRequestVoteReply h (snd st) src t r = st' -> votes (update_elections_data_requestVoteReply h src t r st) = votes (fst st).
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
repeat break_match; repeat tuple_inversion; intuition.
