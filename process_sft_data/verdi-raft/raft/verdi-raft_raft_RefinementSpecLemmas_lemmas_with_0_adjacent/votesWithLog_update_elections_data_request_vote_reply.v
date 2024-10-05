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

Lemma votesWithLog_update_elections_data_request_vote_reply : forall h st src t r st' t' h' l', handleRequestVoteReply h (snd st) src t r = st' -> In (t', h', l') (votesWithLog (update_elections_data_requestVoteReply h src t r st)) -> In (t', h', l') (votesWithLog (fst st)).
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
repeat break_match; repeat tuple_inversion; intuition.
