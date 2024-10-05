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

Lemma update_elections_data_requestVoteReply_allEntries : forall h h' t st r, allEntries (update_elections_data_requestVoteReply h h' t r st) = allEntries (fst st).
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
repeat break_match; auto.
