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

Lemma handleTimeout_same_term_votedFor_preserved : forall h st out st' ps, handleTimeout h st = (out, st', ps) -> currentTerm st' = currentTerm st -> votedFor st' = votedFor st.
Proof using.
unfold handleTimeout, tryToBecomeLeader.
intros.
repeat break_match; repeat tuple_inversion; simpl in *; auto; omega.
