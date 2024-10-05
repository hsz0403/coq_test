Require Import VerdiRaft.Raft.
Require Import VerdiRaft.LastAppliedLeCommitIndexInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.CommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Section LastAppliedLeCommitIndex.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Instance lalcii : lastApplied_le_commitIndex_interface.
split.
auto using lastApplied_le_commitIndex_invariant.
End LastAppliedLeCommitIndex.

Lemma doLeader_same_commitIndex : forall st (os : list raft_output) (d' : raft_data) (ms : list (name * msg)) (h0 : name), doLeader st h0 = (os, d', ms) -> commitIndex st <= commitIndex d'.
Proof using.
intros.
unfold doLeader in *.
repeat break_match; tuple_inversion; auto; eauto using advanceCommitIndex_commitIndex.
eapply le_trans; [eapply advanceCommitIndex_commitIndex with (h := h0)|]; eauto.
