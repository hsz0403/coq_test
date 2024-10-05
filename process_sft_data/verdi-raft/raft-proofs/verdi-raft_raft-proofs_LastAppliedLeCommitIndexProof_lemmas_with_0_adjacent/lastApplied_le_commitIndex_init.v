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

Lemma lastApplied_le_commitIndex_init : raft_net_invariant_init lastApplied_le_commitIndex.
Proof using.
red.
unfold lastApplied_le_commitIndex.
intros.
simpl in *.
auto.
