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

Lemma advanceCommitIndex_commitIndex : forall st h, commitIndex st <= commitIndex (advanceCommitIndex st h).
Proof using.
intros.
unfold advanceCommitIndex.
simpl in *.
apply fold_left_max; auto.
intros.
do_in_map.
subst.
find_apply_lem_hyp filter_In.
repeat (intuition; do_bool).
