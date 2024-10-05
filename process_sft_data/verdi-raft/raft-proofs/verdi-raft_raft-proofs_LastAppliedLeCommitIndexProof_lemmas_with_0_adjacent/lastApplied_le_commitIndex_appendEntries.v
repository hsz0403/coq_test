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

Lemma lastApplied_le_commitIndex_appendEntries : raft_net_invariant_append_entries lastApplied_le_commitIndex.
Proof using.
red.
unfold lastApplied_le_commitIndex.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
find_copy_apply_lem_hyp handleAppendEntries_same_lastApplied.
repeat find_rewrite.
find_apply_lem_hyp handleAppendEntries_log_detailed.
intuition; repeat find_rewrite; eauto; eapply le_trans; eauto; eauto using Max.le_max_l.
