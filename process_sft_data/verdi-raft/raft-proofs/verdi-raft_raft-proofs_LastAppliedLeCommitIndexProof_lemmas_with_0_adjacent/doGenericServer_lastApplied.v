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

Lemma doGenericServer_lastApplied: forall (h : name) (st : raft_data) (out : list raft_output) (st' : raft_data) (ms : list (name * msg)), doGenericServer h st = (out, st', ms) -> lastApplied st' <= max (lastApplied st) (commitIndex st).
Proof using.
intros.
unfold doGenericServer in *.
break_let.
find_inversion.
simpl in *.
break_if; simpl in *; do_bool; auto.
-
use_applyEntries_spec.
subst.
simpl in *.
eauto using Max.le_max_r.
-
use_applyEntries_spec.
subst.
simpl in *.
eauto using Max.le_max_l.
