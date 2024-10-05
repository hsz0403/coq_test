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

Lemma fold_left_max : forall l y z, (forall x, In x l -> y <= x) -> y <= z -> y <= fold_left max l z.
Proof using.
induction l; simpl in *; auto.
intros.
specialize (IHl y (max z a)).
forward IHl; eauto.
concludes.
forward IHl; [eapply le_trans; eauto; eauto using Max.le_max_l|].
concludes.
auto.
