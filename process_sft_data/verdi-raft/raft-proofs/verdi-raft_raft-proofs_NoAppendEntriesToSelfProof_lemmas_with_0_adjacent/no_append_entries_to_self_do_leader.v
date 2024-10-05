Require Import VerdiRaft.Raft.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.NoAppendEntriesToSelfInterface.
Section NoAppendEntriesToSelf.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Instance noaetsi : no_append_entries_to_self_interface.
split.
exact no_append_entries_to_self_invariant.
End NoAppendEntriesToSelf.

Lemma no_append_entries_to_self_do_leader : raft_net_invariant_do_leader no_append_entries_to_self.
Proof using.
red.
red.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
do_in_map.
subst.
simpl in *.
find_eapply_lem_hyp doLeader_no_messages_to_self; eauto.
