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

Lemma no_append_entries_to_self_state_same_packet_subset : raft_net_invariant_state_same_packet_subset no_append_entries_to_self.
Proof using.
red.
red.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
