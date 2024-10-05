Require Import VerdiRaft.Raft.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.NoAppendEntriesRepliesToSelfInterface.
Require Import VerdiRaft.NoAppendEntriesToSelfInterface.
Section NoAppendEntriesRepliesToSelf.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {naetsi : no_append_entries_to_self_interface}.
Instance noaertsi : no_append_entries_replies_to_self_interface.
split.
auto using no_append_entries_replies_to_self_invariant.
End NoAppendEntriesRepliesToSelf.

Lemma no_append_entries_replies_to_self_client_request : raft_net_invariant_client_request no_append_entries_replies_to_self.
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
unfold handleClientRequest in *; repeat break_match; find_inversion; simpl in *; intuition.
