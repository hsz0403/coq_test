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

Instance noaertsi : no_append_entries_replies_to_self_interface.
split.
auto using no_append_entries_replies_to_self_invariant.
