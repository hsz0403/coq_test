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

Theorem no_append_entries_to_self_invariant : forall net, raft_intermediate_reachable net -> no_append_entries_to_self net.
Proof using.
intros.
apply raft_net_invariant; auto.
-
apply no_append_entries_to_self_init.
-
apply no_append_entries_to_self_client_request.
-
apply no_append_entries_to_self_timeout.
-
apply no_append_entries_to_self_append_entries.
-
apply no_append_entries_to_self_append_entries_reply.
-
apply no_append_entries_to_self_request_vote.
-
apply no_append_entries_to_self_request_vote_reply.
-
apply no_append_entries_to_self_do_leader.
-
apply no_append_entries_to_self_do_generic_server.
-
apply no_append_entries_to_self_state_same_packet_subset.
-
apply no_append_entries_to_self_reboot.
