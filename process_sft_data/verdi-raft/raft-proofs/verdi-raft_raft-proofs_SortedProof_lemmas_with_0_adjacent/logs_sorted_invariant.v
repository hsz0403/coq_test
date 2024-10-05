Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.SortedInterface.
Section SortedProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {tsi : term_sanity_interface}.
Ltac find_eapply_hyp_goal := match goal with | H : _ |- _ => eapply H end.
Instance si : sorted_interface.
Proof.
split.
eauto using handleAppendEntries_logs_sorted.
eauto using handleClientRequest_logs_sorted.
auto using logs_sorted_invariant.
End SortedProof.

Theorem logs_sorted_invariant : forall net, raft_intermediate_reachable net -> logs_sorted net.
Proof using tsi.
intros.
eapply raft_net_invariant; eauto.
-
apply logs_sorted_init.
-
apply logs_sorted_client_request.
-
apply logs_sorted_timeout.
-
apply logs_sorted_append_entries.
-
apply logs_sorted_append_entries_reply.
-
apply logs_sorted_request_vote.
-
apply logs_sorted_request_vote_reply.
-
apply logs_sorted_do_leader.
-
apply logs_sorted_do_generic_server.
-
apply logs_sorted_state_same_packet_subset.
-
apply logs_sorted_reboot.
