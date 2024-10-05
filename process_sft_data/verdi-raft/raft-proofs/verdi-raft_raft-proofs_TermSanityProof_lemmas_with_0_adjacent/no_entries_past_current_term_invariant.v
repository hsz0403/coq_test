Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.TermSanityInterface.
Section TermSanityProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Instance tsi : term_sanity_interface.
Proof.
split.
auto using no_entries_past_current_term_invariant.
End TermSanityProof.

Theorem no_entries_past_current_term_invariant : forall net, raft_intermediate_reachable net -> no_entries_past_current_term net.
Proof using.
intros.
eapply raft_net_invariant; eauto.
-
apply no_entries_past_current_term_init.
-
apply no_entries_past_current_term_client_request.
-
apply no_entries_past_current_term_timeout.
-
apply no_entries_past_current_term_append_entries.
-
apply no_entries_past_current_term_append_entries_reply.
-
apply no_entries_past_current_term_request_vote.
-
apply no_entries_past_current_term_request_vote_reply.
-
apply no_entries_past_current_term_do_leader.
-
apply no_entries_past_current_term_do_generic_server.
-
apply no_entries_past_current_term_state_same_packet_subset.
-
apply no_entries_past_current_term_reboot.
