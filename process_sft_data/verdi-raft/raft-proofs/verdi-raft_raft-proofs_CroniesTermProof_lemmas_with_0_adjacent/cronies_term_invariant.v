Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CroniesTermInterface.
Section CroniesTermProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Instance cti : cronies_term_interface.
Proof.
split.
auto using cronies_term_invariant.
End CroniesTermProof.

Theorem cronies_term_invariant : forall net, refined_raft_intermediate_reachable net -> cronies_term net.
Proof using rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply cronies_term_init.
-
apply cronies_term_client_request.
-
apply cronies_term_timeout.
-
apply cronies_term_append_entries.
-
apply cronies_term_append_entries_reply.
-
apply cronies_term_request_vote.
-
apply cronies_term_request_vote_reply.
-
apply cronies_term_do_leader.
-
apply cronies_term_do_generic_server.
-
apply cronies_term_state_same_packet_subset.
-
apply cronies_term_reboot.
