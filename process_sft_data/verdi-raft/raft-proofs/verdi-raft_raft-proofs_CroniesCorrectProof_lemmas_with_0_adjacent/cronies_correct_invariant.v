Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CandidatesVoteForSelvesInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Section CroniesCorrectProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {vci : votes_correct_interface}.
Context {cvfsi : candidates_vote_for_selves_interface}.
Instance cci : cronies_correct_interface.
Proof.
split.
auto using cronies_correct_invariant.
End CroniesCorrectProof.

Theorem cronies_correct_invariant : forall (net : network), refined_raft_intermediate_reachable net -> cronies_correct net.
Proof using cvfsi vci rri.
intros.
eapply refined_raft_net_invariant; eauto.
-
apply cronies_correct_init.
-
apply cronies_correct_client_request.
-
apply cronies_correct_timeout.
-
apply cronies_correct_append_entries.
-
apply cronies_correct_append_entries_reply.
-
apply cronies_correct_request_vote.
-
apply cronies_correct_request_vote_reply.
-
apply cronies_correct_do_leader.
-
apply cronies_correct_do_generic_server.
-
apply cronies_correct_state_same_packet_subset.
-
apply cronies_correct_reboot.
