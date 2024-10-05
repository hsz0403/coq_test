Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.CroniesTermInterface.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CandidateEntriesInterface.
Section CandidateEntriesProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cti : cronies_term_interface}.
Context {tsi : term_sanity_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Ltac prove_in := match goal with | [ _ : nwPackets ?net = _, _ : In (?p : packet) _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition) | [ _ : nwPackets ?net = _, _ : pBody ?p = _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; intuition) end.
Instance cei : candidate_entries_interface.
Proof.
split.
auto using candidate_entries_invariant.
End CandidateEntriesProof.

Theorem candidate_entries_invariant : forall (net : network), refined_raft_intermediate_reachable net -> CandidateEntries net.
Proof using cci cti rri.
intros.
eapply refined_raft_net_invariant; eauto.
-
apply candidate_entries_init.
-
apply candidate_entries_client_request.
-
apply candidate_entries_timeout.
-
apply candidate_entries_append_entries.
-
apply candidate_entries_append_entries_reply.
-
apply candidate_entries_request_vote.
-
apply candidate_entries_request_vote_reply.
-
apply candidate_entries_do_leader.
-
apply candidate_entries_do_generic_server.
-
apply candidate_entries_state_same_packet_subset.
-
apply candidate_entries_reboot.
