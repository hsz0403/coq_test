Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.CroniesTermInterface.
Require Import VerdiRaft.AllEntriesTermSanityInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.AllEntriesCandidateEntriesInterface.
Section AllEntriesCandidateEntries.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cci : cronies_correct_interface}.
Context {cti : cronies_term_interface}.
Context {cei : candidate_entries_interface}.
Context {lltsi : allEntries_term_sanity_interface}.
Ltac start := red; unfold allEntries_candidateEntries; simpl; intros.
Instance aecei : allEntries_candidate_entries_interface.
Proof.
constructor.
exact allEntries_candidateEntries_invariant.
End AllEntriesCandidateEntries.

Lemma allEntries_candidateEntries_invariant : forall net, refined_raft_intermediate_reachable net -> allEntries_candidateEntries net.
Proof using cei cti cci rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply allEntries_candidateEntries_init.
-
apply allEntries_candidateEntries_client_request.
-
apply allEntries_candidateEntries_timeout.
-
apply allEntries_candidateEntries_append_entries.
-
apply allEntries_candidateEntries_append_entries_reply.
-
apply allEntries_candidateEntries_request_vote.
-
apply allEntries_candidateEntries_request_vote_reply.
-
apply allEntries_candidateEntries_do_leader.
-
apply allEntries_candidateEntries_do_generic_server.
-
apply allEntries_candidateEntries_state_same_packet_subset.
-
apply allEntries_candidateEntries_reboot.
