Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CroniesTermInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.RefinementCommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.PrevLogCandidateEntriesTermInterface.
Section PrevLogCandidateEntriesTerm.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cei : candidate_entries_interface}.
Context {cti : cronies_term_interface}.
Context {cci : cronies_correct_interface}.
Instance plceti : prevLog_candidateEntriesTerm_interface.
Proof.
constructor.
apply prevLog_candidateEntriesTerm_invariant.
End PrevLogCandidateEntriesTerm.

Lemma prevLog_candidateEntriesTerm_invariant : forall net, refined_raft_intermediate_reachable net -> prevLog_candidateEntriesTerm net.
Proof using cci cti cei rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply prevLog_candidateEntriesTerm_init.
-
apply prevLog_candidateEntriesTerm_client_request.
-
apply prevLog_candidateEntriesTerm_timeout.
-
apply prevLog_candidateEntriesTerm_append_entries.
-
apply prevLog_candidateEntriesTerm_append_entries_reply.
-
apply prevLog_candidateEntriesTerm_request_vote.
-
apply prevLog_candidateEntriesTerm_request_vote_reply.
-
apply prevLog_candidateEntriesTerm_do_leader.
-
apply prevLog_candidateEntriesTerm_do_generic_server.
-
apply prevLog_candidateEntriesTerm_state_same_packet_subset.
-
apply prevLog_candidateEntriesTerm_reboot.
