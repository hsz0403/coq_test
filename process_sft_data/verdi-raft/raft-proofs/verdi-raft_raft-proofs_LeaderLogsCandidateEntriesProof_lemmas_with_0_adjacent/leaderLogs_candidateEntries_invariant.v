Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.CroniesTermInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.LeaderLogsCandidateEntriesInterface.
Section CandidateEntriesInterface.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cci : cronies_correct_interface}.
Context {cti : cronies_term_interface}.
Context {cei : candidate_entries_interface}.
Context {lltsi : leaderLogs_term_sanity_interface}.
Ltac start := red; unfold leaderLogs_candidateEntries; simpl; intros.
Instance llcei : leaderLogs_candidate_entries_interface.
Proof.
constructor.
exact leaderLogs_candidateEntries_invariant.
End CandidateEntriesInterface.

Lemma leaderLogs_candidateEntries_invariant : forall net, refined_raft_intermediate_reachable net -> leaderLogs_candidateEntries net.
Proof using cei cti cci rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply leaderLogs_candidateEntries_init.
-
apply leaderLogs_candidateEntries_client_request.
-
apply leaderLogs_candidateEntries_timeout.
-
apply leaderLogs_candidateEntries_append_entries.
-
apply leaderLogs_candidateEntries_append_entries_reply.
-
apply leaderLogs_candidateEntries_request_vote.
-
apply leaderLogs_candidateEntries_request_vote_reply.
-
apply leaderLogs_candidateEntries_do_leader.
-
apply leaderLogs_candidateEntries_do_generic_server.
-
apply leaderLogs_candidateEntries_state_same_packet_subset.
-
apply leaderLogs_candidateEntries_reboot.
