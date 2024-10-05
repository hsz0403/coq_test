Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.AllEntriesLeaderSublogInterface.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.AllEntriesCandidateEntriesInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.OneLeaderPerTermInterface.
Section AllEntriesLeaderSublog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cei : candidate_entries_interface}.
Context {lsi : leader_sublog_interface}.
Context {olpti : one_leader_per_term_interface}.
Context {aecei : allEntries_candidate_entries_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Hint Resolve map_snd : core.
Instance aelsi : allEntries_leader_sublog_interface.
split.
intros.
apply refined_raft_net_invariant; auto.
-
apply allEntries_leader_sublog_init.
-
apply allEntries_leader_sublog_client_request.
-
apply allEntries_leader_sublog_timeout.
-
apply allEntries_leader_sublog_append_entries.
-
apply allEntries_leader_sublog_append_entries_reply.
-
apply allEntries_leader_sublog_request_vote.
-
apply allEntries_leader_sublog_request_vote_reply.
-
apply allEntries_leader_sublog_do_leader.
-
apply allEntries_leader_sublog_do_generic_server.
-
apply allEntries_leader_sublog_state_same_packet_subset.
-
apply allEntries_leader_sublog_reboot.
End AllEntriesLeaderSublog.

Lemma allEntries_leader_sublog_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset allEntries_leader_sublog.
Proof using.
red.
unfold allEntries_leader_sublog.
intros.
simpl in *.
repeat find_reverse_higher_order_rewrite.
eauto.
