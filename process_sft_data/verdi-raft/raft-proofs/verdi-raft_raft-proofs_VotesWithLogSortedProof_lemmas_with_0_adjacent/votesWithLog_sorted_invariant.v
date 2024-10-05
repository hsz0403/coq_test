Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.VotesWithLogSortedInterface.
Require Import VerdiRaft.SortedInterface.
Section VotesWithLogSorted.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {si : sorted_interface}.
Instance vwlsi : votesWithLog_sorted_interface.
Proof.
split.
exact votesWithLog_sorted_invariant.
End VotesWithLogSorted.

Lemma votesWithLog_sorted_invariant : forall net, refined_raft_intermediate_reachable net -> votesWithLog_sorted net.
Proof using si rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply votesWithLog_sorted_init.
-
apply votesWithLog_sorted_client_request.
-
apply votesWithLog_sorted_timeout.
-
apply votesWithLog_sorted_append_entries.
-
apply votesWithLog_sorted_append_entries_reply.
-
apply votesWithLog_sorted_request_vote.
-
apply votesWithLog_sorted_request_vote_reply.
-
apply votesWithLog_sorted_do_leader.
-
apply votesWithLog_sorted_do_generic_server.
-
apply votesWithLog_sorted_state_same_packet_subset.
-
apply votesWithLog_sorted_reboot.
