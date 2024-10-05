Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.AllEntriesVotesWithLogInterface.
Require Import VerdiRaft.AllEntriesLogInterface.
Require Import VerdiRaft.VotesWithLogTermSanityInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.VotesVotesWithLogCorrespondInterface.
Section AllEntriesVotesWithLog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {aeli : allEntries_log_interface}.
Context {vwltsi : votesWithLog_term_sanity_interface}.
Context {vvwlci : votes_votesWithLog_correspond_interface}.
Context {vci : votes_correct_interface}.
Definition currentTerm_votedFor_votesWithLog net := forall h t n, (currentTerm (snd (nwState net h)) = t /\ votedFor (snd (nwState net h)) = Some n) -> exists l, In (t, n, l) (votesWithLog (fst (nwState net h))).
Instance aevwli : allEntries_votesWithLog_interface.
split.
eauto using allEntries_votesWithLog_invariant.
Defined.
End AllEntriesVotesWithLog.

Theorem allEntries_votesWithLog_invariant : forall net, refined_raft_intermediate_reachable net -> allEntries_votesWithLog net.
Proof using vwltsi aeli rri.
intros.
eapply refined_raft_net_invariant; eauto.
-
exact allEntries_votesWithLog_init.
-
exact allEntries_votesWithLog_client_request.
-
exact allEntries_votesWithLog_timeout.
-
exact allEntries_votesWithLog_append_entries.
-
exact allEntries_votesWithLog_append_entries_reply.
-
exact allEntries_votesWithLog_request_vote.
-
exact allEntries_votesWithLog_request_vote_reply.
-
exact allEntries_votesWithLog_do_leader.
-
exact allEntries_votesWithLog_do_generic_server.
-
exact allEntries_votesWithLog_state_same_packet_subset.
-
exact allEntries_votesWithLog_reboot.
