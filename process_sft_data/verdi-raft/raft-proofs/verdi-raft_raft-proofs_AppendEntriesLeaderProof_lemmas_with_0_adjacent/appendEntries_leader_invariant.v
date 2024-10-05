Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.AppendEntriesRequestsCameFromLeadersInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.OneLeaderPerTermInterface.
Require Import VerdiRaft.AppendEntriesLeaderInterface.
Section AppendEntriesLeader.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {aecfli : append_entries_came_from_leaders_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {lltsi : leaderLogs_term_sanity_interface}.
Context {olpti : one_leader_per_term_interface}.
Definition type_term_log_monotonic st st' := type st' = Leader -> type st = Leader /\ currentTerm st' = currentTerm st /\ (forall e, In e (log st) -> In e (log st')).
Notation appendEntries_leader_predicate ps st := (forall p t lid pli plt es lci e, In p ps -> pBody p = AppendEntries t lid pli plt es lci -> In e es -> currentTerm st = t -> type st = Leader -> In e (log st)).
Instance appendeli : append_entries_leader_interface.
Proof.
split.
exact appendEntries_leader_invariant.
End AppendEntriesLeader.

Lemma appendEntries_leader_invariant : forall net, refined_raft_intermediate_reachable net -> appendEntries_leader net.
Proof using olpti lltsi ollpti aecfli rri.
intros.
apply refined_raft_net_invariant'; auto.
-
apply appendEntries_leader_init.
-
apply refined_raft_net_invariant_client_request'_weak.
apply appendEntries_leader_client_request.
-
apply refined_raft_net_invariant_timeout'_weak.
apply appendEntries_leader_timeout.
-
apply refined_raft_net_invariant_append_entries'_weak.
apply appendEntries_leader_append_entries.
-
apply refined_raft_net_invariant_append_entries_reply'_weak.
apply appendEntries_leader_append_entries_reply.
-
apply refined_raft_net_invariant_request_vote'_weak.
apply appendEntries_leader_request_vote.
-
apply appendEntries_leader_request_vote_reply.
-
apply refined_raft_net_invariant_do_leader'_weak.
apply appendEntries_leader_do_leader.
-
apply refined_raft_net_invariant_do_generic_server'_weak.
apply appendEntries_leader_do_generic_server.
-
apply appendEntries_leader_state_same_packet_subset.
-
apply refined_raft_net_invariant_reboot'_weak.
apply appendEntries_leader_reboot.
