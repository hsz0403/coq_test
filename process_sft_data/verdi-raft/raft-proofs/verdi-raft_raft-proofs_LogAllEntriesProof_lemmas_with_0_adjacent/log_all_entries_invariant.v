Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.LogAllEntriesInterface.
Section LogAllEntries.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {tsi : term_sanity_interface}.
Ltac rewrite_goal := match goal with | H: _ = _ |- _ => rewrite H end.
Definition no_entries_past_current_term_host_lifted net := forall (h : name) e, In e (log (snd (nwState net h))) -> eTerm e <= currentTerm (snd (nwState net h)).
Instance laei : log_all_entries_interface.
split.
auto using log_all_entries_invariant.
End LogAllEntries.

Theorem log_all_entries_invariant : forall net, refined_raft_intermediate_reachable net -> log_all_entries net.
Proof using tsi rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply log_all_entries_init.
-
apply log_all_entries_client_request.
-
apply log_all_entries_timeout.
-
apply log_all_entries_append_entries.
-
apply log_all_entries_append_entries_reply.
-
apply log_all_entries_request_vote.
-
apply log_all_entries_request_vote_reply.
-
apply log_all_entries_do_leader.
-
apply log_all_entries_do_generic_server.
-
apply log_all_entries_state_same_packet_subset.
-
apply log_all_entries_reboot.
