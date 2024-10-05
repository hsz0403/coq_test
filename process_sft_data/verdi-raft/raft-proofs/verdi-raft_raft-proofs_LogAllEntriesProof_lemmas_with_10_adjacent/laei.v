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

Lemma log_all_entries_request_vote : refined_raft_net_invariant_request_vote log_all_entries.
Proof using tsi rri.
red.
unfold log_all_entries.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto; [|copy_eapply_prop_hyp In In; repeat find_rewrite; auto].
find_copy_apply_lem_hyp handleRequestVote_log.
find_rewrite.
find_copy_apply_lem_hyp handleRequestVote_type_term.
rewrite update_elections_data_requestVote_allEntries.
intuition; repeat find_rewrite; copy_eapply_prop_hyp In In; repeat find_rewrite; auto.
find_apply_lem_hyp no_entries_past_current_term_host_lifted_invariant; auto.
repeat find_rewrite.
Admitted.

Lemma log_all_entries_request_vote_reply : refined_raft_net_invariant_request_vote_reply log_all_entries.
Proof using tsi rri.
red.
unfold log_all_entries.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto; [|copy_eapply_prop_hyp In In; repeat find_rewrite; auto].
find_erewrite_lem handleRequestVoteReply_log.
rewrite update_elections_data_requestVoteReply_allEntries.
match goal with | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?v] => pose proof handleRequestVoteReply_type h st h' t v (handleRequestVoteReply h st h' t v) end.
intuition; repeat find_rewrite; copy_eapply_prop_hyp In In; repeat find_rewrite; auto.
find_apply_lem_hyp no_entries_past_current_term_host_lifted_invariant; auto.
repeat find_rewrite.
unfold raft_data in *.
simpl in *.
unfold raft_data in *.
simpl in *.
Admitted.

Lemma log_all_entries_do_leader : refined_raft_net_invariant_do_leader log_all_entries.
Proof using.
red.
unfold log_all_entries.
intros.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto; [|copy_eapply_prop_hyp In In; repeat find_rewrite; auto].
find_copy_apply_lem_hyp doLeader_type; intuition.
find_apply_lem_hyp doLeader_log.
repeat find_rewrite.
Admitted.

Lemma log_all_entries_do_generic_server : refined_raft_net_invariant_do_generic_server log_all_entries.
Proof using.
red.
unfold log_all_entries.
intros.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto; [|copy_eapply_prop_hyp In In; repeat find_rewrite; auto].
find_copy_apply_lem_hyp doGenericServer_type; intuition.
find_apply_lem_hyp doGenericServer_log.
repeat find_rewrite.
Admitted.

Lemma log_all_entries_client_request : refined_raft_net_invariant_client_request log_all_entries.
Proof using.
red.
unfold log_all_entries.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto; [|copy_eapply_prop_hyp In In; repeat find_rewrite; auto].
find_copy_apply_lem_hyp update_elections_data_client_request_log_allEntries.
find_apply_lem_hyp handleClientRequest_type.
intuition; repeat find_rewrite; [copy_eapply_prop_hyp In In; repeat find_rewrite; auto|].
break_exists.
intuition.
repeat find_rewrite.
simpl in *.
intuition; subst; auto.
Admitted.

Lemma log_all_entries_timeout : refined_raft_net_invariant_timeout log_all_entries.
Proof using tsi rri.
red.
unfold log_all_entries.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto; [|copy_eapply_prop_hyp In In; repeat find_rewrite; auto].
find_copy_apply_lem_hyp handleTimeout_log_same.
rewrite update_elections_data_timeout_allEntries.
find_apply_lem_hyp handleTimeout_type_strong.
intuition; repeat find_rewrite; copy_eapply_prop_hyp In In; repeat find_rewrite; auto.
find_apply_lem_hyp no_entries_past_current_term_host_lifted_invariant; auto.
repeat find_rewrite.
unfold raft_data in *.
simpl in *.
unfold raft_data in *.
simpl in *.
Admitted.

Lemma log_all_entries_reboot : refined_raft_net_invariant_reboot log_all_entries.
Proof using.
red.
unfold log_all_entries.
intros.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
simpl in *.
repeat find_higher_order_rewrite.
Admitted.

Lemma log_all_entries_init : refined_raft_net_invariant_init log_all_entries.
Proof using.
red.
unfold log_all_entries.
intros.
simpl in *.
Admitted.

Lemma log_all_entries_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset log_all_entries.
Proof using.
red.
unfold log_all_entries.
intros.
simpl in *.
repeat find_reverse_higher_order_rewrite.
Admitted.

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
Admitted.

Instance laei : log_all_entries_interface.
split.
auto using log_all_entries_invariant.
