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

Lemma appendEntries_leader_request_vote_reply : refined_raft_net_invariant_request_vote_reply' appendEntries_leader.
Proof using lltsi ollpti aecfli.
unfold refined_raft_net_invariant_request_vote_reply', appendEntries_leader.
simpl.
intros.
find_apply_hyp_hyp.
find_copy_apply_lem_hyp handleRequestVoteReply_spec'.
repeat find_higher_order_rewrite.
update_destruct_simplify.
-
rewrite handleRequestVoteReply_same_log.
intuition; try congruence.
+
repeat find_rewrite.
eauto using in_middle_insert with *.
+
subst.
match goal with | [ H : pBody _ = AppendEntries _ _ _ _ _ _ |- _ ] => copy_eapply (append_entries_came_from_leaders_invariant net) H end; eauto.
break_exists.
assert (pDst p = pSrc p0).
{
destruct (name_eq_dec (pDst p) (pSrc p0)); auto.
find_copy_apply_lem_hyp update_elections_data_RVR_ascending_leaderLog; auto.
break_exists.
repeat find_rewrite.
match goal with | [ H : refined_raft_intermediate_reachable ?the_net, H': In (?the_t, ?the_ll) (leaderLogs (update_elections_data_requestVoteReply _ _ _ _ _)), H'' : In (_, ?the_ll') (leaderLogs (fst _)) |- _ ] => match the_net with | context [ st' ] => apply one_leaderLog_per_term_host_invariant with (net0 := the_net) (t := the_t) (ll := the_ll) (ll' := the_ll') end end; auto; simpl; repeat find_higher_order_rewrite; rewrite_update; simpl; auto.
}
exfalso.
repeat find_rewrite.
eapply lt_irrefl.
eapply leaderLogs_currentTerm_sanity_candidate_invariant; [|eauto|]; auto.
-
Admitted.

Lemma doLeader_TTLM : forall st h os st' ms, doLeader st h = (os, st', ms) -> type_term_log_monotonic st st'.
Proof using.
unfold doLeader, type_term_log_monotonic.
intros.
Admitted.

Lemma doLeader_message_entries : forall st h os st' ms m t n pli plt es ci e, doLeader st h = (os, st', ms) -> In m ms -> snd m = AppendEntries t n pli plt es ci -> In e es -> currentTerm st = t /\ type st = Leader /\ In e (log st).
Proof using.
intros.
unfold doLeader, advanceCommitIndex in *.
break_match; try solve [find_inversion; simpl in *; intuition].
break_if; try solve [find_inversion; simpl in *; intuition].
find_inversion.
simpl.
do_in_map.
subst.
simpl in *.
find_inversion.
Admitted.

Lemma lifted_one_leader_per_term : forall net h h', refined_raft_intermediate_reachable net -> currentTerm (snd (nwState net h)) = currentTerm (snd (nwState net h')) -> type (snd (nwState net h)) = Leader -> type (snd (nwState net h')) = Leader -> h = h'.
Proof using olpti rri.
intros.
Admitted.

Lemma appendEntries_leader_do_leader : refined_raft_net_invariant_do_leader appendEntries_leader.
Proof using olpti rri.
unfold refined_raft_net_invariant_do_leader, appendEntries_leader.
simpl.
intros.
find_apply_hyp_hyp.
intuition.
-
repeat find_higher_order_rewrite.
update_destruct_simplify.
+
eapply appendEntries_leader_predicate_TTLM_preserved; eauto using doLeader_TTLM.
match goal with | [ H : nwState ?net ?h = (?gd, ?d) |- _ ] => replace d with (snd (nwState net h)) in * by (rewrite H; auto) end.
eauto.
+
eauto.
-
do_in_map.
subst.
simpl in *.
repeat find_higher_order_rewrite.
find_copy_eapply_lem_hyp (doLeader_message_entries d); match goal with | [ H : nwState ?net ?h = (?gd, ?d) |- _ ] => replace d with (snd (nwState net h)) in * by (rewrite H; auto) end; eauto; break_and.
update_destruct_simplify.
+
erewrite doLeader_same_log; eauto.
+
exfalso.
Admitted.

Lemma doGenericServer_TTLM : forall h st os st' ps, doGenericServer h st = (os, st', ps) -> type_term_log_monotonic st st'.
Proof using.
unfold type_term_log_monotonic, doGenericServer.
intros.
Admitted.

Lemma appendEntries_leader_do_generic_server : refined_raft_net_invariant_do_generic_server appendEntries_leader.
Proof using.
unfold refined_raft_net_invariant_do_generic_server, appendEntries_leader.
simpl.
intros.
find_apply_hyp_hyp.
intuition.
-
repeat find_higher_order_rewrite.
update_destruct_simplify.
+
eapply appendEntries_leader_predicate_TTLM_preserved; eauto using doGenericServer_TTLM.
match goal with | [ H : nwState ?net ?h = (?gd, ?d) |- _ ] => replace d with (snd (nwState net h)) in * by (rewrite H; auto) end.
eauto.
+
eauto.
-
find_apply_lem_hyp doGenericServer_packets.
subst.
simpl in *.
Admitted.

Lemma appendEntries_leader_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset appendEntries_leader.
Proof using.
unfold refined_raft_net_invariant_state_same_packet_subset, appendEntries_leader.
simpl.
intros.
repeat find_reverse_higher_order_rewrite.
Admitted.

Lemma appendEntries_leader_reboot : refined_raft_net_invariant_reboot appendEntries_leader.
Proof using.
unfold refined_raft_net_invariant_reboot, appendEntries_leader, reboot.
simpl.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
-
discriminate.
-
Admitted.

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
Admitted.

Instance appendeli : append_entries_leader_interface.
Proof.
split.
exact appendEntries_leader_invariant.
