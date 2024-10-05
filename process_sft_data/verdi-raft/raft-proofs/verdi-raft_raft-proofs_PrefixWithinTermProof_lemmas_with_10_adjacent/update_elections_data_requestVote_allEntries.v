Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.PrefixWithinTermInterface.
Require Import VerdiRaft.LogsLeaderLogsInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.LeaderLogsSublogInterface.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.NextIndexSafetyInterface.
Require Import VerdiRaft.LeaderLogsContiguousInterface.
Require Import VerdiRaft.AllEntriesLogMatchingInterface.
Require Import VerdiRaft.AppendEntriesRequestTermSanityInterface.
Require Import VerdiRaft.AllEntriesLeaderSublogInterface.
Section PrefixWithinTerm.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {llli : logs_leaderLogs_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {llsi : leaderLogs_sorted_interface}.
Context {llsli : leaderLogs_sublog_interface}.
Context {lsli : leader_sublog_interface}.
Context {nisi : nextIndex_safety_interface}.
Context {llci : leaderLogs_contiguous_interface}.
Context {aelmi : allEntries_log_matching_interface}.
Context {aertsi : append_entries_request_term_sanity_interface}.
Context {aelsi : allEntries_leader_sublog_interface}.
Definition lift_leader_sublog : forall net leader e h, refined_raft_intermediate_reachable net -> type (snd (nwState net leader)) = Leader -> In e (log (snd (nwState net h))) -> eTerm e = currentTerm (snd (nwState net leader)) -> In e (log (snd (nwState net leader))).
Proof using lsli rri.
intros.
pose proof lift_prop leader_sublog_host_invariant.
conclude_using ltac:(apply leader_sublog_invariant_invariant).
find_apply_hyp_hyp.
match goal with | H : leader_sublog_host_invariant _ |- _ => specialize (H leader e h) end.
repeat find_rewrite_lem deghost_spec.
intuition.
Definition lift_leader_sublog_nw : forall net leader p t leaderId prevLogIndex prevLogTerm entries leaderCommit e, refined_raft_intermediate_reachable net -> type (snd (nwState net leader)) = Leader -> In p (nwPackets net) -> pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit -> In e entries -> eTerm e = currentTerm (snd (nwState net leader)) -> In e (log (snd (nwState net leader))).
Proof using lsli rri.
intros.
pose proof lift_prop leader_sublog_nw_invariant.
conclude_using ltac:(apply leader_sublog_invariant_invariant).
find_apply_hyp_hyp.
find_apply_lem_hyp exists_deghosted_packet.
match goal with | H : exists _, _ |- _ => destruct H as [q] end.
break_and.
match goal with | H : leader_sublog_nw_invariant _ |- _ => specialize (H leader q t leaderId prevLogIndex prevLogTerm entries leaderCommit e) end.
repeat find_rewrite_lem deghost_spec.
subst.
simpl in *.
intuition.
Definition append_entries_append_entries_prefix_within_term_nw net := forall p t n pli plt es ci p' t' n' pli' plt' es' ci' e e', In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> In p' (nwPackets net) -> pBody p' = AppendEntries t' n' pli' plt' es' ci' -> eTerm e = eTerm e' -> eIndex e <= eIndex e' -> In e es -> In e' es' -> (In e es' \/ (eIndex e = pli' /\ eTerm e = plt') \/ (eIndex e < pli' /\ eTerm e <= plt')).
Definition locked_or x y := x \/ y.
Definition log_leaderLogs_prefix_within_term net := forall h t ll leader, In (t, ll) (leaderLogs (fst (nwState net leader))) -> prefix_within_term (log (snd (nwState net h))) ll.
Definition allEntries_log_prefix_within_term net := forall h h', prefix_within_term (map snd (allEntries (fst (nwState net h)))) (log (snd (nwState net h'))).
Definition allEntries_append_entries_prefix_within_term_nw net := forall p t n pli plt es ci h e e', In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> eTerm e = eTerm e' -> eIndex e <= eIndex e' -> In e (map snd (allEntries (fst (nwState net h)))) -> In e' es -> (In e es \/ (eIndex e = pli /\ eTerm e = plt) \/ (eIndex e < pli /\ eTerm e <= plt)).
Definition append_entries_leaderLogs_prefix_within_term net := forall p t n pli plt es ci h t' ll, In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> In (t', ll) (leaderLogs (fst (nwState net h))) -> prefix_within_term es ll.
Definition append_entries_log_prefix_within_term net := forall p t n pli plt es ci h, In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> prefix_within_term es (log (snd (nwState net h))).
Definition prefix_within_term_inductive net := allEntries_leaderLogs_prefix_within_term net /\ log_leaderLogs_prefix_within_term net /\ allEntries_log_prefix_within_term net /\ allEntries_append_entries_prefix_within_term_nw net /\ append_entries_leaderLogs_prefix_within_term net /\ append_entries_log_prefix_within_term net.
Instance pwti : prefix_within_term_interface.
split; intros.
-
apply prefix_within_term_inductive_invariant.
auto.
-
apply log_log_prefix_within_term_invariant.
auto.
Defined.
End PrefixWithinTerm.

Lemma lift_nextIndex_safety : forall net, refined_raft_intermediate_reachable net -> nextIndex_safety (deghost net).
Proof using nisi rri.
intros.
Admitted.

Lemma nextIndex_sanity : forall net h h', refined_raft_intermediate_reachable net -> type (snd (nwState net h)) = Leader -> pred (getNextIndex (snd (nwState net h)) h') <> 0 -> exists e, findAtIndex (log (snd (nwState net h))) (pred (getNextIndex (snd (nwState net h)) h')) = Some e.
Proof using nisi rlmli rri.
intros.
find_copy_apply_lem_hyp entries_contiguous_invariant.
find_copy_apply_lem_hyp lift_nextIndex_safety.
assert (pred (getNextIndex (snd (nwState net h)) h') > 0) by omega.
unfold nextIndex_safety in *.
match goal with | H : forall _ _, type _ = _ -> _ |- _ => specialize (H h h') end.
intuition.
unfold entries_contiguous in *.
specialize (H2 h).
unfold contiguous_range_exact_lo in *.
intuition.
match goal with | H : forall _, _ < _ <= _ -> _ |- _ => specialize (H (pred (getNextIndex (snd (nwState net h)) h'))) end.
unfold raft_refined_base_params in *.
repeat find_rewrite_lem deghost_spec.
intuition.
break_exists_exists.
intuition.
find_apply_lem_hyp entries_sorted_invariant.
Admitted.

Lemma prefix_within_term_subset : forall l1 l1' l2, prefix_within_term l1' l2 -> (forall e, In e l1 -> In e l1') -> prefix_within_term l1 l2.
Proof using.
Admitted.

Lemma prefix_within_term_inductive_do_leader : refined_raft_net_invariant_do_leader prefix_within_term_inductive.
Proof using nisi ollpti rlmli llli rri.
red.
unfold prefix_within_term_inductive.
intros.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
intuition.
-
unfold allEntries_leaderLogs_prefix_within_term in *.
simpl in *.
intros.
repeat find_higher_order_rewrite.
repeat destruct_update; simpl in *; eauto.
-
unfold log_leaderLogs_prefix_within_term in *.
simpl in *.
intros.
repeat find_higher_order_rewrite.
repeat destruct_update; simpl in *; eauto; erewrite doLeader_log; eauto; eauto.
-
unfold allEntries_log_prefix_within_term in *.
simpl in *.
intros.
repeat find_higher_order_rewrite.
repeat destruct_update; simpl in *; eauto; erewrite doLeader_log; eauto; eauto.
-
find_copy_apply_lem_hyp entries_sorted_invariant.
unfold entries_sorted in *.
unfold allEntries_append_entries_prefix_within_term_nw in *.
simpl in *.
intros.
repeat find_higher_order_rewrite.
repeat destruct_update; simpl in *; eauto.
+
find_apply_hyp_hyp.
intuition; [repeat find_reverse_rewrite; eauto|].
do_in_map.
subst.
simpl in *.
find_eapply_lem_hyp doLeader_spec; eauto.
intuition; subst.
*
left.
find_apply_lem_hyp findGtIndex_necessary.
intuition.
apply findGtIndex_sufficient; eauto using allEntries_gt_0_invariant.
unfold allEntries_log_prefix_within_term, prefix_within_term in *.
eauto.
*
{
break_exists.
break_and.
find_apply_lem_hyp findAtIndex_elim.
break_and.
subst.
find_apply_lem_hyp findGtIndex_necessary.
break_and.
eapply_prop_hyp allEntries_log_prefix_within_term allEntries; eauto; conclude_using eauto.
match goal with | _ : eIndex ?e <= eIndex ?e', _ : eIndex ?e' > eIndex ?x |- _ => destruct (lt_eq_lt_dec (eIndex e) (eIndex x)) end; intuition.
-
right.
right.
intuition.
repeat find_reverse_rewrite.
eapply sorted_term_index_lt; eauto.
repeat find_rewrite.
auto.
-
right.
left.
intuition.
repeat find_reverse_rewrite.
match goal with | |- eTerm ?e = eTerm ?x => cut (e = x); intros; subst; intuition end.
repeat find_rewrite.
eapply uniqueIndices_elim_eq; eauto using sorted_uniqueIndices.
-
left.
apply findGtIndex_sufficient; eauto.
}
*
break_exists.
intuition.
find_eapply_lem_hyp nextIndex_sanity; eauto.
break_exists.
unfold ghost_data in *.
simpl in *.
congruence.
+
find_apply_hyp_hyp.
intuition; [repeat find_reverse_rewrite; eauto|].
do_in_map.
subst.
simpl in *.
find_eapply_lem_hyp doLeader_spec; eauto.
intuition; subst.
*
left.
find_apply_lem_hyp findGtIndex_necessary.
intuition.
apply findGtIndex_sufficient; eauto using allEntries_gt_0_invariant.
unfold allEntries_log_prefix_within_term, prefix_within_term in *.
eauto.
*
{
break_exists.
break_and.
find_apply_lem_hyp findAtIndex_elim.
break_and.
subst.
find_apply_lem_hyp findGtIndex_necessary.
break_and.
eapply_prop_hyp allEntries_log_prefix_within_term allEntries; eauto; conclude_using eauto.
match goal with | _ : eIndex ?e <= eIndex ?e', _ : eIndex ?e' > eIndex ?x |- _ => destruct (lt_eq_lt_dec (eIndex e) (eIndex x)) end; intuition.
-
right.
right.
intuition.
repeat find_reverse_rewrite.
eapply sorted_term_index_lt; eauto.
repeat find_rewrite.
auto.
-
right.
left.
intuition.
repeat find_reverse_rewrite.
match goal with | |- eTerm ?e = eTerm ?x => cut (e = x); intros; subst; intuition end.
repeat find_rewrite.
eapply uniqueIndices_elim_eq; eauto using sorted_uniqueIndices.
-
left.
apply findGtIndex_sufficient; eauto.
}
*
break_exists.
intuition.
find_eapply_lem_hyp nextIndex_sanity; eauto.
break_exists.
unfold ghost_data in *.
simpl in *.
congruence.
-
unfold append_entries_leaderLogs_prefix_within_term in *.
intros.
simpl in *.
match goal with | H : In ?x (leaderLogs (fst (st' ?h))) |- _ => assert (In x (leaderLogs (fst (nwState net h)))) by (find_higher_order_rewrite; destruct_update; simpl in *; auto); clear H end.
find_apply_hyp_hyp.
intuition; eauto.
do_in_map.
subst.
simpl in *.
eapply prefix_within_term_subset; [eapply_prop log_leaderLogs_prefix_within_term|]; eauto using doLeader_in_entries_in_log.
-
unfold append_entries_log_prefix_within_term in *.
intros.
simpl in *.
match goal with | |- context [log (snd (st' ?h)) ] => assert (log (snd (st' h)) = log (snd (nwState net h))) by (find_higher_order_rewrite; destruct_update; simpl in *; auto; eapply doLeader_log; eauto) end.
repeat find_rewrite.
find_apply_hyp_hyp.
intuition; eauto.
do_in_map.
subst.
simpl in *.
Admitted.

Lemma update_elections_data_requestVoteReply_leaderLogs' : forall h h' t st t' ll' r, In (t', ll') (leaderLogs (update_elections_data_requestVoteReply h h' t r st)) -> In (t', ll') (leaderLogs (fst st)) \/ ll' = log (snd st).
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
repeat break_match; auto.
simpl in *.
intuition.
find_inversion.
right.
Admitted.

Lemma update_elections_data_requestVoteReply_allEntries : forall h h' t st r, allEntries (update_elections_data_requestVoteReply h h' t r st) = allEntries (fst st).
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
Admitted.

Lemma prefix_within_term_inductive_request_vote_reply : refined_raft_net_invariant_request_vote_reply prefix_within_term_inductive.
Proof using ollpti rlmli llli.
red.
unfold prefix_within_term_inductive.
intros.
find_eapply_lem_hyp handleRequestVoteReply_log.
intuition.
-
unfold allEntries_leaderLogs_prefix_within_term, allEntries_log_prefix_within_term in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; try rewrite update_elections_data_requestVoteReply_allEntries; eauto; find_apply_lem_hyp update_elections_data_requestVoteReply_leaderLogs'; intuition; subst; eauto.
-
unfold log_leaderLogs_prefix_within_term in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; repeat find_rewrite; eauto; find_apply_lem_hyp update_elections_data_requestVoteReply_leaderLogs'; intuition; subst; eauto; eapply log_log_prefix_within_term_invariant; eauto.
-
unfold allEntries_log_prefix_within_term in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; repeat find_rewrite; eauto; rewrite update_elections_data_requestVoteReply_allEntries; eauto.
-
unfold allEntries_append_entries_prefix_within_term_nw in *.
intros.
simpl in *.
find_apply_hyp_hyp.
match goal with | H : forall _, _ _ = update _ _ _ _ _ |- _ => rewrite H in * end.
destruct_update; simpl in *; eauto; try find_rewrite_lem update_elections_data_requestVoteReply_allEntries; eauto.
-
unfold append_entries_leaderLogs_prefix_within_term, append_entries_log_prefix_within_term in *.
intros.
simpl in *.
find_apply_hyp_hyp.
match goal with | H : forall _, _ _ = update _ _ _ _ _ |- _ => rewrite H in * end.
destruct_update; simpl in *; eauto; find_apply_lem_hyp update_elections_data_requestVoteReply_leaderLogs'; intuition; subst; eauto.
-
unfold append_entries_log_prefix_within_term in *.
intros.
simpl in *.
find_apply_hyp_hyp.
match goal with | H : forall _, _ _ = update _ _ _ _ _ |- _ => rewrite H in * end.
Admitted.

Lemma prefix_within_term_inductive_append_entries_reply : refined_raft_net_invariant_append_entries_reply prefix_within_term_inductive.
Proof using.
red.
unfold prefix_within_term_inductive.
intros.
subst.
find_copy_apply_lem_hyp handleAppendEntriesReply_log.
find_apply_lem_hyp handleAppendEntriesReply_packets.
subst.
simpl in *.
intuition.
-
unfold allEntries_leaderLogs_prefix_within_term in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
-
unfold log_leaderLogs_prefix_within_term in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; repeat find_rewrite; eauto.
-
unfold allEntries_log_prefix_within_term in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; repeat find_rewrite; eauto.
-
unfold allEntries_append_entries_prefix_within_term_nw in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition; match goal with | H : forall _, _ _ = update _ _ _ _ _ |- _ => rewrite H in * end; destruct_update; simpl in *; eauto.
-
unfold append_entries_leaderLogs_prefix_within_term in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition; match goal with | H : forall _, _ _ = update _ _ _ _ _ |- _ => rewrite H in * end; destruct_update; simpl in *; eauto.
-
unfold append_entries_log_prefix_within_term in *.
intros.
simpl in *.
find_apply_hyp_hyp.
Admitted.

Lemma update_elections_data_timeout_allEntries : forall h st, allEntries (update_elections_data_timeout h st) = allEntries (fst st).
Proof using.
intros.
unfold update_elections_data_timeout.
Admitted.

Lemma prefix_within_term_inductive_timeout : refined_raft_net_invariant_timeout prefix_within_term_inductive.
Proof using.
red.
unfold prefix_within_term_inductive.
intros.
subst.
find_copy_apply_lem_hyp handleTimeout_log_same.
intuition.
-
unfold allEntries_leaderLogs_prefix_within_term in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto; try find_rewrite_lem update_elections_data_timeout_leaderLogs; try rewrite update_elections_data_timeout_allEntries; eauto.
-
unfold log_leaderLogs_prefix_within_term in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; repeat find_rewrite; try find_rewrite_lem update_elections_data_timeout_leaderLogs; eauto.
-
unfold allEntries_log_prefix_within_term in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; repeat find_rewrite; try rewrite update_elections_data_timeout_allEntries; eauto.
-
unfold allEntries_append_entries_prefix_within_term_nw.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition; [|do_in_map; subst; simpl in *; find_eapply_lem_hyp handleTimeout_packets; eauto; find_rewrite; intuition; find_false; repeat eexists; eauto].
match goal with | H : forall _, _ _ = update _ _ _ _ _ |- _ => rewrite H in * end; destruct_update; simpl in *; try find_rewrite_lem update_elections_data_timeout_allEntries; eauto.
-
unfold append_entries_leaderLogs_prefix_within_term in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition; [|do_in_map; subst; simpl in *; find_eapply_lem_hyp handleTimeout_packets; eauto; find_rewrite; intuition; find_false; repeat eexists; eauto].
match goal with | H : forall _, _ _ = update _ _ _ _ _ |- _ => rewrite H in * end; destruct_update; simpl in *; try find_rewrite_lem update_elections_data_timeout_leaderLogs; eauto.
-
unfold append_entries_log_prefix_within_term in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition; [|do_in_map; subst; simpl in *; find_eapply_lem_hyp handleTimeout_packets; eauto; find_rewrite; intuition; find_false; repeat eexists; eauto].
Admitted.

Lemma prefix_within_term_inductive_request_vote : refined_raft_net_invariant_request_vote prefix_within_term_inductive.
Proof using.
red.
unfold prefix_within_term_inductive.
intros.
subst.
find_copy_apply_lem_hyp handleRequestVote_log.
intuition.
-
unfold allEntries_leaderLogs_prefix_within_term in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto; try find_rewrite_lem update_elections_data_requestVote_leaderLogs; try rewrite update_elections_data_requestVote_allEntries; eauto.
-
unfold log_leaderLogs_prefix_within_term in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; repeat find_rewrite; try find_rewrite_lem update_elections_data_requestVote_leaderLogs; eauto.
-
unfold allEntries_log_prefix_within_term in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; repeat find_rewrite; try rewrite update_elections_data_requestVote_allEntries; eauto.
-
unfold allEntries_append_entries_prefix_within_term_nw.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition; [|subst; simpl in *; find_eapply_lem_hyp handleRequestVote_no_append_entries; subst; intuition; find_false; repeat eexists; eauto].
match goal with | H : forall _, _ _ = update _ _ _ _ _ |- _ => rewrite H in * end; destruct_update; simpl in *; try find_rewrite_lem update_elections_data_requestVote_allEntries; eauto.
-
unfold append_entries_leaderLogs_prefix_within_term in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition; [|subst; simpl in *; find_eapply_lem_hyp handleRequestVote_no_append_entries; subst; intuition; find_false; repeat eexists; eauto].
match goal with | H : forall _, _ _ = update _ _ _ _ _ |- _ => rewrite H in * end; destruct_update; simpl in *; try find_rewrite_lem update_elections_data_requestVote_leaderLogs; eauto.
-
unfold append_entries_log_prefix_within_term in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition; [|subst; simpl in *; find_eapply_lem_hyp handleRequestVote_no_append_entries; subst; intuition; find_false; repeat eexists; eauto].
Admitted.

Lemma prefix_within_term_inductive_do_generic_server : refined_raft_net_invariant_do_generic_server prefix_within_term_inductive.
Proof using.
red.
unfold prefix_within_term_inductive.
intros.
subst.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
find_copy_apply_lem_hyp doGenericServer_log.
find_apply_lem_hyp doGenericServer_packets.
subst.
simpl in *.
intuition.
-
unfold allEntries_leaderLogs_prefix_within_term in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
-
unfold log_leaderLogs_prefix_within_term in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; repeat find_rewrite; eauto.
-
unfold allEntries_log_prefix_within_term in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; repeat find_rewrite; eauto.
-
unfold allEntries_append_entries_prefix_within_term_nw in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition; match goal with | H : forall _, _ _ = update _ _ _ _ _ |- _ => rewrite H in * end; destruct_update; simpl in *; eauto.
-
unfold append_entries_leaderLogs_prefix_within_term in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition; match goal with | H : forall _, _ _ = update _ _ _ _ _ |- _ => rewrite H in * end; destruct_update; simpl in *; eauto.
-
unfold append_entries_log_prefix_within_term in *.
intros.
simpl in *.
find_apply_hyp_hyp.
Admitted.

Lemma prefix_within_term_inductive_init : refined_raft_net_invariant_init prefix_within_term_inductive.
Proof using.
red.
unfold prefix_within_term_inductive in *.
intuition; red; intros; simpl in *; intuition.
unfold prefix_within_term.
intros.
simpl in *.
Admitted.

Lemma prefix_within_term_inductive_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset prefix_within_term_inductive.
Proof using.
red.
unfold prefix_within_term_inductive in *.
intros.
Admitted.

Lemma prefix_within_term_inductive_reboot : refined_raft_net_invariant_reboot prefix_within_term_inductive.
Proof using.
red.
intros.
subst.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
unfold reboot in *.
unfold prefix_within_term_inductive in *.
intros.
intros.
Admitted.

Theorem prefix_within_term_inductive_invariant : forall net, refined_raft_intermediate_reachable net -> prefix_within_term_inductive net.
Proof using aelsi aertsi aelmi nisi lsli llsli llsi ollpti rlmli llli rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply prefix_within_term_inductive_init.
-
apply prefix_within_term_inductive_client_request.
-
apply prefix_within_term_inductive_timeout.
-
apply prefix_within_term_inductive_append_entries.
-
apply prefix_within_term_inductive_append_entries_reply.
-
apply prefix_within_term_inductive_request_vote.
-
apply prefix_within_term_inductive_request_vote_reply.
-
apply prefix_within_term_inductive_do_leader.
-
apply prefix_within_term_inductive_do_generic_server.
-
apply prefix_within_term_inductive_state_same_packet_subset.
-
Admitted.

Instance pwti : prefix_within_term_interface.
split; intros.
-
apply prefix_within_term_inductive_invariant.
auto.
-
apply log_log_prefix_within_term_invariant.
Admitted.

Lemma update_elections_data_requestVote_allEntries : forall h h' t lli llt st, allEntries (update_elections_data_requestVote h h' t h' lli llt st) = allEntries (fst st).
Proof using.
unfold update_elections_data_requestVote.
intros.
repeat break_match; auto.
