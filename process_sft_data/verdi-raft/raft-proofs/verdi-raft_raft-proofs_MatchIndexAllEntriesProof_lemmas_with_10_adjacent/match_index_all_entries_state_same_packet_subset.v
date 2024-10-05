Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.NoAppendEntriesToLeaderInterface.
Require Import VerdiRaft.NoAppendEntriesToSelfInterface.
Require Import VerdiRaft.TermsAndIndicesFromOneLogInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.LogAllEntriesInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.MatchIndexLeaderInterface.
Require Import VerdiRaft.MatchIndexSanityInterface.
Require Import VerdiRaft.AppendEntriesReplySublogInterface.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.MatchIndexAllEntriesInterface.
Section MatchIndexAllEntries.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {naetli : no_append_entries_to_leader_interface}.
Context {naetsi : no_append_entries_to_self_interface}.
Context {taifoli : terms_and_indices_from_one_log_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Context {laei : log_all_entries_interface}.
Context {aelli : append_entries_leaderLogs_interface}.
Context {lsi : leader_sublog_interface}.
Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {mili : match_index_leader_interface}.
Context {matchisi : match_index_sanity_interface}.
Context {aersi : append_entries_reply_sublog_interface}.
Context {cei : candidate_entries_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Definition match_index_all_entries_nw (net : network) : Prop := forall p t es e, In p (nwPackets net) -> pBody p = AppendEntriesReply t es true -> currentTerm (snd (nwState net (pDst p))) = t -> In e (log (snd (nwState net (pDst p)))) -> eTerm e = t -> eIndex e <= maxIndex es -> type (snd (nwState net (pDst p))) = Leader -> In (t, e) (allEntries (fst (nwState net (pSrc p)))).
Definition match_index_all_entries_inv (net : network) : Prop := match_index_all_entries net /\ match_index_all_entries_nw net.
Instance miaei : match_index_all_entries_interface.
Proof.
constructor.
apply match_index_all_entries_invariant.
End MatchIndexAllEntries.

Lemma update_nop_fst : forall A B f x (v2 : B) y, fst (update name_eq_dec f x (fst (f x), v2) y) = fst (A := A) (f y).
Proof using.
intros.
Admitted.

Lemma match_index_all_entries_append_entries_reply : refined_raft_net_invariant_append_entries_reply match_index_all_entries_inv.
Proof using.
unfold refined_raft_net_invariant_append_entries_reply, match_index_all_entries_inv.
simpl.
intros.
split.
-
{
unfold match_index_all_entries in *.
simpl.
intros.
break_and.
repeat find_higher_order_rewrite.
rewrite update_nop_fst.
update_destruct_simplify_hyp.
-
find_copy_apply_lem_hyp handleAppendEntriesReply_spec.
intuition.
+
match goal with | [ H : forall _ _ _, type _ = _ -> _ |- _ ] => specialize (H e (pDst p) h) end.
repeat find_rewrite.
repeat concludes.
find_erewrite_lem handleAppendEntriesReply_log.
auto.
+
congruence.
+
repeat find_rewrite.
match goal with | [ H : context [ assoc_default _ (assoc_set _ _ ?x _) ?y _ ] |- _ ] => destruct (name_eq_dec x y) end.
*
subst.
rewrite get_set_same_default in *.
find_apply_lem_hyp app_cons_in.
find_erewrite_lem handleAppendEntriesReply_log.
{
find_apply_lem_hyp PeanoNat.Nat.max_le.
break_or_hyp.
-
match goal with | [ H : forall _ _ _, type _ = _ -> _ |- _ ] => specialize (H e (pDst p) (pSrc p)) end.
repeat find_rewrite.
auto.
-
unfold match_index_all_entries_nw in *.
match goal with | [ H : pBody _ = _, H' : _ |- _ ] => eapply H' with (e := e) in H; auto end.
}
*
rewrite get_set_diff_default in * by auto.
match goal with | [ H : forall _ _ _, type _ = _ -> _ |- _ ] => specialize (H e (pDst p) h) end.
repeat find_rewrite.
repeat concludes.
find_erewrite_lem handleAppendEntriesReply_log.
auto.
-
find_apply_hyp_hyp.
congruence.
}
-
break_and.
unfold match_index_all_entries_nw in *.
simpl.
intros.
repeat find_higher_order_rewrite.
rewrite update_nop_fst.
find_apply_hyp_hyp.
break_or_hyp.
+
update_destruct_simplify_hyp.
*
find_erewrite_lem handleAppendEntriesReply_log.
find_copy_apply_lem_hyp handleAppendEntriesReply_spec.
{
repeat break_or_hyp; break_and.
-
repeat find_rewrite.
eauto using in_middle_insert.
-
congruence.
-
repeat find_rewrite.
eauto using in_middle_insert.
}
*
eauto using in_middle_insert.
+
do_in_map.
find_apply_lem_hyp handleAppendEntriesReply_packets.
subst.
simpl in *.
Admitted.

Lemma handleRequestVote_sends_RVR : forall st h h' t lli llt st' m, handleRequestVote h st t h' lli llt = (st', m) -> exists t b, m = RequestVoteReply t b.
Proof using.
unfold handleRequestVote.
intros.
Admitted.

Lemma match_index_all_entries_request_vote : refined_raft_net_invariant_request_vote match_index_all_entries_inv.
Proof using.
unfold refined_raft_net_invariant_request_vote, match_index_all_entries_inv.
simpl.
intros.
split.
-
unfold match_index_all_entries in *.
simpl.
intros.
break_and.
repeat find_higher_order_rewrite.
update_destruct_simplify_hyp.
+
find_copy_apply_lem_hyp handleRequestVote_type.
intuition; try congruence.
find_copy_apply_lem_hyp handleRequestVote_matchIndex_preserved.
unfold matchIndex_preserved in *.
intuition.
update_destruct_simplify_hyp.
*
rewrite update_elections_data_requestVote_allEntries.
repeat find_reverse_rewrite.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => apply H with (leader := pDst p) end; auto; repeat find_rewrite; auto.
*
repeat find_reverse_rewrite.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => apply H with (leader := pDst p) end; auto; repeat find_rewrite; auto.
+
update_destruct_simplify_hyp.
*
rewrite update_elections_data_requestVote_allEntries.
repeat find_reverse_rewrite.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto end.
*
repeat find_reverse_rewrite.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto end.
-
break_and.
unfold match_index_all_entries_nw in *.
simpl.
intros.
find_apply_hyp_hyp.
break_or_hyp.
+
repeat find_higher_order_rewrite.
update_destruct_simplify_hyp.
*
{
find_copy_apply_lem_hyp handleRequestVote_type.
intuition; try congruence.
find_copy_apply_lem_hyp handleRequestVote_matchIndex_preserved.
unfold matchIndex_preserved in *.
intuition.
update_destruct_simplify_hyp.
-
rewrite update_elections_data_requestVote_allEntries.
repeat find_rewrite.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => apply H with (es := es); auto using in_middle_insert; try congruence end.
-
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => apply H with (es := es); auto using in_middle_insert; try congruence end.
}
*
{
update_destruct_simplify_hyp.
-
rewrite update_elections_data_requestVote_allEntries.
repeat find_rewrite.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => apply H with (es := es); auto using in_middle_insert; try congruence end.
-
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => apply H with (es := es); auto using in_middle_insert; try congruence end.
}
+
simpl in *.
find_apply_lem_hyp handleRequestVote_sends_RVR.
break_exists.
Admitted.

Lemma handleRequestVoteReply_spec : forall h st h' t r st', handleRequestVoteReply h st h' t r = st' -> type st' = Follower \/ st' = st \/ (log st' = log st /\ currentTerm st' = currentTerm st /\ matchIndex st' = assoc_set name_eq_dec nil h (maxIndex (log st))).
Proof using.
unfold handleRequestVoteReply.
intros.
Admitted.

Lemma handleRequestVoteReply_spec' : forall h st h' t r st', handleRequestVoteReply h st h' t r = st' -> type st' = Follower \/ st' = st \/ type st' = Candidate \/ (type st' = Leader /\ type st = Candidate /\ log st' = log st /\ r = true /\ t = currentTerm st /\ wonElection (dedup name_eq_dec (h' :: votesReceived st)) = true /\ currentTerm st' = currentTerm st).
Proof using.
unfold handleRequestVoteReply.
intros.
Admitted.

Lemma match_index_all_entries_request_vote_reply : refined_raft_net_invariant_request_vote_reply match_index_all_entries_inv.
Proof using cci vci cei laei taifoli rri.
unfold refined_raft_net_invariant_request_vote_reply, match_index_all_entries_inv.
simpl.
intros.
split.
-
unfold match_index_all_entries in *.
simpl.
intros.
break_and.
find_apply_lem_hyp handleRequestVoteReply_spec.
repeat find_higher_order_rewrite.
update_destruct_simplify_hyp.
+
intuition; try congruence.
*
subst.
{
update_destruct_simplify_hyp.
-
rewrite update_elections_data_requestVoteReply_allEntries.
repeat find_reverse_rewrite.
eauto.
-
repeat find_reverse_rewrite.
eauto.
}
*
repeat find_rewrite.
unfold assoc_default in *.
{
break_match.
-
simpl in *.
break_if; try discriminate.
match goal with | [ H : Some _ = Some _ |- _ ] => invc H end.
rewrite_update.
simpl.
rewrite update_elections_data_requestVoteReply_allEntries.
match goal with | [ |- In (?t, _) _ ] => replace t with (eTerm e) by congruence end.
eapply log_all_entries_invariant; auto.
-
find_apply_lem_hyp lifted_terms_and_indices_from_one_log; auto.
intuition.
omega.
}
+
update_destruct_simplify_hyp.
*
rewrite update_elections_data_requestVoteReply_allEntries.
repeat find_reverse_rewrite.
eauto.
*
repeat find_reverse_rewrite.
eauto.
-
unfold match_index_all_entries_nw in *.
simpl in *.
intros.
find_apply_lem_hyp handleRequestVoteReply_spec'.
repeat find_higher_order_rewrite.
find_apply_hyp_hyp.
update_destruct_simplify_hyp.
+
intuition; try congruence.
*
subst.
{
update_destruct_simplify_hyp.
-
rewrite update_elections_data_requestVoteReply_allEntries.
repeat find_rewrite.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto; congruence end.
-
repeat find_rewrite.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto; congruence end.
}
*
subst.
intro_refined_invariant candidate_entries_invariant.
match goal with | [ H : candidateEntries_host_invariant _ |- _ ] => pose proof H (pDst p) e end.
unfold raft_data in *.
conclude_using congruence.
{
find_eapply_lem_hyp wonElection_candidateEntries_rvr; eauto.
-
intuition.
-
eauto using votes_correct_invariant.
-
eauto using cronies_correct_invariant.
-
unfold raft_refined_base_params, raft_refined_multi_params in *.
congruence.
-
unfold raft_refined_multi_params, raft_refined_base_params in *.
simpl in *.
unfold raft_data in *.
congruence.
}
+
{
update_destruct_simplify_hyp.
-
rewrite update_elections_data_requestVoteReply_allEntries.
repeat find_rewrite.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto; congruence end.
-
repeat find_rewrite.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto; congruence end.
Admitted.

Lemma doLeader_sends_AE : forall st h os st' ms m, doLeader st h = (os, st', ms) -> In m ms -> is_append_entries (snd m).
Proof using.
unfold doLeader.
intros.
repeat break_match; repeat find_inversion; simpl in *; intuition.
do_in_map.
subst.
unfold replicaMessage.
Admitted.

Lemma match_index_all_entries_do_leader : refined_raft_net_invariant_do_leader match_index_all_entries_inv.
Proof using.
unfold refined_raft_net_invariant_do_leader, match_index_all_entries_inv.
intros.
break_and.
split.
-
unfold match_index_all_entries in *.
simpl in *.
intros.
repeat find_higher_order_rewrite.
match goal with | [ H : nwState ?net ?h = (?x, ?y) |- _ ] => replace x with (fst (nwState net h)) in * by (rewrite H; auto); replace y with (snd (nwState net h)) in * by (rewrite H; auto); clear H end.
rewrite update_nop_fst.
update_destruct_simplify_hyp.
+
repeat find_reverse_rewrite.
find_copy_apply_lem_hyp doLeader_type.
intuition.
find_copy_apply_lem_hyp doLeader_matchIndex_preserved.
unfold matchIndex_preserved in *.
intuition.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto; try congruence end.
+
repeat find_reverse_rewrite.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto; try congruence end.
-
unfold match_index_all_entries_nw in *.
simpl in *.
intros.
find_apply_hyp_hyp.
break_or_hyp.
+
repeat find_higher_order_rewrite.
match goal with | [ H : nwState ?net ?h = (?x, ?y) |- _ ] => replace x with (fst (nwState net h)) in * by (rewrite H; auto); replace y with (snd (nwState net h)) in * by (rewrite H; auto); clear H end.
rewrite update_nop_fst in *.
find_copy_apply_lem_hyp doLeader_type.
intuition.
update_destruct_simplify_hyp.
*
find_copy_apply_lem_hyp doLeader_matchIndex_preserved.
unfold matchIndex_preserved in *.
intuition.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto; try congruence end.
*
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto; try congruence end.
+
do_in_map.
find_eapply_lem_hyp doLeader_sends_AE; [|eauto].
break_exists.
subst.
simpl in *.
Admitted.

Lemma match_index_all_entries_do_generic_server : refined_raft_net_invariant_do_generic_server match_index_all_entries_inv.
Proof using.
unfold refined_raft_net_invariant_do_generic_server, match_index_all_entries_inv.
simpl.
intros.
break_and.
split.
-
unfold match_index_all_entries in *.
simpl in *.
intros.
repeat find_higher_order_rewrite.
match goal with | [ H : nwState ?net ?h = (?x, ?y) |- _ ] => replace x with (fst (nwState net h)) in * by (rewrite H; auto); replace y with (snd (nwState net h)) in * by (rewrite H; auto); clear H end.
rewrite update_nop_fst.
update_destruct_simplify_hyp.
+
repeat find_reverse_rewrite.
find_copy_apply_lem_hyp doGenericServer_type.
intuition.
find_copy_apply_lem_hyp doGenericServer_matchIndex_preserved.
unfold matchIndex_preserved in *.
intuition.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto; try congruence end.
+
repeat find_reverse_rewrite.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto; try congruence end.
-
unfold match_index_all_entries_nw in *.
simpl in *.
intros.
find_apply_hyp_hyp.
break_or_hyp.
+
repeat find_higher_order_rewrite.
match goal with | [ H : nwState ?net ?h = (?x, ?y) |- _ ] => replace x with (fst (nwState net h)) in * by (rewrite H; auto); replace y with (snd (nwState net h)) in * by (rewrite H; auto); clear H end.
rewrite update_nop_fst in *.
find_copy_apply_lem_hyp doGenericServer_type.
intuition.
update_destruct_simplify_hyp.
*
find_copy_apply_lem_hyp doGenericServer_matchIndex_preserved.
unfold matchIndex_preserved in *.
intuition.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto; try congruence end.
*
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto; try congruence end.
+
do_in_map.
find_apply_lem_hyp doGenericServer_packets.
subst.
simpl in *.
Admitted.

Lemma match_index_all_entries_reboot : refined_raft_net_invariant_reboot match_index_all_entries_inv.
Proof using.
unfold refined_raft_net_invariant_reboot, match_index_all_entries_inv.
intros.
break_and.
subst.
split.
-
unfold match_index_all_entries in *.
intros.
repeat find_higher_order_rewrite.
match goal with | [ H : nwState ?net ?h = (?x, ?y) |- _ ] => replace x with (fst (nwState net h)) in * by (rewrite H; auto); replace y with (snd (nwState net h)) in * by (rewrite H; auto); clear H end.
rewrite update_nop_fst.
update_destruct_simplify_hyp.
+
discriminate.
+
repeat find_reverse_rewrite.
eauto.
-
unfold match_index_all_entries_nw in *.
intros.
repeat find_higher_order_rewrite.
match goal with | [ H : nwState ?net ?h = (?x, ?y) |- _ ] => replace x with (fst (nwState net h)) in * by (rewrite H; auto); replace y with (snd (nwState net h)) in * by (rewrite H; auto); clear H end.
rewrite update_nop_fst.
update_destruct_simplify_hyp.
+
discriminate.
+
repeat find_reverse_rewrite.
Admitted.

Lemma match_index_all_entries_invariant : forall net, refined_raft_intermediate_reachable net -> match_index_all_entries_inv net.
Proof using cci vci cei aersi matchisi mili ollpti lhllsi lsi aelli laei rlmli taifoli naetsi naetli rri.
intros.
apply refined_raft_net_invariant'; auto.
-
apply match_index_all_entries_init.
-
apply refined_raft_net_invariant_client_request'_weak.
apply match_index_all_entries_client_request.
-
apply refined_raft_net_invariant_timeout'_weak.
apply match_index_all_entries_timeout.
-
apply match_index_all_entries_append_entries.
-
apply refined_raft_net_invariant_append_entries_reply'_weak.
apply match_index_all_entries_append_entries_reply.
-
apply refined_raft_net_invariant_request_vote'_weak.
apply match_index_all_entries_request_vote.
-
apply refined_raft_net_invariant_request_vote_reply'_weak.
apply match_index_all_entries_request_vote_reply.
-
apply refined_raft_net_invariant_do_leader'_weak.
apply match_index_all_entries_do_leader.
-
apply refined_raft_net_invariant_do_generic_server'_weak.
apply match_index_all_entries_do_generic_server.
-
apply match_index_all_entries_state_same_packet_subset.
-
apply refined_raft_net_invariant_reboot'_weak.
Admitted.

Instance miaei : match_index_all_entries_interface.
Proof.
constructor.
Admitted.

Lemma match_index_all_entries_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset match_index_all_entries_inv.
Proof using.
unfold refined_raft_net_invariant_state_same_packet_subset, match_index_all_entries_inv.
simpl.
intros.
break_and.
split.
-
unfold match_index_all_entries in *.
intros.
repeat find_reverse_higher_order_rewrite.
eauto.
-
unfold match_index_all_entries_nw in *.
intros.
find_apply_hyp_hyp.
repeat find_reverse_higher_order_rewrite.
eauto.
