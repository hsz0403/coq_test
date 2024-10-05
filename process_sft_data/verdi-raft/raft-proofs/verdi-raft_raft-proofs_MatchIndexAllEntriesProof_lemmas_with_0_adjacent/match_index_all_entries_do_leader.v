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
congruence.
