Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.CommitRecordedCommittedInterface.
Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.StateMachineSafetyPrimeInterface.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.MaxIndexSanityInterface.
Require Import VerdiRaft.LeaderCompletenessInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.PrevLogLeaderSublogInterface.
Require Import VerdiRaft.CurrentTermGtZeroInterface.
Require Import VerdiRaft.LastAppliedLeCommitIndexInterface.
Require Import VerdiRaft.MatchIndexAllEntriesInterface.
Require Import VerdiRaft.LeadersHaveLeaderLogsInterface.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.TermsAndIndicesFromOneLogInterface.
Require Import VerdiRaft.GhostLogCorrectInterface.
Require Import VerdiRaft.GhostLogsLogPropertiesInterface.
Require Import VerdiRaft.GhostLogLogMatchingInterface.
Require Import VerdiRaft.TransitiveCommitInterface.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.RaftMsgRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Section StateMachineSafetyProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {si : sorted_interface}.
Context {lmi : log_matching_interface}.
Context {smspi : state_machine_safety'interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Context {pllsi : prevLog_leader_sublog_interface}.
Context {ctgt0 : current_term_gt_zero_interface}.
Context {lalcii : lastApplied_le_commitIndex_interface}.
Context {miaei : match_index_all_entries_interface}.
Context {lhlli : leaders_have_leaderLogs_interface}.
Context {lci : leader_completeness_interface}.
Context {lsi : leader_sublog_interface}.
Context {taifoli : terms_and_indices_from_one_log_interface}.
Context {glci : ghost_log_correct_interface}.
Context {lphogli : log_properties_hold_on_ghost_logs_interface}.
Context {glemi : ghost_log_entries_match_interface}.
Context {tci : transitive_commit_interface}.
Context {tsi : term_sanity_interface}.
Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {rmri : raft_msg_refinement_interface}.
Definition ghost_log_network : Type := @network _ raft_msg_refined_multi_params.
Definition ghost_log_packet : Type := @packet _ raft_msg_refined_multi_params.
Definition lifted_maxIndex_sanity (net : ghost_log_network) : Prop := (forall h, lastApplied (snd (nwState net h)) <= maxIndex (log (snd (nwState net h)))) /\ (forall h, commitIndex (snd (nwState net h)) <= maxIndex (log (snd (nwState net h)))).
Definition lifted_no_entries_past_current_term_host net := forall (h : name) e, In e (log (snd (nwState net h))) -> eTerm e <= currentTerm (snd (nwState net h)).
Definition lifted_entries_contiguous (net : ghost_log_network) : Prop := forall h, contiguous_range_exact_lo (log (snd (nwState net h))) 0.
Definition lifted_entries_contiguous_nw (net : ghost_log_network) : Prop := forall p t n pli plt es ci, In p (nwPackets net) -> snd (pBody p) = AppendEntries t n pli plt es ci -> contiguous_range_exact_lo es pli.
Definition lifted_entries_gt_0 (net : ghost_log_network) : Prop := forall h e, In e (log (snd (nwState net h))) -> eIndex e > 0.
Definition lifted_directly_committed (net : ghost_log_network) (e : entry) : Prop := exists quorum, NoDup quorum /\ length quorum > div2 (length nodes) /\ (forall h, In h quorum -> In (eTerm e, e) (allEntries (fst (nwState net h)))).
Definition lifted_committed (net : ghost_log_network) (e : entry) (t : term) : Prop := exists h e', eTerm e' <= t /\ lifted_directly_committed net e' /\ eIndex e <= eIndex e' /\ In e (log (snd (nwState net h))) /\ In e' (log (snd (nwState net h))).
Definition commit_invariant_host (net : ghost_log_network) : Prop := forall h e, In e (log (snd (nwState net h))) -> eIndex e <= commitIndex (snd (nwState net h)) -> lifted_committed net e (currentTerm (snd (nwState net h))).
Definition commit_invariant_nw (net : ghost_log_network) : Prop := forall p t lid pli plt es lci e, In p (nwPackets net) -> snd (pBody p) = AppendEntries t lid pli plt es lci -> In e (fst (pBody p)) -> eIndex e <= lci -> lifted_committed net e t.
Definition commit_invariant (net : ghost_log_network) : Prop := commit_invariant_host net /\ commit_invariant_nw net.
Definition lifted_prevLog_leader_sublog (net : network) : Prop := forall leader p t leaderId prevLogIndex prevLogTerm entries leaderCommit, type (snd (nwState net leader)) = Leader -> In p (nwPackets net) -> snd (pBody p) = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit -> currentTerm (snd (nwState net leader)) = prevLogTerm -> 0 < prevLogIndex -> 0 < prevLogTerm -> exists ple, eIndex ple = prevLogIndex /\ eTerm ple = prevLogTerm /\ In ple (log (snd (nwState net leader))).
Definition lifted_state_machine_safety_nw' net := forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit e t', In p (nwPackets net) -> snd (pBody p) = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit -> lifted_committed net e t' -> t >= t' -> (prevLogIndex > eIndex e \/ (prevLogIndex = eIndex e /\ prevLogTerm = eTerm e) \/ eIndex e > maxIndex entries \/ In e entries).
Definition lifted_entries_gt_0_nw (net : ghost_log_network) : Prop := forall p t n pli plt es ci e, In p (nwPackets net) -> snd (pBody p) = AppendEntries t n pli plt es ci -> In e es -> eIndex e > 0.
Definition lifted_entries_sorted_nw' (net : ghost_log_network) := forall p t n pli plt es ci, In p (nwPackets net) -> snd (pBody p) = AppendEntries t n pli plt es ci -> sorted es.
Definition lifted_leaders_have_leaderLogs_strong (net : ghost_log_network) := forall h, type (snd (nwState net h)) = Leader -> exists ll es, In (currentTerm (snd (nwState net h)), ll) (leaderLogs (fst (nwState net h))) /\ log (snd (nwState net h)) = es ++ ll /\ (forall e : entry, In e es -> eTerm e = currentTerm (snd (nwState net h))).
Definition lifted_one_leaderLog_per_term (net : ghost_log_network) : Prop := forall h h' t ll ll', In (t, ll) (leaderLogs (fst (nwState net h))) -> In (t, ll') (leaderLogs (fst (nwState net h'))) -> h = h' /\ ll = ll'.
Definition lifted_leaders_have_leaderLogs (net : ghost_log_network) : Prop := forall h, type (snd (nwState net h)) = Leader -> exists ll, In (currentTerm (snd (nwState net h)), ll) (leaderLogs (fst (nwState net h))).
Definition lifted_leader_completeness_directly_committed (net : ghost_log_network) : Prop := forall t e log h, lifted_directly_committed net e -> t > eTerm e -> In (t, log) (leaderLogs (fst (nwState net h))) -> In e log.
Definition lifted_leader_completeness_committed (net : ghost_log_network) : Prop := forall t t' e log h, lifted_committed net e t -> t' > t -> In (t', log) (leaderLogs (fst (nwState net h))) -> In e log.
Definition lifted_leader_completeness (net : ghost_log_network) : Prop := lifted_leader_completeness_directly_committed net /\ lifted_leader_completeness_committed net.
Definition msg_lifted_leader_sublog_host (net : ghost_log_network) : Prop := forall leader e h, type (snd (nwState net leader)) = Leader -> In e (log (snd (nwState net h))) -> eTerm e = currentTerm (snd (nwState net leader)) -> In e (log (snd (nwState net leader))).
Definition everything (net : ghost_log_network) : Prop := lifted_maxIndex_sanity net /\ commit_invariant net /\ state_machine_safety (deghost (mgv_deghost net)).
Instance smsi : state_machine_safety_interface.
Proof.
split.
exact state_machine_safety_invariant.
Instance misi : max_index_sanity_interface.
Proof.
split.
exact maxIndex_sanity_invariant.
Instance crci : commit_recorded_committed_interface.
Proof.
split.
intros.
find_apply_lem_hyp commit_recorded_committed_invariant.
unfold commit_invariant, commit_recorded_committed, commit_recorded in *.
intros.
find_rewrite_lem (deghost_spec net h).
intuition; repeat match goal with | [ H : forall _, _, h : entry |- _ ] => specialize (H h) | [ H : forall _, _, h : Net.name |- _ ] => specialize (H h) end; repeat find_rewrite_lem deghost_spec; auto.
End StateMachineSafetyProof.

Lemma commit_recorded_lift_intro : forall (net : network (params := raft_refined_multi_params)) h e, In e (log (snd (nwState net h))) -> (eIndex e <= lastApplied (snd (nwState net h)) \/ eIndex e <= commitIndex (snd (nwState net h))) -> commit_recorded (deghost net) h e.
Proof using rri.
unfold commit_recorded.
intros.
rewrite deghost_spec.
Admitted.

Lemma msg_commit_recorded_lift_intro : forall (net : ghost_log_network) h e, In e (log (snd (nwState net h))) -> (eIndex e <= lastApplied (snd (nwState net h)) \/ eIndex e <= commitIndex (snd (nwState net h))) -> commit_recorded (deghost (mgv_deghost net)) h e.
Proof using rmri rri.
unfold commit_recorded.
intros.
rewrite deghost_spec.
rewrite msg_deghost_spec with (net0 := net).
Admitted.

Lemma lifted_entries_contiguous_invariant : forall net, msg_refined_raft_intermediate_reachable net -> lifted_entries_contiguous net.
Proof using rmri rlmli.
unfold lifted_entries_contiguous.
intros.
pose proof (msg_lift_prop _ entries_contiguous_invariant _ ltac:(eauto) h).
find_rewrite_lem msg_deghost_spec.
Admitted.

Lemma lifted_entries_contiguous_nw_invariant : forall net, msg_refined_raft_intermediate_reachable net -> lifted_entries_contiguous_nw net.
Proof using rmri rlmli.
unfold lifted_entries_contiguous_nw.
intros.
pose proof msg_lift_prop _ entries_contiguous_nw_invariant _ ltac:(eauto) (mgv_deghost_packet p).
match goal with | [ H : context [In] |- _ ] => eapply H end.
-
auto using in_mgv_ghost_packet.
-
rewrite pBody_mgv_deghost_packet.
Admitted.

Lemma lifted_entries_gt_0_invariant : forall net, msg_refined_raft_intermediate_reachable net -> lifted_entries_gt_0 net.
Proof using rmri rlmli.
unfold lifted_entries_gt_0.
intros.
pose proof msg_lift_prop _ entries_gt_0_invariant _ ltac:(eauto).
unfold entries_gt_0 in *.
match goal with | [ H : _ |- _ ] => eapply H; eauto end.
rewrite msg_deghost_spec.
Admitted.

Lemma lifted_maxIndex_sanity_append_entries : forall xs (p : ghost_log_packet) ys (net : ghost_log_network) st' ps' gd d m t n pli plt es ci, handleAppendEntries (pDst p) (snd (nwState net (pDst p))) t n pli plt es ci = (d, m) -> gd = update_elections_data_appendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci -> snd (pBody p) = AppendEntries t n pli plt es ci -> lifted_maxIndex_sanity net -> state_machine_safety (deghost (mgv_deghost net)) -> msg_refined_raft_intermediate_reachable net -> nwPackets net = xs ++ p :: ys -> (forall h, st' h = update name_eq_dec (nwState net) (pDst p) (gd, d) h) -> (forall (p' : ghost_log_packet), In p' ps' -> In p' (xs ++ ys) \/ mgv_deghost_packet p' = mkPacket (params := raft_refined_multi_params) (pDst p) (pSrc p) m) -> lifted_maxIndex_sanity (mkNetwork ps' st').
Proof using rmri rlmli si rri.
unfold lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
intros.
intuition; simpl in *; repeat find_higher_order_rewrite; update_destruct_simplify; auto.
-
erewrite handleAppendEntries_lastApplied by eauto.
assert (sorted (log d)) by (eauto using lifted_handleAppendEntries_logs_sorted).
match goal with | _ : handleAppendEntries ?h ?s ?t ?n ?pli ?plt ?es ?ci = (?s', ?m) |- _ => pose proof handleAppendEntries_log_detailed h s t n pli plt es ci s' m end.
intuition; repeat find_rewrite.
+
eauto.
+
subst.
destruct (le_lt_dec (lastApplied (snd (nwState net (pDst p)))) (maxIndex (log d))); auto.
exfalso.
assert (In p (nwPackets net)) by (find_rewrite; intuition).
assert (exists x, eIndex x = maxIndex (log d) /\ In x (log (snd (nwState net (pDst p))))).
{
eapply contiguous_range_exact_lo_elim_exists.
-
eapply lifted_entries_contiguous_invariant.
auto.
-
split.
+
find_apply_lem_hyp maxIndex_non_empty.
break_exists.
break_and.
repeat find_rewrite.
eapply contiguous_range_exact_lo_elim_lt.
*
eapply lifted_entries_contiguous_nw_invariant; eauto.
*
auto.
+
eapply le_trans; [|eauto].
simpl in *.
omega.
}
break_exists.
break_and.
eapply findAtIndex_None; [|eauto| |]; eauto.
apply msg_lifted_sorted_host; auto.
+
subst.
destruct (le_lt_dec (lastApplied (snd (nwState net (pDst p)))) (maxIndex (log d))); auto.
exfalso.
assert (In p (nwPackets net)) by (find_rewrite; intuition).
break_exists; intuition.
find_apply_lem_hyp findAtIndex_elim; intuition.
find_eapply_lem_hyp msg_lifted_sms_nw; eauto; [|eapply msg_commit_recorded_lift_intro; eauto; left; repeat find_rewrite; auto using lt_le_weak].
intuition.
*
subst.
assert (0 < eIndex x) by (eapply lifted_entries_contiguous_invariant; eauto).
omega.
*
destruct (log d); intuition.
simpl in *.
intuition; subst; auto.
find_apply_hyp_hyp.
omega.
+
destruct (le_lt_dec (lastApplied (snd (nwState net (pDst p)))) pli); intuition; [eapply le_trans; [| apply sorted_maxIndex_app]; auto; break_exists; break_and; erewrite maxIndex_removeAfterIndex by (eauto; apply msg_lifted_sorted_host; auto); auto|]; [idtac].
destruct (le_lt_dec (lastApplied (snd (nwState net (pDst p)))) (maxIndex es)); intuition; [match goal with | |- context [ maxIndex (?ll1 ++ ?ll2) ] => pose proof maxIndex_app ll1 ll2 end; simpl in *; intuition|]; [idtac].
assert (exists x, eIndex x = maxIndex es /\ In x (log (snd (nwState net (pDst p))))).
{
eapply contiguous_range_exact_lo_elim_exists.
-
eapply lifted_entries_contiguous_invariant.
auto.
-
split.
+
find_apply_lem_hyp maxIndex_non_empty.
break_exists.
break_and.
repeat find_rewrite.
destruct es.
*
simpl in *.
intuition.
*
simpl.
subst.
{
eapply le_lt_trans with (m := eIndex x).
-
omega.
-
eapply contiguous_range_exact_lo_elim_lt.
+
eapply lifted_entries_contiguous_nw_invariant; eauto.
+
intuition.
}
+
eapply le_trans; [|eauto].
simpl in *.
omega.
}
break_exists.
intuition.
match goal with | H : findAtIndex _ _ = None |- _ => eapply findAtIndex_None with (x1 := x) in H end; eauto.
*
congruence.
*
apply msg_lifted_sorted_host.
auto.
+
destruct (le_lt_dec (lastApplied (snd (nwState net (pDst p)))) (maxIndex es)); intuition; [match goal with | |- context [ maxIndex (?ll1 ++ ?ll2) ] => pose proof maxIndex_app ll1 ll2 end; simpl in *; intuition|]; [idtac].
exfalso.
assert (In p (nwPackets net)) by (find_rewrite; intuition).
break_exists; intuition.
find_apply_lem_hyp findAtIndex_elim; intuition.
find_copy_apply_lem_hyp maxIndex_non_empty.
break_exists.
intuition.
find_eapply_lem_hyp msg_lifted_sms_nw; eauto; [|eapply msg_commit_recorded_lift_intro; eauto; left; repeat find_rewrite; auto using lt_le_weak].
match goal with | _ : In ?x es, _ : maxIndex es = eIndex ?x |- _ => assert (pli < eIndex x) by ( eapply contiguous_range_exact_lo_elim_lt; eauto; eapply lifted_entries_contiguous_nw_invariant; eauto) end.
intuition.
match goal with | H : _ = _ ++ _ |- _ => symmetry in H end.
destruct es; intuition; simpl in *; intuition; subst_max; intuition; repeat clean; match goal with | _ : eIndex ?x' = eIndex ?x, H : context [eIndex ?x'] |- _ => specialize (H x); conclude H ltac:(apply in_app_iff; auto) end; intuition.
-
assert (sorted (log d)) by (eauto using lifted_handleAppendEntries_logs_sorted).
match goal with | _ : handleAppendEntries ?h ?s ?t ?n ?pli ?plt ?es ?ci = (?s', ?m) |- _ => pose proof handleAppendEntries_log_detailed h s t n pli plt es ci s' m end.
intuition; repeat find_rewrite; try apply max_min_thing; match goal with | H : context [ lastApplied _ ] |- _ => clear H end.
+
eauto.
+
subst.
destruct (le_lt_dec (commitIndex (snd (nwState net (pDst p)))) (maxIndex (log d))); auto.
exfalso.
assert (In p (nwPackets net)) by (find_rewrite; intuition).
assert (exists x, eIndex x = maxIndex (log d) /\ In x (log (snd (nwState net (pDst p))))).
{
eapply contiguous_range_exact_lo_elim_exists.
-
eapply lifted_entries_contiguous_invariant.
auto.
-
split.
+
find_apply_lem_hyp maxIndex_non_empty.
break_exists.
break_and.
repeat find_rewrite.
eapply contiguous_range_exact_lo_elim_lt.
*
eapply lifted_entries_contiguous_nw_invariant; eauto.
*
auto.
+
eapply le_trans; [|eauto].
simpl in *.
omega.
}
break_exists.
intuition.
find_eapply_lem_hyp findAtIndex_None; eauto.
apply msg_lifted_sorted_host.
auto.
+
subst.
destruct (le_lt_dec (commitIndex (snd (nwState net (pDst p)))) (maxIndex (log d))); auto.
exfalso.
assert (In p (nwPackets net)) by (find_rewrite; intuition).
break_exists; intuition.
find_apply_lem_hyp findAtIndex_elim; intuition.
find_eapply_lem_hyp msg_lifted_sms_nw; eauto; [|eapply msg_commit_recorded_lift_intro; eauto; right; repeat find_rewrite; intuition].
intuition.
*
subst.
assert (0 < eIndex x) by (eapply lifted_entries_contiguous_invariant; eauto).
omega.
*
destruct (log d); intuition.
simpl in *.
intuition; subst; auto.
find_apply_hyp_hyp.
omega.
+
destruct (le_lt_dec (commitIndex (snd (nwState net (pDst p)))) pli); intuition; [eapply le_trans; [| apply sorted_maxIndex_app]; auto; break_exists; intuition; erewrite maxIndex_removeAfterIndex; eauto; apply msg_lifted_sorted_host; auto|]; [idtac].
destruct (le_lt_dec (commitIndex (snd (nwState net (pDst p)))) (maxIndex es)); intuition; [match goal with | |- context [ maxIndex (?ll1 ++ ?ll2) ] => pose proof maxIndex_app ll1 ll2 end; simpl in *; intuition|]; [idtac].
assert (exists x, eIndex x = maxIndex es /\ In x (log (snd (nwState net (pDst p))))).
{
eapply contiguous_range_exact_lo_elim_exists.
-
eapply lifted_entries_contiguous_invariant.
auto.
-
split.
+
find_apply_lem_hyp maxIndex_non_empty.
break_exists.
break_and.
repeat find_rewrite.
destruct es.
*
simpl in *.
intuition.
*
simpl.
subst.
{
eapply le_lt_trans with (m := eIndex x).
-
omega.
-
eapply contiguous_range_exact_lo_elim_lt.
+
eapply lifted_entries_contiguous_nw_invariant; eauto.
+
intuition.
}
+
eapply le_trans; [|eauto].
simpl in *.
omega.
}
break_exists.
intuition.
match goal with | H : findAtIndex _ _ = None |- _ => eapply findAtIndex_None with (x1 := x) in H end; eauto.
*
congruence.
*
apply msg_lifted_sorted_host; auto.
+
destruct (le_lt_dec (commitIndex (snd (nwState net (pDst p)))) (maxIndex es)); intuition; [match goal with | |- context [ maxIndex (?ll1 ++ ?ll2) ] => pose proof maxIndex_app ll1 ll2 end; simpl in *; intuition|]; [idtac].
exfalso.
assert (In p (nwPackets net)) by (find_rewrite; intuition).
break_exists; intuition.
find_apply_lem_hyp findAtIndex_elim; intuition.
find_copy_apply_lem_hyp maxIndex_non_empty.
break_exists.
intuition.
find_eapply_lem_hyp msg_lifted_sms_nw; eauto; [|eapply msg_commit_recorded_lift_intro; eauto; right; repeat find_rewrite; intuition].
match goal with | _ : In ?x es, _ : maxIndex es = eIndex ?x |- _ => assert (pli < eIndex x) by (eapply contiguous_range_exact_lo_elim_lt; eauto; eapply lifted_entries_contiguous_nw_invariant; eauto) end.
intuition.
*
match goal with | H : _ = _ ++ _ |- _ => symmetry in H end.
Admitted.

Lemma lifted_maxIndex_sanity_append_entries_reply : msg_refined_raft_net_invariant_append_entries_reply lifted_maxIndex_sanity.
Proof using.
unfold msg_refined_raft_net_invariant_append_entries_reply, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
intuition; repeat find_higher_order_rewrite; update_destruct_simplify; auto.
-
erewrite handleAppendEntriesReply_same_lastApplied by eauto.
erewrite handleAppendEntriesReply_same_log by eauto.
auto.
-
erewrite handleAppendEntriesReply_same_commitIndex by eauto.
erewrite handleAppendEntriesReply_same_log by eauto.
Admitted.

Lemma lifted_maxIndex_sanity_request_vote : msg_refined_raft_net_invariant_request_vote lifted_maxIndex_sanity.
Proof using.
unfold msg_refined_raft_net_invariant_request_vote, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
intuition; repeat find_higher_order_rewrite; update_destruct_simplify; auto.
-
erewrite handleRequestVote_same_log by eauto.
erewrite handleRequestVote_same_lastApplied by eauto.
auto.
-
erewrite handleRequestVote_same_log by eauto.
erewrite handleRequestVote_same_commitIndex by eauto.
Admitted.

Lemma lifted_maxIndex_sanity_request_vote_reply : msg_refined_raft_net_invariant_request_vote_reply lifted_maxIndex_sanity.
Proof using.
unfold msg_refined_raft_net_invariant_request_vote_reply, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
intuition; repeat find_higher_order_rewrite; update_destruct_simplify; auto.
-
rewrite handleRequestVoteReply_same_log.
rewrite handleRequestVoteReply_same_lastApplied.
auto.
-
rewrite handleRequestVoteReply_same_log.
rewrite handleRequestVoteReply_same_commitIndex.
Admitted.

Lemma doLeader_same_lastApplied : forall st n os st' ms, doLeader st n = (os, st', ms) -> lastApplied st' = lastApplied st.
Proof using.
unfold doLeader.
intros.
Admitted.

Lemma fold_left_maximum_le : forall l x, x <= fold_left max l x.
Proof using.
intros.
apply fold_left_maximum_le'.
Admitted.

Lemma fold_left_maxmimum_increase_init : forall l x y, fold_left max l x = x -> x <= y -> fold_left max l y = y.
Proof using.
induction l; intros.
-
auto.
-
simpl in *.
revert H.
repeat (apply Max.max_case_strong; intros).
+
eauto.
+
assert (a = y) by omega.
subst_max.
eauto.
+
subst x.
pose proof (fold_left_maximum_le l a).
assert (fold_left max l a = a) by omega.
eauto.
+
subst x.
pose proof (fold_left_maximum_le l a).
assert (fold_left max l a = a) by omega.
assert (a = y) by omega.
subst.
Admitted.

Lemma fold_left_maximum_cases : forall l x, fold_left max l x = x \/ exists y, In y l /\ fold_left max l x = y.
Proof using.
induction l; simpl.
-
auto.
-
intros.
specialize (IHl (max x a)).
intuition.
+
revert H.
apply Max.max_case_strong; intuition.
intuition eauto using fold_left_maxmimum_increase_init.
+
break_exists.
break_and.
Admitted.

Lemma fold_left_maximum_ind : forall l x (P : nat -> Prop), P x -> (forall y, In y l -> P y) -> P (fold_left max l x).
Proof using.
intros.
destruct (fold_left_maximum_cases l x).
-
find_rewrite.
auto.
-
break_exists.
break_and.
find_rewrite.
Admitted.

Lemma doLeader_same_commitIndex : forall st n os st' ms, doLeader st n = (os, st', ms) -> sorted (log st) -> commitIndex st <= maxIndex (log st) -> commitIndex st' <= maxIndex (log st').
Proof using.
unfold doLeader.
intros.
repeat break_match; repeat find_inversion; simpl; auto; apply fold_left_maximum_ind; auto.
-
intros.
do_in_map.
find_apply_lem_hyp filter_In.
subst.
break_and.
apply maxIndex_is_max; eauto using findGtIndex_in.
-
intros.
do_in_map.
find_apply_lem_hyp filter_In.
break_and.
subst.
Admitted.

Lemma lifted_maxIndex_sanity_do_leader : msg_refined_raft_net_invariant_do_leader lifted_maxIndex_sanity.
Proof using rmri si rri.
unfold msg_refined_raft_net_invariant_do_leader, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
intuition; repeat find_higher_order_rewrite; update_destruct_simplify; auto.
-
erewrite doLeader_same_log by eauto.
erewrite doLeader_same_lastApplied by eauto.
repeat match goal with | [ H : forall _ , _ |- _ ] => specialize (H h0) end.
unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params in *.
simpl in *.
repeat find_rewrite.
auto.
-
repeat match goal with | [ H : forall _ , _ |- _ ] => specialize (H h0) end.
unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params in *.
simpl in *.
repeat find_rewrite.
simpl in *.
erewrite doLeader_same_commitIndex; eauto.
find_eapply_lem_hyp (msg_lifted_sorted_host net h0).
unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params in *.
simpl in *.
find_rewrite.
Admitted.

Lemma doGenericServer_lastApplied : forall h st out st' ms, doGenericServer h st = (out, st', ms) -> lastApplied st' = lastApplied st \/ (lastApplied st < commitIndex st /\ lastApplied st' = commitIndex st).
Proof using.
unfold doGenericServer.
intros.
repeat break_match; repeat find_inversion; simpl.
-
do_bool.
revert Heqb.
eapply applyEntries_spec_ind; eauto.
-
do_bool.
revert Heqb.
Admitted.

Lemma lifted_maxIndex_sanity_do_generic_server : msg_refined_raft_net_invariant_do_generic_server lifted_maxIndex_sanity.
Proof using.
unfold msg_refined_raft_net_invariant_do_generic_server, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
intuition; find_higher_order_rewrite; update_destruct_simplify; auto; erewrite doGenericServer_log by eauto.
-
repeat match goal with | [ H : forall _ , _ |- _ ] => specialize (H h0) end.
repeat find_rewrite.
simpl in *.
find_apply_lem_hyp doGenericServer_lastApplied.
unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params in *.
simpl in *.
intuition; repeat find_rewrite; auto.
-
repeat match goal with | [ H : forall _ , _ |- _ ] => specialize (H h0) end.
unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params in *.
simpl in *.
repeat find_rewrite.
simpl in *.
erewrite doGenericServer_commitIndex by eauto.
Admitted.

Lemma lifted_maxIndex_sanity_state_same_packet_subset : msg_refined_raft_net_invariant_state_same_packet_subset lifted_maxIndex_sanity.
Proof using.
unfold msg_refined_raft_net_invariant_state_same_packet_subset, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
Admitted.

Lemma lifted_maxIndex_sanity_reboot : msg_refined_raft_net_invariant_reboot lifted_maxIndex_sanity.
Proof using.
unfold msg_refined_raft_net_invariant_reboot, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
unfold reboot.
Admitted.

Lemma fold_left_maximum_le' : forall l x y, x <= y -> x <= fold_left max l y.
Proof using.
induction l; intros.
-
auto.
-
simpl.
apply IHl.
apply Max.max_case_strong; omega.
