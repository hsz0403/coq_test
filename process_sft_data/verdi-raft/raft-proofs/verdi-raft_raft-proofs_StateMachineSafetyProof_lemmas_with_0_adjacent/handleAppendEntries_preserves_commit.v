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

Lemma handleAppendEntries_preserves_commit : forall net net' h p t n pli plt es ci d m e t', msg_refined_raft_intermediate_reachable net -> In p (nwPackets net) -> snd (pBody p) = AppendEntries t n pli plt es ci -> handleAppendEntries h (snd (nwState net h)) t n pli plt es ci = (d, m) -> (forall h', nwState net' h' = update name_eq_dec (nwState net) h (update_elections_data_appendEntries h (nwState net h) t n pli plt es ci, d) h') -> lifted_committed net e t' -> lifted_committed net' e t'.
Proof using rmri tsi rlmli smspi si rri.
intros.
unfold lifted_committed in *.
break_exists_name host.
break_exists_name e'.
exists host, e'.
intuition.
-
unfold lifted_directly_committed in *.
break_exists_exists; intuition.
find_higher_order_rewrite.
update_destruct_simplify; eauto using update_elections_data_appendEntries_preserves_allEntries'.
-
find_higher_order_rewrite.
update_destruct_simplify; simpl in *; eauto.
assert (lifted_committed net e (currentTerm (snd (nwState net host)))) by (unfold lifted_committed; exists host, e'; intuition; eapply lifted_no_entries_past_current_term_host_invariant; eauto).
find_eapply_lem_hyp handleAppendEntries_log_detailed.
intuition; repeat find_rewrite; eauto.
+
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
assert (eIndex e > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
intuition; try omega.
find_copy_eapply_lem_hyp msg_lifted_sorted_host.
exfalso.
enough (exists e, eIndex e = (maxIndex es) /\ In e (log (snd (nwState net host)))) by (break_exists; intuition; eapply findAtIndex_None; eauto).
eapply contiguous_range_exact_lo_elim_exists; [apply lifted_entries_contiguous_invariant; auto|].
intuition.
*
find_apply_lem_hyp maxIndex_non_empty.
break_exists; intuition; repeat find_rewrite.
enough (eIndex x > 0) by omega.
eapply lifted_entries_contiguous_nw_invariant; eauto.
*
enough (eIndex e <= maxIndex (log (snd (nwState net host)))) by omega.
apply maxIndex_is_max; auto.
+
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
assert (eIndex e > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
intuition; try omega.
break_exists.
intuition.
find_apply_lem_hyp maxIndex_non_empty.
break_exists_name maxEntry; intuition.
repeat find_rewrite.
find_false.
f_equal.
find_apply_lem_hyp findAtIndex_elim.
intuition.
eapply uniqueIndices_elim_eq; [| |eauto|]; eauto using sorted_uniqueIndices,lifted_entries_sorted_nw.
match goal with | |- In ?e _ => assert (lifted_committed net e (currentTerm (snd (nwState net host)))) by (unfold lifted_committed; exists host, e'; intuition; eapply lifted_no_entries_past_current_term_host_invariant; eauto) end.
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
assert (eIndex x > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
intuition; omega.
+
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
intuition; try solve [apply in_app_iff; right; apply removeAfterIndex_le_In; auto; omega]; [idtac].
find_copy_eapply_lem_hyp msg_lifted_sorted_host.
exfalso.
enough (exists e, eIndex e = (maxIndex es) /\ In e (log (snd (nwState net host)))) by (break_exists; intuition; eapply findAtIndex_None; eauto).
eapply contiguous_range_exact_lo_elim_exists; [apply lifted_entries_contiguous_invariant; auto|].
intuition.
*
find_apply_lem_hyp maxIndex_non_empty.
break_exists; intuition; repeat find_rewrite.
enough (eIndex x0 > 0) by omega.
enough (eIndex x0 > pli) by omega.
eapply lifted_entries_contiguous_nw_invariant; eauto.
*
enough (eIndex e <= maxIndex (log (snd (nwState net host)))) by omega.
apply maxIndex_is_max; auto.
+
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
intuition; try solve [apply in_app_iff; right; apply removeAfterIndex_le_In; auto; omega]; [idtac].
break_exists.
intuition.
find_apply_lem_hyp maxIndex_non_empty.
break_exists_name maxEntry; intuition.
repeat find_rewrite.
find_false.
f_equal.
find_apply_lem_hyp findAtIndex_elim.
intuition.
eapply uniqueIndices_elim_eq; [| |eauto|]; eauto using sorted_uniqueIndices,lifted_entries_sorted_nw.
match goal with | |- In ?e _ => assert (lifted_committed net e (currentTerm (snd (nwState net host)))) by (unfold lifted_committed; exists host, e'; intuition; eapply lifted_no_entries_past_current_term_host_invariant; eauto) end.
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
intuition; try omega; enough (pli < eIndex maxEntry) by omega; eapply lifted_entries_contiguous_nw_invariant; eauto.
-
find_higher_order_rewrite.
update_destruct_simplify; simpl in *; eauto.
assert (lifted_committed net e' (currentTerm (snd (nwState net host)))) by (unfold lifted_committed; exists host, e'; intuition; eapply lifted_no_entries_past_current_term_host_invariant; eauto).
find_eapply_lem_hyp handleAppendEntries_log_detailed.
intuition; repeat find_rewrite; eauto.
+
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
assert (eIndex e' > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
intuition; try omega.
find_copy_eapply_lem_hyp msg_lifted_sorted_host.
exfalso.
enough (exists e, eIndex e = (maxIndex es) /\ In e (log (snd (nwState net host)))) by (break_exists; intuition; eapply findAtIndex_None; eauto).
eapply contiguous_range_exact_lo_elim_exists; [apply lifted_entries_contiguous_invariant; auto|].
intuition.
*
find_apply_lem_hyp maxIndex_non_empty.
break_exists; intuition; repeat find_rewrite.
enough (eIndex x > 0) by omega.
eapply lifted_entries_contiguous_nw_invariant; eauto.
*
enough (eIndex e' <= maxIndex (log (snd (nwState net host)))) by omega.
apply maxIndex_is_max; auto.
+
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
assert (eIndex e' > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
intuition; try omega.
break_exists.
intuition.
find_apply_lem_hyp maxIndex_non_empty.
break_exists_name maxEntry; intuition.
repeat find_rewrite.
find_false.
f_equal.
find_apply_lem_hyp findAtIndex_elim.
intuition.
eapply uniqueIndices_elim_eq; [| |eauto|]; eauto using sorted_uniqueIndices,lifted_entries_sorted_nw.
match goal with | |- In ?e _ => assert (lifted_committed net e (currentTerm (snd (nwState net host)))) by (unfold lifted_committed; exists host, e'; intuition; eapply lifted_no_entries_past_current_term_host_invariant; eauto) end.
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
assert (eIndex x > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
intuition; omega.
+
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
intuition; try solve [apply in_app_iff; right; apply removeAfterIndex_le_In; auto; omega]; [idtac].
find_copy_eapply_lem_hyp msg_lifted_sorted_host.
exfalso.
enough (exists e, eIndex e = (maxIndex es) /\ In e (log (snd (nwState net host)))) by (break_exists; intuition; eapply findAtIndex_None; eauto).
eapply contiguous_range_exact_lo_elim_exists; [apply lifted_entries_contiguous_invariant; auto|].
intuition.
*
find_apply_lem_hyp maxIndex_non_empty.
break_exists; intuition; repeat find_rewrite.
enough (eIndex x0 > 0) by omega.
enough (eIndex x0 > pli) by omega.
eapply lifted_entries_contiguous_nw_invariant; eauto.
*
enough (eIndex e' <= maxIndex (log (snd (nwState net host)))) by omega.
apply maxIndex_is_max; auto.
+
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
intuition; try solve [apply in_app_iff; right; apply removeAfterIndex_le_In; auto; omega]; [idtac].
break_exists.
intuition.
find_apply_lem_hyp maxIndex_non_empty.
break_exists_name maxEntry; intuition.
repeat find_rewrite.
find_false.
f_equal.
find_apply_lem_hyp findAtIndex_elim.
intuition.
eapply uniqueIndices_elim_eq; [| |eauto|]; eauto using sorted_uniqueIndices,lifted_entries_sorted_nw.
match goal with | |- In ?e _ => assert (lifted_committed net e (currentTerm (snd (nwState net host)))) by (unfold lifted_committed; exists host, e'; intuition; eapply lifted_no_entries_past_current_term_host_invariant; eauto) end.
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
intuition; try omega; enough (pli < eIndex maxEntry) by omega; eapply lifted_entries_contiguous_nw_invariant; eauto.
