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

Lemma commit_invariant_append_entries : forall xs p ys (net : ghost_log_network) st' ps' gd d m t n pli plt es ci, handleAppendEntries (pDst p) (snd (nwState net (pDst p))) t n pli plt es ci = (d, m) -> gd = update_elections_data_appendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci -> snd (pBody p) = AppendEntries t n pli plt es ci -> commit_invariant net -> msg_refined_raft_intermediate_reachable net -> lifted_maxIndex_sanity net -> nwPackets net = xs ++ p :: ys -> (forall h, st' h = update name_eq_dec (nwState net) (pDst p) (gd, d) h) -> (forall p', In p' ps' -> In p' (xs ++ ys) \/ p' = mkPacket (pDst p) (pSrc p) (write_ghost_log (pDst p) (gd, d), m)) -> commit_invariant (mkNetwork ps' st').
Proof using rmri tsi glemi lphogli glci rlmli smspi si rri.
unfold commit_invariant.
intros.
assert (In p (nwPackets net)) by (repeat find_rewrite; auto with *).
split.
-
break_and.
match goal with | [ H : commit_invariant_host _ |- _ ] => rename H into Hhost; unfold commit_invariant_host in * end.
simpl.
intros.
eapply lifted_committed_ext; eauto.
match goal with | [ H : forall _, _ = _ |- _ ] => rewrite H in * end.
update_destruct_simplify.
+
find_copy_apply_lem_hyp handleAppendEntries_log_detailed.
break_or_hyp.
*
break_and.
repeat find_rewrite.
eapply lifted_committed_monotonic; [ solve [eapply handleAppendEntries_preserves_commit; eauto] | solve [eauto using handleAppendEntries_currentTerm_le] ].
*
{
break_or_hyp; repeat break_and.
-
repeat match goal with | [ H : _ <= _, H': _ |- _ ] => rewrite H' in H end.
find_apply_lem_hyp NPeano.Nat.max_le.
break_or_hyp.
+
assert (eIndex e > 0) by (eapply lifted_entries_gt_0_nw_invariant; eauto).
assert (exists e', eIndex e' = eIndex e /\ In e' (log (snd (nwState net (pDst p))))).
{
eapply contiguous_range_exact_lo_elim_exists.
-
eapply lifted_entries_contiguous_invariant.
auto.
-
split.
+
auto.
+
eapply le_trans; [eauto|].
eapply_prop lifted_maxIndex_sanity.
}
break_exists_name e'.
break_and.
assert (lifted_committed net e' (currentTerm (snd (nwState net (pDst p))))) as He'committed by (apply Hhost; [auto|congruence]) .
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
concludes.
assert (sorted (log d)) by (eauto using lifted_handleAppendEntries_logs_sorted).
intuition.
*
omega.
*
omega.
*
match goal with | [ H : _ |- _ ] => eapply maxIndex_is_max in H; eauto; [idtac] end.
omega.
*
assert (e = e') by (eapply uniqueIndices_elim_eq; eauto using sorted_uniqueIndices).
subst.
eapply lifted_committed_monotonic; [ solve [eapply handleAppendEntries_preserves_commit; eauto] | solve [eauto using handleAppendEntries_currentTerm_le] ].
+
match goal with | [ H : commit_invariant_nw _ |- _ ] => rename H into Hnet; unfold commit_invariant_nw in * end.
eapply_prop_hyp In In; [| eauto | | eauto using Min.min_glb_l].
*
eapply handleAppendEntries_preserves_commit; eauto.
*
find_eapply_lem_hyp ghost_log_correct_invariant; eauto.
conclude_using eauto.
{
intuition.
-
match goal with | [ H : In _ _, H' : _ |- _ ] => rewrite H' in H end.
auto.
-
break_exists.
break_and.
pose proof log_properties_hold_on_ghost_logs_invariant _ ltac:(eauto) as Hprop.
unfold log_properties_hold_on_ghost_logs in *.
unfold msg_log_property in *.
specialize (Hprop (fun l => forall e, In e l -> eIndex e > 0) p).
conclude_using ltac:(intros; eapply lifted_entries_gt_0_invariant; eauto).
conclude_using eauto.
simpl in *.
find_apply_hyp_hyp.
omega.
}
-
break_exists_name ple.
break_and.
repeat match goal with | [ H : _ <= _, H': _ |- _ ] => rewrite H' in H end.
find_apply_lem_hyp NPeano.Nat.max_le.
break_or_hyp.
+
repeat find_rewrite.
match goal with | [ H : In e (_ ++ _) |- _ ] => apply in_app_or in H; destruct H end.
*
{
assert (eIndex e > 0) by (eapply lifted_entries_gt_0_nw_invariant; eauto).
assert (exists e', eIndex e' = eIndex e /\ In e' (log (snd (nwState net (pDst p))))).
{
eapply contiguous_range_exact_lo_elim_exists.
-
eapply lifted_entries_contiguous_invariant.
auto.
-
split.
+
auto.
+
eapply le_trans; [eauto|].
eapply_prop lifted_maxIndex_sanity.
}
break_exists_name e'.
break_and.
assert (lifted_committed net e' (currentTerm (snd (nwState net (pDst p))))) as He'committed by (apply Hhost; [auto|congruence]) .
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
concludes.
assert (sorted es) by (eapply lifted_entries_sorted_nw'_invariant; eauto).
assert (contiguous_range_exact_lo es (eIndex ple)) by (eapply lifted_entries_contiguous_nw_invariant; eauto).
find_eapply_lem_hyp contiguous_range_exact_lo_elim_lt; eauto.
intuition.
*
omega.
*
omega.
*
match goal with | [ H : _ |- _ ] => eapply maxIndex_is_max in H; eauto with *; [idtac] end.
omega.
*
assert (e = e') by (eapply uniqueIndices_elim_eq; eauto using sorted_uniqueIndices).
subst.
eapply lifted_committed_monotonic; [ solve [eapply handleAppendEntries_preserves_commit; eauto] | solve [eauto using handleAppendEntries_currentTerm_le] ].
}
*
{
eapply lifted_committed_monotonic.
-
eapply handleAppendEntries_preserves_commit; eauto.
eapply Hhost with (h := pDst p); eauto using removeAfterIndex_in.
-
eauto using handleAppendEntries_currentTerm_le.
}
+
match goal with | [ H : In e _ |- _ ] => repeat match goal with | [ H' : _ |- _ ] => rewrite H' in H end; apply in_app_or in H; destruct H end.
*
{
match goal with | [ H : commit_invariant_nw _ |- _ ] => rename H into Hnet; unfold commit_invariant_nw in * end.
match goal with | [ H : In _ (nwPackets _), H' : _ |- _ ] => eapply H' in H end; [| eauto | | eauto using Min.min_glb_l].
*
eapply handleAppendEntries_preserves_commit; eauto.
*
find_copy_eapply_lem_hyp ghost_log_correct_invariant; eauto.
conclude_using eauto.
{
intuition.
-
match goal with | [ H : In _ _, H' : _ |- _ ] => rewrite H' in H end.
auto.
-
break_exists_name gple.
break_and.
subst.
eauto using findGtIndex_in.
}
}
*
assert (eIndex e <= eIndex ple) by (eapply removeAfterIndex_In_le; eauto using msg_lifted_sorted_host).
pose proof log_properties_hold_on_ghost_logs_invariant _ ltac:(eauto) as Hprop.
unfold log_properties_hold_on_ghost_logs in *.
unfold msg_log_property in *.
specialize (Hprop (fun l => contiguous_range_exact_lo l 0) p).
conclude_using ltac:(intros; eapply lifted_entries_contiguous_invariant; eauto).
concludes.
simpl in *.
find_copy_eapply_lem_hyp ghost_log_correct_invariant; eauto.
conclude_using eauto.
{
intuition.
-
subst.
find_apply_lem_hyp removeAfterIndex_in.
pose proof lifted_entries_gt_0_invariant _ ltac:(eauto) _ _ ltac:(eauto).
omega.
-
break_exists_name gple.
break_and.
assert (exists e', eIndex e' = eIndex e /\ In e' (fst (pBody p))).
{
eapply contiguous_range_exact_lo_elim_exists; eauto.
split.
+
eapply lifted_entries_gt_0_invariant; eauto using removeAfterIndex_in.
+
eapply le_trans with (m := eIndex gple); try omega.
apply maxIndex_is_max; auto.
pose proof log_properties_hold_on_ghost_logs_invariant _ ltac:(eauto) as Hsort.
unfold log_properties_hold_on_ghost_logs in *.
unfold msg_log_property in *.
specialize (Hsort sorted p msg_lifted_sorted_host).
auto.
}
break_exists_name e'.
break_and.
find_apply_lem_hyp removeAfterIndex_in.
assert (e = e').
{
eapply uniqueIndices_elim_eq; eauto using msg_lifted_sorted_host, sorted_uniqueIndices.
pose proof ghost_log_entries_match_invariant _ ltac:(eauto) (pDst p) _ ltac:(eauto) as Hem.
specialize (Hem ple gple e').
repeat concludes.
assert (eIndex e' <= eIndex ple) by omega.
intuition.
}
subst.
match goal with | [ H : commit_invariant_nw _ |- _ ] => rename H into Hnet; unfold commit_invariant_nw in * end.
eapply handleAppendEntries_preserves_commit; eauto.
eapply Hnet; eauto using Min.min_glb_l.
}
}
+
eapply handleAppendEntries_preserves_commit; eauto.
-
break_and.
unfold commit_invariant_nw in *.
simpl.
intros.
find_apply_hyp_hyp.
intuition.
+
eapply handleAppendEntries_preserves_commit; eauto.
simpl.
subst.
auto.
+
subst.
simpl in *.
find_apply_lem_hyp handleAppendEntries_not_append_entries.
subst.
exfalso.
eauto 10.
