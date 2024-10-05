Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.UniqueIndicesInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.MaxIndexSanityInterface.
Require Import VerdiRaft.CommitRecordedCommittedInterface.
Require Import VerdiRaft.LeaderCompletenessInterface.
Require Import VerdiRaft.LastAppliedCommitIndexMatchingInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.AppliedEntriesMonotonicInterface.
Section AppliedEntriesMonotonicProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {si : sorted_interface}.
Context {lmi : log_matching_interface}.
Context {uii : unique_indices_interface}.
Context {smsi : state_machine_safety_interface}.
Context {misi : max_index_sanity_interface}.
Context {crci : commit_recorded_committed_interface}.
Context {lci : leader_completeness_interface}.
Context {lacimi : lastApplied_commitIndex_match_interface}.
Instance aemi : applied_entries_monotonic_interface.
Proof.
split; eauto using applied_entries_monotonic, applied_entries_monotonic'.
End AppliedEntriesMonotonicProof.

Lemma entries_max_thing : forall net p es, raft_intermediate_reachable net -> In p (nwPackets net) -> mEntries (pBody p) = Some es -> es <> nil -> 1 <= maxIndex es.
Proof using lmi.
intros.
find_apply_lem_hyp maxIndex_non_empty.
break_exists; intuition; find_rewrite.
find_apply_lem_hyp log_matching_invariant.
unfold log_matching, log_matching_nw in *.
intuition.
destruct (pBody p) eqn:?; simpl in *; try congruence.
find_apply_hyp_hyp.
intuition.
find_inversion.
find_apply_hyp_hyp.
Admitted.

Lemma deghost_snd : forall net h, snd (nwState net h) = nwState (deghost net) h.
Proof using.
intros.
unfold deghost in *.
simpl.
repeat break_match; subst; simpl.
repeat find_rewrite.
Admitted.

Lemma lt_committed_committed : forall net e e' t h, log_matching (deghost net) -> committed net e t -> eIndex e' <= eIndex e -> In e (log (snd (nwState net h))) -> In e' (log (snd (nwState net h))) -> committed net e' t.
Proof using.
intros.
unfold committed in *.
break_exists_exists.
intuition.
unfold log_matching, log_matching_hosts in *.
intuition.
unfold entries_match in *.
rewrite deghost_snd in *.
Admitted.

Lemma logs_contiguous : forall net h, raft_intermediate_reachable net -> contiguous_range_exact_lo (log (nwState net h)) 0.
Proof using lmi.
intros.
find_apply_lem_hyp log_matching_invariant.
unfold log_matching, log_matching_hosts in *.
intuition.
unfold contiguous_range_exact_lo.
intuition eauto.
find_apply_hyp_hyp.
Admitted.

Lemma entries_gt_0 : forall net p es e, raft_intermediate_reachable net -> In p (nwPackets net) -> mEntries (pBody p) = Some es -> In e es -> 0 < eIndex e.
Proof using lmi.
intros.
find_apply_lem_hyp log_matching_invariant.
unfold log_matching, log_matching_nw in *.
intuition.
destruct (pBody p) eqn:?; simpl in *; try congruence.
find_inversion.
find_apply_hyp_hyp.
intuition.
find_apply_hyp_hyp.
Admitted.

Lemma entries_gt_pli : forall net p e t n pli plt es ci, raft_intermediate_reachable net -> In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> In e es -> pli < eIndex e.
Proof using lmi.
intros.
find_apply_lem_hyp log_matching_invariant.
unfold log_matching, log_matching_nw in *.
intuition.
destruct (pBody p) eqn:?; simpl in *; try congruence.
find_inversion.
find_apply_hyp_hyp.
Admitted.

Lemma sorted_app : forall l l', sorted (l ++ l') -> sorted l.
Proof using.
induction l; simpl in *; intros; intuition eauto.
-
apply H0.
intuition.
-
apply H0.
Admitted.

Lemma handleMessage_applied_entries : forall net h h' m st' ms, raft_intermediate_reachable net -> In {| pBody := m; pDst := h; pSrc := h' |} (nwPackets net) -> handleMessage h' h m (nwState net h) = (st', ms) -> applied_entries (nwState net) = applied_entries (update name_eq_dec (nwState net) h st').
Proof using misi smsi uii lmi si.
intros.
symmetry.
unfold handleMessage in *.
break_match; repeat break_let; repeat find_inversion.
-
apply applied_entries_log_lastApplied_update_same; eauto using handleRequestVote_same_log, handleRequestVote_same_lastApplied.
-
apply applied_entries_log_lastApplied_update_same; eauto using handleRequestVoteReply_same_log, handleRequestVoteReply_same_lastApplied.
-
find_copy_eapply_lem_hyp handleAppendEntries_logs_sorted; eauto using logs_sorted_invariant.
apply applied_entries_safe_update; eauto using handleAppendEntries_same_lastApplied.
find_apply_lem_hyp handleAppendEntries_log_detailed.
intuition.
+
repeat find_rewrite.
auto.
+
subst.
find_copy_apply_lem_hyp state_machine_safety_invariant.
unfold state_machine_safety in *.
intuition.
find_copy_apply_lem_hyp max_index_sanity_invariant.
intuition.
find_copy_apply_lem_hyp logs_sorted_invariant.
unfold logs_sorted, maxIndex_sanity in *.
intuition.
apply removeAfterIndex_same_sufficient; eauto.
*
intros.
copy_eapply_prop_hyp state_machine_safety_nw In; unfold commit_recorded in *.
simpl in *; repeat (forwards; eauto; concludes).
intuition; try omega; exfalso; find_eapply_lem_hyp findAtIndex_max_thing; eauto; try break_exists; try congruence; eauto using entries_max_thing; find_apply_lem_hyp logs_contiguous; auto; omega.
*
intros.
find_copy_apply_lem_hyp log_matching_invariant.
unfold log_matching, log_matching_hosts in *.
intuition.
match goal with | H : forall _ _, _ <= _ <= _ -> _ |- _ => specialize (H h (eIndex e)); forward H end; copy_eapply_prop_hyp log_matching_nw AppendEntries; eauto; repeat (forwards; [intuition eauto; omega|]; concludes); intuition; [eapply le_trans; eauto|].
match goal with | H : exists _, _ |- _ => destruct H as [e'] end.
intuition.
copy_eapply_prop_hyp state_machine_safety_nw In; unfold commit_recorded in *; simpl in *; repeat (forwards; [intuition eauto; omega|]; concludes).
match goal with H : _ /\ (_ \/ _) |- _ => clear H end.
intuition; try omega; [|find_copy_apply_lem_hyp UniqueIndices_invariant; unfold UniqueIndices in *; intuition; eapply rachet; [symmetry|idtac|idtac|idtac|idtac]; eauto].
exfalso.
find_eapply_lem_hyp findAtIndex_max_thing; eauto; try break_exists; try congruence; eauto using entries_max_thing.
+
repeat find_rewrite.
find_copy_apply_lem_hyp state_machine_safety_invariant.
find_copy_apply_lem_hyp max_index_sanity_invariant.
unfold state_machine_safety, maxIndex_sanity in *.
intuition.
find_copy_apply_lem_hyp logs_sorted_invariant.
unfold logs_sorted in *.
intuition.
eapply removeAfterIndex_same_sufficient'; eauto using logs_contiguous.
*
intros.
eapply entries_gt_0; intuition eauto.
*
intros.
copy_eapply_prop_hyp state_machine_safety_nw In; unfold commit_recorded in *; simpl in *; repeat (forwards; [intuition eauto; omega|]; concludes).
match goal with H : _ /\ (_ \/ _) |- _ => clear H end.
intuition; try omega; try solve [find_apply_lem_hyp logs_contiguous; auto; omega].
exfalso.
subst.
break_exists.
intuition.
find_false.
find_apply_lem_hyp maxIndex_non_empty.
break_exists.
intuition.
repeat find_rewrite.
f_equal.
find_apply_lem_hyp findAtIndex_elim.
intuition.
eapply uniqueIndices_elim_eq with (xs := log st'); eauto using sorted_uniqueIndices.
unfold state_machine_safety_nw in *.
eapply_prop_hyp commit_recorded In; intuition; eauto; try omega; try solve [find_apply_lem_hyp logs_contiguous; auto; omega].
unfold commit_recorded.
intuition.
+
repeat find_rewrite.
find_copy_apply_lem_hyp logs_sorted_invariant.
unfold logs_sorted in *.
intuition.
eapply removeAfterIndex_same_sufficient'; eauto using logs_contiguous.
*
{
intros.
do_in_app.
intuition.
-
eapply entries_gt_0; eauto.
reflexivity.
-
find_apply_lem_hyp removeAfterIndex_in.
find_apply_lem_hyp logs_contiguous; eauto.
}
*
find_apply_lem_hyp max_index_sanity_invariant.
unfold maxIndex_sanity in *.
intuition.
*
intros.
find_copy_apply_lem_hyp state_machine_safety_invariant.
unfold state_machine_safety in *.
break_and.
copy_eapply_prop_hyp state_machine_safety_nw In; eauto.
simpl in *.
intuition eauto.
forwards; eauto.
concludes.
forwards; [unfold commit_recorded in *; intuition eauto|].
concludes.
intuition; apply in_app_iff; try solve [right; eapply removeAfterIndex_le_In; eauto; omega]; exfalso.
find_eapply_lem_hyp findAtIndex_max_thing; eauto using entries_max_thing.
break_exists; congruence.
+
break_exists.
intuition.
subst.
repeat find_rewrite.
find_copy_apply_lem_hyp logs_sorted_invariant.
unfold logs_sorted in *.
intuition.
eapply removeAfterIndex_same_sufficient'; eauto using logs_contiguous.
*
{
intros.
do_in_app.
intuition.
-
eapply entries_gt_0; eauto.
reflexivity.
-
find_apply_lem_hyp removeAfterIndex_in.
find_apply_lem_hyp logs_contiguous; eauto.
}
*
find_apply_lem_hyp max_index_sanity_invariant.
unfold maxIndex_sanity in *.
intuition.
*
{
intros.
find_copy_apply_lem_hyp state_machine_safety_invariant.
unfold state_machine_safety in *.
break_and.
copy_eapply_prop_hyp state_machine_safety_nw In; eauto.
simpl in *.
intuition eauto.
forwards; eauto.
concludes.
forwards; [unfold commit_recorded in *; intuition eauto|].
concludes.
intuition; apply in_app_iff; try solve [right; eapply removeAfterIndex_le_In; eauto; omega].
subst.
find_apply_lem_hyp maxIndex_non_empty.
break_exists.
intuition.
repeat find_rewrite.
find_apply_lem_hyp findAtIndex_elim.
intuition.
find_false.
f_equal.
eapply uniqueIndices_elim_eq with (xs := log (nwState net h)); eauto using sorted_uniqueIndices.
unfold state_machine_safety_nw in *.
eapply rachet; eauto using sorted_app, sorted_uniqueIndices.
copy_eapply_prop_hyp commit_recorded In; intuition; eauto; try omega; unfold commit_recorded; intuition.
-
exfalso.
pose proof entries_gt_pli.
eapply_prop_hyp AppendEntries AppendEntries; [|idtac|simpl; eauto|]; eauto.
omega.
-
exfalso.
pose proof entries_gt_pli.
eapply_prop_hyp AppendEntries AppendEntries; [|idtac|simpl; eauto|]; eauto.
omega.
}
-
Admitted.

Theorem handleTimeout_log : forall h st out st' ps, handleTimeout h st = (out, st', ps) -> log st' = log st.
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Lemma handleInput_applied_entries : forall net h inp os st' ms, raft_intermediate_reachable net -> handleInput h inp (nwState net h) = (os, st', ms) -> applied_entries (nwState net) = applied_entries (update name_eq_dec (nwState net) h st').
Proof using misi.
intros.
symmetry.
unfold handleInput in *.
break_match; repeat break_let; repeat find_inversion.
-
apply applied_entries_log_lastApplied_update_same; eauto using handleTimeout_log, handleTimeout_lastApplied.
-
apply applied_entries_safe_update; eauto using handleClientRequest_lastApplied.
destruct (log st') using (handleClientRequest_log_ind ltac:(eauto)); auto.
simpl in *.
break_if; auto.
exfalso.
do_bool.
find_apply_lem_hyp max_index_sanity_invariant.
unfold maxIndex_sanity, maxIndex_lastApplied in *.
intuition.
match goal with | H : forall _, _ |- _ => specialize (H h) end.
Admitted.

Lemma findAtIndex_max_thing : forall net h e i, raft_intermediate_reachable net -> In e (log (nwState net h)) -> eIndex e > i -> 1 <= i -> exists e', findAtIndex (log (nwState net h)) i = Some e'.
Proof using lmi si.
intros.
find_copy_apply_lem_hyp logs_sorted_invariant.
pose proof log_matching_invariant.
eapply_prop_hyp raft_intermediate_reachable raft_intermediate_reachable.
unfold log_matching, log_matching_hosts, logs_sorted in *.
intuition.
match goal with | H : forall _ _, _ <= _ <= _ -> _ |- _ => specialize (H h i); conclude H ltac:(intuition; find_apply_lem_hyp maxIndex_is_max; eauto; omega) end.
break_exists_exists.
intuition.
apply findAtIndex_intro; eauto using sorted_uniqueIndices.
