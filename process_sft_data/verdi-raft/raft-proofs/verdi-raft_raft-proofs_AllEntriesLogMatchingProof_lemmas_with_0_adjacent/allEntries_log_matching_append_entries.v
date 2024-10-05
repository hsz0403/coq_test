Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.AllEntriesLeaderSublogInterface.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.AllEntriesLogMatchingInterface.
Section AllEntriesLogMatching.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {aelsi : allEntries_leader_sublog_interface}.
Context {lsi : leader_sublog_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Definition allEntries_log_matching_nw net := forall (e e' : entry) (h : name) (p : packet) t leaderId prevLogIndex prevLogTerm entries leaderCommit, In p (nwPackets net) -> pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit -> In e entries -> In e' (map snd (allEntries (fst (nwState net h)))) -> eTerm e = eTerm e' -> eIndex e = eIndex e' -> e = e'.
Definition allEntries_log_matching_inductive net := allEntries_log_matching net /\ allEntries_log_matching_nw net.
Ltac start := red; unfold allEntries_log_matching_inductive; simpl; intros.
Ltac start_update := start; intuition; [unfold allEntries_log_matching in *|unfold allEntries_log_matching_nw in *]; intros; repeat find_higher_order_rewrite; repeat (update_destruct; rewrite_update); subst; simpl; eauto.
Definition leader_sublog (net : network) := forall leader e h, type (snd (nwState net leader)) = Leader -> In e (log (snd (nwState net h))) -> eTerm e = currentTerm (snd (nwState net leader)) -> In e (log (snd (nwState net leader))).
Ltac fix_data := do 2 (unfold raft_data in *; simpl in *).
Ltac contradict_maxIndex := exfalso; find_apply_lem_hyp maxIndex_is_max; try (fix_data; omega); eapply entries_sorted_invariant; eauto.
Ltac unchanged := red; intros; eapply allEntries_log_matching_unchanged; subst; eauto.
Instance aelmi : allEntries_log_matching_interface.
Proof.
constructor.
intros.
apply allEntries_log_matching_inductive_invariant; auto.
End AllEntriesLogMatching.

Lemma allEntries_log_matching_append_entries : refined_raft_net_invariant_append_entries allEntries_log_matching_inductive.
Proof using rlmli.
start_update; simpl in *.
-
match goal with | H : context [handleAppendEntries] |- _ => eapply update_elections_data_appendEntries_log_allEntries with (h' := n) in H end ; intuition; repeat find_rewrite; simpl in *; intuition; subst; eauto; try (find_rewrite_lem map_app; find_rewrite_lem map_map; simpl in *; find_rewrite_lem map_id; do_in_app; intuition; eauto).
+
enough (In e' (log (snd (nwState net (pDst p))))) by (eapply uniqueIndices_elim_eq; eauto; apply sorted_uniqueIndices; eapply entries_sorted_invariant; eauto).
eapply entries_match_nw_host_invariant; eauto.
+
eapply uniqueIndices_elim_eq; eauto; apply sorted_uniqueIndices; eapply entries_sorted_nw_invariant; eauto.
+
do_in_app.
intuition.
*
eapply uniqueIndices_elim_eq; eauto; apply sorted_uniqueIndices; eapply entries_sorted_nw_invariant; eauto.
*
find_apply_lem_hyp removeAfterIndex_in.
enough (In e' (log (snd (nwState net (pDst p))))) by (eapply uniqueIndices_elim_eq; eauto; apply sorted_uniqueIndices; eapply entries_sorted_invariant; eauto).
eapply entries_match_nw_host_invariant; eauto.
+
do_in_app; intuition; eauto using removeAfterIndex_in.
-
match goal with | H : context [handleAppendEntries] |- _ => eapply update_elections_data_appendEntries_log_allEntries with (h' := n) in H end ; intuition; repeat find_rewrite; simpl in *; intuition; subst; eauto; try (find_rewrite_lem map_app; find_rewrite_lem map_map; simpl in *; find_rewrite_lem map_id; do_in_app; intuition; eauto).
+
enough (In e' (log (snd (nwState net h)))) by (eapply uniqueIndices_elim_eq; eauto; apply sorted_uniqueIndices; eapply entries_sorted_invariant; eauto).
eapply entries_match_nw_host_invariant; eauto.
+
enough (In e' (log (snd (nwState net h)))) by (eapply uniqueIndices_elim_eq; eauto; apply sorted_uniqueIndices; eapply entries_sorted_invariant; eauto).
eapply entries_match_nw_host_invariant; eauto.
+
enough (In e' (log (snd (nwState net h)))) by (eapply uniqueIndices_elim_eq; eauto; apply sorted_uniqueIndices; eapply entries_sorted_invariant; eauto).
eapply entries_match_nw_host_invariant; eauto.
-
find_apply_lem_hyp handleAppendEntries_log.
intuition; repeat find_rewrite; simpl in *; eauto.
do_in_app.
intuition; eauto using removeAfterIndex_in.
-
find_apply_hyp_hyp.
intuition; [|exfalso; do_in_map; subst; simpl in *; find_eapply_lem_hyp handleAppendEntries_not_append_entries; eauto; intuition; repeat find_rewrite; find_false; repeat eexists; eauto].
assert (In p0 (xs ++ p :: ys)) by in_crush.
match goal with | H : context [handleAppendEntries] |- _ => eapply update_elections_data_appendEntries_log_allEntries with (h' := n) in H end.
intuition; repeat find_rewrite; simpl in *; subst; intuition; eauto.
+
find_rewrite_lem map_app.
find_rewrite_lem map_map.
simpl in *.
find_rewrite_lem map_id.
apply in_app_or in H11.
intuition; eauto.
eauto using packets_entries_eq.
+
find_rewrite_lem map_app.
find_rewrite_lem map_map.
simpl in *.
find_rewrite_lem map_id.
apply in_app_or in H11.
intuition; eauto.
eauto using packets_entries_eq.
+
find_rewrite_lem map_app.
find_rewrite_lem map_map.
simpl in *.
find_rewrite_lem map_id.
apply in_app_or in H11.
intuition; eauto.
eauto using packets_entries_eq.
-
find_apply_hyp_hyp.
intuition; [|exfalso; do_in_map; subst; simpl in *; eapply handleAppendEntries_not_append_entries; eauto; intuition; repeat find_rewrite; repeat eexists; eauto].
eauto.
