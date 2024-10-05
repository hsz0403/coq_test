Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.SortedInterface.
Section SortedProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {tsi : term_sanity_interface}.
Ltac find_eapply_hyp_goal := match goal with | H : _ |- _ => eapply H end.
Instance si : sorted_interface.
Proof.
split.
eauto using handleAppendEntries_logs_sorted.
eauto using handleClientRequest_logs_sorted.
auto using logs_sorted_invariant.
End SortedProof.

Theorem packets_gt_prevIndex_packets_unchanged : forall net ps' st', packets_gt_prevIndex net -> (forall p, In p ps' -> In p (nwPackets net) \/ False) -> packets_gt_prevIndex (mkNetwork ps' st').
Proof using.
unfold packets_gt_prevIndex in *.
intros.
simpl in *.
find_apply_hyp_hyp.
Admitted.

Theorem packets_ge_prevTerm_packets_unchanged : forall net ps' st', packets_ge_prevTerm net -> (forall p, In p ps' -> In p (nwPackets net) \/ False) -> packets_ge_prevTerm (mkNetwork ps' st').
Proof using.
unfold packets_ge_prevTerm in *.
intros.
simpl in *.
find_apply_hyp_hyp.
Admitted.

Lemma handleClientRequest_logs_sorted : forall h client id c out st l net, handleClientRequest h (nwState net h) client id c = (out, st, l) -> raft_intermediate_reachable net -> logs_sorted_host net -> sorted (log st).
Proof using tsi.
unfold logs_sorted_host.
intros.
find_apply_lem_hyp handleClientRequest_log.
intuition.
+
repeat find_rewrite.
eauto.
+
find_apply_lem_hyp no_entries_past_current_term_invariant.
break_exists; intuition; repeat find_rewrite.
simpl.
intuition eauto.
*
find_eapply_lem_hyp maxIndex_is_max; eauto.
omega.
*
unfold no_entries_past_current_term, no_entries_past_current_term_host in *.
intuition.
simpl in *.
find_apply_hyp_hyp.
Admitted.

Theorem logs_sorted_client_request : raft_net_invariant_client_request logs_sorted.
Proof using tsi.
unfold raft_net_invariant_client_request.
unfold logs_sorted.
intuition.
-
unfold logs_sorted_host in *.
simpl in *.
intros.
find_higher_order_rewrite.
break_match; eauto.
subst.
eauto using handleClientRequest_logs_sorted.
-
find_apply_lem_hyp handleClientRequest_packets.
subst.
simpl in *.
eauto using logs_sorted_nw_packets_unchanged.
-
find_apply_lem_hyp handleClientRequest_packets.
subst.
simpl in *.
eauto using packets_gt_prevIndex_packets_unchanged.
-
find_apply_lem_hyp handleClientRequest_packets.
subst.
simpl in *.
Admitted.

Theorem handleTimeout_log : forall h st out st' ps, handleTimeout h st = (out, st', ps) -> log st' = log st.
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Theorem logs_sorted_nw_only_new_packets_matter : forall net ps' l st', logs_sorted_nw net -> (forall p, In p ps' -> In p (nwPackets net) \/ In p l) -> logs_sorted_nw (mkNetwork l st') -> logs_sorted_nw (mkNetwork ps' st').
Proof using.
unfold logs_sorted_nw.
intros.
simpl in *.
find_apply_hyp_hyp.
Admitted.

Theorem logs_sorted_nw_no_append_entries : forall net ps' l st', logs_sorted_nw net -> (forall p, In p ps' -> In p (nwPackets net) \/ In p l) -> (forall p, In p l -> ~ is_append_entries (pBody p)) -> logs_sorted_nw (mkNetwork ps' st').
Proof using.
intros.
eapply logs_sorted_nw_only_new_packets_matter; eauto.
unfold logs_sorted_nw.
intros.
simpl in *.
find_apply_hyp_hyp.
exfalso.
match goal with H : _ |- _ => apply H end.
Admitted.

Theorem logs_sorted_nw_not_append_entries : forall net ps' p' st', logs_sorted_nw net -> (forall p, In p ps' -> In p (nwPackets net) \/ p = p') -> ~ is_append_entries (pBody p') -> logs_sorted_nw (mkNetwork ps' st').
Proof using.
intros.
unfold logs_sorted_nw.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
-
unfold logs_sorted_nw in *.
eauto.
-
subst.
exfalso.
match goal with H : _ |- _ => apply H end.
Admitted.

Theorem packets_gt_prevIndex_only_new_packets_matter : forall net ps' l st', packets_gt_prevIndex net -> (forall p, In p ps' -> In p (nwPackets net) \/ In p l) -> packets_gt_prevIndex (mkNetwork l st') -> packets_gt_prevIndex (mkNetwork ps' st').
Proof using.
unfold packets_gt_prevIndex.
intros.
simpl in *.
find_apply_hyp_hyp.
Admitted.

Theorem packets_gt_prevIndex_no_append_entries : forall net ps' l st', packets_gt_prevIndex net -> (forall p, In p ps' -> In p (nwPackets net) \/ In p l) -> (forall p, In p l -> ~ is_append_entries (pBody p)) -> packets_gt_prevIndex (mkNetwork ps' st').
Proof using.
intros.
eapply packets_gt_prevIndex_only_new_packets_matter; eauto.
unfold packets_gt_prevIndex.
intros.
simpl in *.
find_apply_hyp_hyp.
exfalso.
match goal with H : _ |- _ => apply H end.
Admitted.

Theorem packets_ge_prevTerm_only_new_packets_matter : forall net ps' l st', packets_ge_prevTerm net -> (forall p, In p ps' -> In p (nwPackets net) \/ In p l) -> packets_ge_prevTerm (mkNetwork l st') -> packets_ge_prevTerm (mkNetwork ps' st').
Proof using.
unfold packets_ge_prevTerm.
intros.
simpl in *.
find_apply_hyp_hyp.
Admitted.

Theorem packets_ge_prevTerm_no_append_entries : forall net ps' l st', packets_ge_prevTerm net -> (forall p, In p ps' -> In p (nwPackets net) \/ In p l) -> (forall p, In p l -> ~ is_append_entries (pBody p)) -> packets_ge_prevTerm (mkNetwork ps' st').
Proof using.
intros.
eapply packets_ge_prevTerm_only_new_packets_matter; eauto.
unfold packets_ge_prevTerm.
intros.
simpl in *.
find_apply_hyp_hyp.
exfalso.
match goal with H : _ |- _ => apply H end.
Admitted.

Theorem packets_ge_prevTerm_not_append_entries : forall net ps' p' st', packets_ge_prevTerm net -> (forall p, In p ps' -> In p (nwPackets net) \/ p = p') -> ~ is_append_entries (pBody p') -> packets_ge_prevTerm (mkNetwork ps' st').
Proof using.
intros.
unfold packets_ge_prevTerm.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
-
unfold packets_ge_prevTerm in *.
eauto.
-
subst.
exfalso.
match goal with H : _ |- _ => apply H end.
Admitted.

Theorem handleTimeout_not_is_append_entries : forall h st st' ps p, handleTimeout h st = (st', ps) -> In p (send_packets h ps) -> ~ is_append_entries (pBody p).
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Theorem logs_sorted_timeout : raft_net_invariant_timeout logs_sorted.
Proof using.
unfold raft_net_invariant_timeout.
unfold logs_sorted.
intuition.
-
unfold logs_sorted_host in *.
simpl in *.
intros.
find_apply_lem_hyp handleTimeout_log.
find_higher_order_rewrite.
break_match; repeat find_rewrite; eauto.
-
eapply logs_sorted_nw_no_append_entries; eauto.
intros.
eauto using handleTimeout_not_is_append_entries.
-
eapply packets_gt_prevIndex_no_append_entries; eauto.
intros.
eauto using handleTimeout_not_is_append_entries.
-
eapply packets_ge_prevTerm_no_append_entries; eauto.
intros.
Admitted.

Theorem sorted_append : forall l l', sorted l -> sorted l' -> (forall e e', In e l -> In e' l' -> eIndex e > eIndex e') -> (forall e e', In e l -> In e' l' -> eTerm e >= eTerm e') -> sorted (l ++ l').
Proof using.
induction l; intros; simpl in *; auto.
Admitted.

Theorem sorted_index_term : forall l e e', eIndex e <= eIndex e' -> sorted l -> In e l -> In e' l -> eTerm e <= eTerm e'.
Proof using.
induction l; intros; simpl in *; intuition.
-
subst_max.
intuition.
-
subst.
find_apply_hyp_hyp.
intuition.
-
subst.
find_apply_hyp_hyp.
Admitted.

Lemma handleAppendEntries_logs_sorted : forall net p t n pli plt es ci st' m, raft_intermediate_reachable net -> logs_sorted net -> handleAppendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci = (st', m) -> pBody p = AppendEntries t n pli plt es ci -> In p (nwPackets net) -> sorted (log st').
Proof using.
intros.
unfold logs_sorted in *.
intuition.
find_apply_lem_hyp handleAppendEntries_log.
intuition.
-
find_rewrite; eauto.
-
subst.
unfold logs_sorted_nw in *.
simpl in *.
find_eapply_hyp_goal; eauto.
-
find_rewrite.
apply sorted_append; eauto using removeAfterIndex_sorted.
+
intros.
find_apply_lem_hyp removeAfterIndex_In_le; eauto.
unfold packets_gt_prevIndex in *.
eapply gt_le_trans; [|eauto].
find_eapply_hyp_goal; [in_crush|eauto|eauto].
simpl in *.
eauto.
+
intros.
find_copy_apply_lem_hyp removeAfterIndex_In_le; eauto.
find_apply_lem_hyp removeAfterIndex_in.
break_exists.
intuition.
subst.
match goal with | H : eIndex ?x <= eIndex ?x', _ : In ?x ?ll |- _ => apply sorted_index_term with (l := ll) (e := x) (e' := x') in H end; eauto.
match goal with |- ?a >= ?b => cut (b <= a); [omega|] end.
eapply le_trans; eauto.
unfold packets_ge_prevTerm in *.
Admitted.

Theorem logs_sorted_append_entries : raft_net_invariant_append_entries logs_sorted.
Proof using.
unfold raft_net_invariant_append_entries.
intros.
unfold logs_sorted.
intuition.
-
unfold logs_sorted_host.
simpl in *.
intros.
repeat find_higher_order_rewrite.
break_match; repeat find_rewrite; eauto; [|unfold logs_sorted in *; intuition eauto].
subst.
eauto using handleAppendEntries_logs_sorted.
-
unfold logs_sorted in *.
intuition.
simpl in *.
eapply logs_sorted_nw_not_append_entries; eauto.
+
intros.
find_apply_hyp_hyp.
intuition eauto.
+
simpl.
eauto using handleAppendEntries_not_append_entries.
-
unfold logs_sorted in *.
intuition.
simpl in *.
eapply packets_gt_prevIndex_not_append_entries; eauto.
+
intros.
find_apply_hyp_hyp.
intuition eauto.
+
simpl.
eauto using handleAppendEntries_not_append_entries.
-
unfold logs_sorted in *.
intuition.
simpl in *.
eapply packets_ge_prevTerm_not_append_entries; eauto.
+
intros.
find_apply_hyp_hyp.
intuition eauto.
+
simpl.
Admitted.

Lemma handleAppendEntriesReply_log : forall h st from t es s st' ps, handleAppendEntriesReply h st from t es s = (st', ps) -> log st' = log st.
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Theorem packets_gt_prevIndex_not_append_entries : forall net ps' p' st', packets_gt_prevIndex net -> (forall p, In p ps' -> In p (nwPackets net) \/ p = p') -> ~ is_append_entries (pBody p') -> packets_gt_prevIndex (mkNetwork ps' st').
Proof using.
intros.
unfold packets_gt_prevIndex.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
-
unfold packets_gt_prevIndex in *.
eauto.
-
subst.
exfalso.
match goal with H : _ |- _ => apply H end.
repeat eexists; eauto.
