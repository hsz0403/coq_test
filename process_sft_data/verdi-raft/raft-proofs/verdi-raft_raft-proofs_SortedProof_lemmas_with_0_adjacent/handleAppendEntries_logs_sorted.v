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
find_eapply_hyp_goal; [in_crush|eauto|eauto]; simpl in *; eauto.
