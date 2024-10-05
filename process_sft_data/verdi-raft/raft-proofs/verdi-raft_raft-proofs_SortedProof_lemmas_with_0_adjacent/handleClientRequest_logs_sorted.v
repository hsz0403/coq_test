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
omega.
