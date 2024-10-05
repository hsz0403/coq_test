Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.AppendEntriesReplySublogInterface.
Require Import VerdiRaft.MatchIndexSanityInterface.
Require Import VerdiRaft.SortedInterface.
Section MatchIndexSanity.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {aersi : append_entries_reply_sublog_interface}.
Context {si : sorted_interface}.
Instance matchisi : match_index_sanity_interface.
Proof.
split.
exact match_index_sanity_invariant.
End MatchIndexSanity.

Lemma match_index_sanity_client_request : raft_net_invariant_client_request match_index_sanity.
Proof using.
unfold raft_net_invariant_client_request, match_index_sanity.
simpl.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
-
find_copy_apply_lem_hyp handleClientRequest_type.
find_copy_apply_lem_hyp handleClientRequest_matchIndex.
intuition.
+
repeat find_rewrite.
auto.
+
repeat find_rewrite.
destruct (name_eq_dec h0 leader).
*
subst.
rewrite get_set_same_default.
auto.
*
rewrite get_set_diff_default by auto.
eauto using le_trans.
-
auto.
