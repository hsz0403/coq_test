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

Lemma match_index_sanity_request_vote_reply : raft_net_invariant_request_vote_reply match_index_sanity.
Proof using.
unfold raft_net_invariant_request_vote_reply, match_index_sanity.
simpl.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
-
pose proof handleRequestVoteReply_matchIndex (pDst p) (nwState net (pDst p)) (pSrc p) t v.
erewrite handleRequestVoteReply_log by eauto.
intuition.
+
repeat find_rewrite.
auto.
+
repeat find_rewrite.
destruct (name_eq_dec h (pDst p)).
*
subst.
rewrite get_set_same_default.
auto.
*
rewrite get_set_diff_default by auto.
unfold assoc_default.
simpl.
omega.
-
auto.
