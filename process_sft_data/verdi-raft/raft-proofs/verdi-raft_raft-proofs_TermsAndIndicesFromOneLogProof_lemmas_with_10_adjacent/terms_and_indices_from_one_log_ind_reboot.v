Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.TermsAndIndicesFromOneLogInterface.
Require Import VerdiRaft.CurrentTermGtZeroInterface.
Section TermsAndIndicesFromOneLog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {ctgzi : current_term_gt_zero_interface}.
Definition terms_and_indices_from_one_log_ind (net : network) : Prop := terms_and_indices_from_one_log net /\ terms_and_indices_from_one_log_nw net.
Instance taifoli : terms_and_indices_from_one_log_interface.
Proof.
split.
-
apply terms_and_indices_from_one_log_ind_invariant.
-
apply terms_and_indices_from_one_log_ind_invariant.
End TermsAndIndicesFromOneLog.

Lemma terms_and_indices_from_one_log_ind_timeout : raft_net_invariant_timeout terms_and_indices_from_one_log_ind.
Proof using.
red.
unfold terms_and_indices_from_one_log_ind.
split; red; simpl in *; intuition.
-
find_higher_order_rewrite.
update_destruct; subst; rewrite_update; auto.
find_apply_lem_hyp handleTimeout_log_same.
find_rewrite.
auto.
-
Admitted.

Lemma terms_and_indices_from_one_app : forall xs ys, terms_and_indices_from_one xs -> terms_and_indices_from_one ys -> terms_and_indices_from_one (xs ++ ys).
Proof using.
induction xs.
-
auto.
-
unfold terms_and_indices_from_one in *.
simpl.
intros.
Admitted.

Lemma terms_and_indices_from_one_In : forall (xs ys : list entry), (forall x, In x xs -> In x ys) -> terms_and_indices_from_one ys -> terms_and_indices_from_one xs.
Proof using.
unfold terms_and_indices_from_one.
Admitted.

Lemma terms_and_indices_from_one_log_ind_append_entries : raft_net_invariant_append_entries terms_and_indices_from_one_log_ind.
Proof using.
red.
unfold terms_and_indices_from_one_log_ind.
split; red; simpl in *; intuition.
-
find_higher_order_rewrite.
update_destruct; subst; rewrite_update; auto.
find_apply_lem_hyp handleAppendEntries_log.
intuition.
+
find_rewrite.
auto.
+
subst.
unfold terms_and_indices_from_one_log_nw in *.
eauto.
+
break_exists.
intuition.
subst.
find_rewrite.
apply terms_and_indices_from_one_app.
*
eauto.
*
eapply terms_and_indices_from_one_In; [eapply removeAfterIndex_in | eauto].
-
unfold terms_and_indices_from_one_log_nw in *.
find_apply_hyp_hyp.
intuition; eauto.
find_apply_lem_hyp handleAppendEntries_not_append_entries.
exfalso.
apply H.
repeat eexists.
subst.
Admitted.

Lemma terms_and_indices_from_one_log_ind_append_entries_reply : raft_net_invariant_append_entries_reply terms_and_indices_from_one_log_ind.
Proof using.
red.
unfold terms_and_indices_from_one_log_ind.
split; red; simpl in *; intuition.
-
find_higher_order_rewrite.
update_destruct; subst; rewrite_update; auto.
find_apply_lem_hyp handleAppendEntriesReply_log.
find_rewrite.
auto.
-
find_apply_hyp_hyp.
intuition; eauto.
do_in_map.
find_apply_lem_hyp handleAppendEntriesReply_packets; eauto.
subst.
Admitted.

Lemma terms_and_indices_from_one_log_ind_request_vote : raft_net_invariant_request_vote terms_and_indices_from_one_log_ind.
Proof using.
red.
unfold terms_and_indices_from_one_log_ind.
split; red; simpl in *; intuition.
-
find_higher_order_rewrite.
update_destruct; subst; rewrite_update; auto.
find_apply_lem_hyp handleRequestVote_log.
find_rewrite.
auto.
-
find_apply_hyp_hyp.
intuition; eauto.
find_apply_lem_hyp handleRequestVote_no_append_entries.
unfold not in *.
find_false.
repeat eexists.
subst.
Admitted.

Lemma terms_and_indices_from_one_log_ind_request_vote_reply : raft_net_invariant_request_vote_reply terms_and_indices_from_one_log_ind.
Proof using.
red.
unfold terms_and_indices_from_one_log_ind.
split; red; simpl in *; intuition.
-
find_higher_order_rewrite.
update_destruct; rewrite_update; auto.
find_apply_lem_hyp handleRequestVoteReply_log.
subst.
find_rewrite.
auto.
-
Admitted.

Lemma terms_and_indices_from_one_log_ind_do_leader : raft_net_invariant_do_leader terms_and_indices_from_one_log_ind.
Proof using.
red.
unfold terms_and_indices_from_one_log_ind.
split; red; simpl in *; intuition.
-
find_higher_order_rewrite.
update_destruct; subst; rewrite_update; auto.
find_apply_lem_hyp doLeader_log.
find_rewrite.
auto.
-
find_apply_hyp_hyp.
intuition; eauto.
unfold doLeader in *.
repeat break_match; tuple_inversion; subst; try contradiction.
repeat do_in_map.
unfold replicaMessage in *.
subst.
simpl in *.
find_inversion.
eapply terms_and_indices_from_one_In.
apply findGtIndex_in.
Admitted.

Lemma terms_and_indices_from_one_log_ind_do_generic_server : raft_net_invariant_do_generic_server terms_and_indices_from_one_log_ind.
Proof using.
red.
unfold terms_and_indices_from_one_log_ind.
split; red; simpl in *; intuition.
-
find_higher_order_rewrite.
update_destruct; subst; rewrite_update; auto.
find_apply_lem_hyp doGenericServer_log.
find_rewrite.
auto.
-
find_apply_lem_hyp doGenericServer_packets.
find_apply_hyp_hyp.
subst.
intuition; eauto.
do_in_map.
Admitted.

Lemma terms_and_indices_from_one_log_ind_state_same_packet_subset : raft_net_invariant_state_same_packet_subset terms_and_indices_from_one_log_ind.
Proof using.
red.
unfold terms_and_indices_from_one_log_ind.
split; red; simpl in *; intuition.
-
find_reverse_higher_order_rewrite.
auto.
-
Admitted.

Lemma terms_and_indices_from_one_log_ind_invariant : forall net, raft_intermediate_reachable net -> terms_and_indices_from_one_log_ind net.
Proof using ctgzi.
intros.
apply raft_net_invariant; auto.
-
apply terms_and_indices_from_one_log_ind_init.
-
apply terms_and_indices_from_one_log_ind_client_request.
-
apply terms_and_indices_from_one_log_ind_timeout.
-
apply terms_and_indices_from_one_log_ind_append_entries.
-
apply terms_and_indices_from_one_log_ind_append_entries_reply.
-
apply terms_and_indices_from_one_log_ind_request_vote.
-
apply terms_and_indices_from_one_log_ind_request_vote_reply.
-
apply terms_and_indices_from_one_log_ind_do_leader.
-
apply terms_and_indices_from_one_log_ind_do_generic_server.
-
apply terms_and_indices_from_one_log_ind_state_same_packet_subset.
-
Admitted.

Instance taifoli : terms_and_indices_from_one_log_interface.
Proof.
split.
-
apply terms_and_indices_from_one_log_ind_invariant.
-
Admitted.

Lemma terms_and_indices_from_one_log_ind_reboot : raft_net_invariant_reboot terms_and_indices_from_one_log_ind.
Proof using.
red.
unfold terms_and_indices_from_one_log_ind.
split; red; simpl in *; intuition.
-
find_higher_order_rewrite.
update_destruct; subst; rewrite_update; auto.
unfold reboot.
eauto.
-
find_reverse_rewrite.
eauto.
