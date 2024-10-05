Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.VotesWithLogSortedInterface.
Require Import VerdiRaft.SortedInterface.
Section VotesWithLogSorted.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {si : sorted_interface}.
Instance vwlsi : votesWithLog_sorted_interface.
Proof.
split.
exact votesWithLog_sorted_invariant.
End VotesWithLogSorted.

Lemma votesWithLog_sorted_timeout : refined_raft_net_invariant_timeout votesWithLog_sorted.
Proof using si rri.
unfold refined_raft_net_invariant_timeout, votesWithLog_sorted.
intros.
subst.
simpl in *.
find_higher_order_rewrite.
update_destruct_simplify; simpl in *.
-
destruct (votesWithLog (update_elections_data_timeout h0 (nwState net h0))) using (votesWithLog_update_elections_data_timeout ltac:(eauto)).
+
simpl in *.
intuition.
*
find_inversion.
erewrite handleTimeout_log_same by eauto.
eauto using sorted_host_lifted.
*
eauto.
+
eauto.
-
Admitted.

Lemma votesWithLog_update_elections_data_AE : forall me st t li pli plt es lci, votesWithLog (update_elections_data_appendEntries me st t li pli plt es lci) = votesWithLog (fst st).
Proof using.
unfold update_elections_data_appendEntries.
intros.
Admitted.

Lemma votesWithLog_sorted_append_entries : refined_raft_net_invariant_append_entries votesWithLog_sorted.
Proof using.
unfold refined_raft_net_invariant_append_entries, votesWithLog_sorted.
intros.
subst.
simpl in *.
find_higher_order_rewrite.
update_destruct_simplify; simpl in *.
-
rewrite votesWithLog_update_elections_data_AE in *.
eauto.
-
Admitted.

Lemma votesWithLog_sorted_append_entries_reply : refined_raft_net_invariant_append_entries_reply votesWithLog_sorted.
Proof using.
unfold refined_raft_net_invariant_append_entries_reply, votesWithLog_sorted.
intros.
subst.
simpl in *.
find_higher_order_rewrite.
Admitted.

Lemma votesWithLog_sorted_request_vote : refined_raft_net_invariant_request_vote votesWithLog_sorted.
Proof using si rri.
unfold refined_raft_net_invariant_request_vote, votesWithLog_sorted.
intros.
subst.
simpl in *.
find_higher_order_rewrite.
update_destruct_simplify.
-
unfold update_elections_data_requestVote in *.
repeat break_match; simpl in *; intuition; repeat find_inversion; eauto; erewrite handleRequestVote_log; eauto using sorted_host_lifted.
-
Admitted.

Lemma votesWithLog_update_elections_data_RVR : forall me src t status st, votesWithLog (update_elections_data_requestVoteReply me src t status st) = votesWithLog (fst st).
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
Admitted.

Lemma votesWithLog_sorted_request_vote_reply : refined_raft_net_invariant_request_vote_reply votesWithLog_sorted.
Proof using.
unfold refined_raft_net_invariant_request_vote_reply, votesWithLog_sorted.
intros.
subst.
simpl in *.
find_higher_order_rewrite.
update_destruct_simplify.
-
rewrite votesWithLog_update_elections_data_RVR in *.
eauto.
-
Admitted.

Lemma votesWithLog_sorted_do_leader : refined_raft_net_invariant_do_leader votesWithLog_sorted.
Proof using.
unfold refined_raft_net_invariant_do_leader, votesWithLog_sorted.
intros.
subst.
simpl in *.
find_higher_order_rewrite.
update_destruct_simplify.
-
match goal with | [ H : _, H' : _ |- _ ] => eapply H; rewrite H'; simpl; eauto end.
-
Admitted.

Lemma votesWithLog_sorted_do_generic_server : refined_raft_net_invariant_do_generic_server votesWithLog_sorted.
Proof using.
unfold refined_raft_net_invariant_do_generic_server, votesWithLog_sorted.
intros.
subst.
simpl in *.
find_higher_order_rewrite.
update_destruct_simplify.
-
match goal with | [ H : _, H' : _ |- _ ] => eapply H; rewrite H'; simpl; eauto end.
-
Admitted.

Lemma votesWithLog_sorted_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset votesWithLog_sorted.
Proof using.
unfold refined_raft_net_invariant_state_same_packet_subset, votesWithLog_sorted.
intros.
subst.
simpl in *.
find_reverse_higher_order_rewrite.
Admitted.

Lemma votesWithLog_sorted_invariant : forall net, refined_raft_intermediate_reachable net -> votesWithLog_sorted net.
Proof using si rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply votesWithLog_sorted_init.
-
apply votesWithLog_sorted_client_request.
-
apply votesWithLog_sorted_timeout.
-
apply votesWithLog_sorted_append_entries.
-
apply votesWithLog_sorted_append_entries_reply.
-
apply votesWithLog_sorted_request_vote.
-
apply votesWithLog_sorted_request_vote_reply.
-
apply votesWithLog_sorted_do_leader.
-
apply votesWithLog_sorted_do_generic_server.
-
apply votesWithLog_sorted_state_same_packet_subset.
-
Admitted.

Instance vwlsi : votesWithLog_sorted_interface.
Proof.
split.
Admitted.

Lemma votesWithLog_sorted_reboot : refined_raft_net_invariant_reboot votesWithLog_sorted.
Proof using.
unfold refined_raft_net_invariant_reboot, votesWithLog_sorted.
intros.
find_higher_order_rewrite.
update_destruct_simplify.
-
match goal with | [ H : _, H' : _ |- _ ] => eapply H; rewrite H'; simpl; eauto end.
-
eauto.
