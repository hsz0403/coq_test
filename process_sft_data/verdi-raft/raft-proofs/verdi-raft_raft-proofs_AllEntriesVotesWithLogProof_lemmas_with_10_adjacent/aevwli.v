Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.AllEntriesVotesWithLogInterface.
Require Import VerdiRaft.AllEntriesLogInterface.
Require Import VerdiRaft.VotesWithLogTermSanityInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.VotesVotesWithLogCorrespondInterface.
Section AllEntriesVotesWithLog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {aeli : allEntries_log_interface}.
Context {vwltsi : votesWithLog_term_sanity_interface}.
Context {vvwlci : votes_votesWithLog_correspond_interface}.
Context {vci : votes_correct_interface}.
Definition currentTerm_votedFor_votesWithLog net := forall h t n, (currentTerm (snd (nwState net h)) = t /\ votedFor (snd (nwState net h)) = Some n) -> exists l, In (t, n, l) (votesWithLog (fst (nwState net h))).
Instance aevwli : allEntries_votesWithLog_interface.
split.
eauto using allEntries_votesWithLog_invariant.
Defined.
End AllEntriesVotesWithLog.

Lemma update_elections_data_client_request_allEntries_in_or_term : forall h st client id c out st' ms t e, handleClientRequest h (snd st) client id c = (out, st', ms) -> In (t, e) (allEntries (update_elections_data_client_request h st client id c)) -> In (t, e) (allEntries (fst st)) \/ t = currentTerm (snd st).
Proof using.
intros.
intros.
unfold update_elections_data_client_request in *.
repeat break_match; repeat find_inversion; auto.
simpl in *.
intuition.
find_inversion.
repeat find_rewrite.
intuition.
unfold handleClientRequest in *.
Admitted.

Lemma allEntries_votesWithLog_client_request : refined_raft_net_invariant_client_request allEntries_votesWithLog.
Proof using vwltsi.
red.
unfold allEntries_votesWithLog.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *.
-
find_copy_eapply_lem_hyp update_elections_data_client_request_allEntries_in_or_term; eauto.
intuition.
+
repeat find_rewrite.
find_eapply_lem_hyp votesWithLog_update_elections_data_client_request; eauto.
eapply_prop_hyp votesWithLog votesWithLog; eauto; intuition; right; break_exists_exists; intuition; find_higher_order_rewrite; destruct_update; simpl in *; auto.
rewrite update_elections_data_client_request_leaderLogs.
auto.
+
subst.
find_eapply_lem_hyp votesWithLog_update_elections_data_client_request; eauto.
find_eapply_lem_hyp votesWithLog_term_sanity_invariant; eauto.
repeat (unfold raft_data, ghost_data in *; simpl in *).
omega.
-
eapply_prop_hyp votesWithLog votesWithLog; eauto; intuition; right; break_exists_exists; intuition; find_higher_order_rewrite; destruct_update; simpl in *; auto.
rewrite update_elections_data_client_request_leaderLogs.
Admitted.

Lemma votesWithLog_update_elections_data_timeout' : forall net h out st' ps t' h' l', refined_raft_intermediate_reachable net -> handleTimeout h (snd (nwState net h)) = (out, st', ps) -> In (t', h', l') (votesWithLog (update_elections_data_timeout h (nwState net h))) -> In (t', h', l') (votesWithLog (fst (nwState net h))) \/ (t' = currentTerm st' /\ l' = log st' /\ currentTerm (snd (nwState net h)) < currentTerm st').
Proof using.
unfold update_elections_data_timeout.
intros.
repeat break_match; simpl in *; intuition; repeat tuple_inversion; intuition.
-
unfold handleTimeout, tryToBecomeLeader in *.
repeat break_match; repeat find_inversion; simpl in *; intuition.
-
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Lemma allEntries_votesWithLog_timeout : refined_raft_net_invariant_timeout allEntries_votesWithLog.
Proof using aeli.
red.
unfold allEntries_votesWithLog.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *.
-
find_rewrite_lem update_elections_data_timeout_allEntries.
find_eapply_lem_hyp votesWithLog_update_elections_data_timeout'; eauto.
intuition.
+
eapply_prop_hyp votesWithLog votesWithLog; eauto; intuition; right; break_exists_exists; intuition; find_higher_order_rewrite; destruct_update; simpl in *; auto.
rewrite update_elections_data_timeout_leaderLogs.
auto.
+
subst.
find_copy_apply_lem_hyp handleTimeout_log_same.
repeat find_rewrite.
find_apply_lem_hyp allEntries_log_invariant; eauto.
intuition.
right.
break_exists_exists; intuition; find_higher_order_rewrite; destruct_update; simpl in *; auto; rewrite update_elections_data_timeout_leaderLogs; auto.
-
eapply_prop_hyp votesWithLog votesWithLog; eauto; intuition; right; break_exists_exists; intuition; find_higher_order_rewrite; destruct_update; simpl in *; auto.
Admitted.

Lemma allEntries_votesWithLog_do_leader : refined_raft_net_invariant_do_leader allEntries_votesWithLog.
Proof using.
red.
unfold allEntries_votesWithLog.
intros.
simpl in *.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
repeat find_higher_order_rewrite.
Admitted.

Lemma allEntries_votesWithLog_do_generic_server : refined_raft_net_invariant_do_generic_server allEntries_votesWithLog.
Proof using.
red.
unfold allEntries_votesWithLog.
intros.
simpl in *.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
repeat find_higher_order_rewrite.
Admitted.

Lemma allEntries_votesWithLog_init : refined_raft_net_invariant_init allEntries_votesWithLog.
Proof using.
red.
unfold allEntries_votesWithLog.
intros.
simpl in *.
Admitted.

Lemma allEntries_votesWithLog_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset allEntries_votesWithLog.
Proof using.
red.
unfold allEntries_votesWithLog in *.
intros.
repeat find_reverse_higher_order_rewrite.
copy_eapply_prop_hyp votesWithLog votesWithLog; eauto.
intuition.
right.
break_exists_exists.
repeat find_higher_order_rewrite.
Admitted.

Lemma allEntries_votesWithLog_reboot : refined_raft_net_invariant_reboot allEntries_votesWithLog.
Proof using.
red.
unfold allEntries_votesWithLog in *.
intros.
simpl in *.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
repeat find_higher_order_rewrite.
subst.
unfold reboot in *.
Admitted.

Theorem allEntries_votesWithLog_invariant : forall net, refined_raft_intermediate_reachable net -> allEntries_votesWithLog net.
Proof using vwltsi aeli rri.
intros.
eapply refined_raft_net_invariant; eauto.
-
exact allEntries_votesWithLog_init.
-
exact allEntries_votesWithLog_client_request.
-
exact allEntries_votesWithLog_timeout.
-
exact allEntries_votesWithLog_append_entries.
-
exact allEntries_votesWithLog_append_entries_reply.
-
exact allEntries_votesWithLog_request_vote.
-
exact allEntries_votesWithLog_request_vote_reply.
-
exact allEntries_votesWithLog_do_leader.
-
exact allEntries_votesWithLog_do_generic_server.
-
exact allEntries_votesWithLog_state_same_packet_subset.
-
Admitted.

Instance aevwli : allEntries_votesWithLog_interface.
split.
eauto using allEntries_votesWithLog_invariant.
