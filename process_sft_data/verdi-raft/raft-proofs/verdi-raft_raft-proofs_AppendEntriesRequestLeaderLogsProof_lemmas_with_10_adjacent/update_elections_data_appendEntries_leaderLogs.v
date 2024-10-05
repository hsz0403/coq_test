Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Require Import VerdiRaft.NextIndexSafetyInterface.
Section AppendEntriesRequestLeaderLogs.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
Context {rri : raft_refinement_interface}.
Context {si : sorted_interface}.
Context {lmi : log_matching_interface}.
Context {nisi : nextIndex_safety_interface}.
Ltac start := red; unfold append_entries_leaderLogs; intros; subst; simpl in *; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *.
Ltac prove_in := match goal with | [ _ : nwPackets ?net = _, _ : In (?p : packet) _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition) | [ _ : nwPackets ?net = _, _ : pBody ?p = _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; intuition) end.
Instance aerlli : append_entries_leaderLogs_interface.
split.
exact append_entries_leaderLogs_invariant.
End AppendEntriesRequestLeaderLogs.

Theorem lift_sorted : forall net, refined_raft_intermediate_reachable net -> logs_sorted (deghost net).
Proof using si rri.
intros.
Admitted.

Theorem lift_logs_sorted : forall net h, refined_raft_intermediate_reachable net -> sorted (log (snd (nwState net h))).
Proof using si rri.
intros.
find_apply_lem_hyp lift_sorted.
unfold logs_sorted, logs_sorted_host in *.
intuition.
unfold deghost in *.
simpl in *.
Admitted.

Theorem lift_log_matching : forall net, refined_raft_intermediate_reachable net -> log_matching (deghost net).
Proof using lmi rri.
intros.
Admitted.

Lemma update_elections_data_client_request_leaderLogs : forall h st client id c, leaderLogs (update_elections_data_client_request h st client id c) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_client_request in *.
intros.
Admitted.

Lemma update_elections_data_timeout_leaderLogs : forall h st, leaderLogs (update_elections_data_timeout h st) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_timeout.
intros.
Admitted.

Lemma update_elections_data_requestVote_leaderLogs : forall h h' t lli llt st, leaderLogs (update_elections_data_requestVote h h' t h' lli llt st) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_requestVote.
intros.
Admitted.

Lemma update_elections_data_requestVoteReply_leaderLogs : forall h h' t st t' ll' r, In (t', ll') (leaderLogs (fst st)) -> In (t', ll') (leaderLogs (update_elections_data_requestVoteReply h h' t r st)).
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
repeat break_match; auto.
simpl in *.
Admitted.

Lemma append_entries_leaderLogs_appendEntries : refined_raft_net_invariant_append_entries append_entries_leaderLogs.
Proof using.
red.
unfold append_entries_leaderLogs.
intros.
subst.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
-
prove_in.
eapply_prop_hyp In In; break_exists.
intuition; eauto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto; rewrite update_elections_data_appendEntries_leaderLogs; eauto; subst; auto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto; rewrite update_elections_data_appendEntries_leaderLogs; eauto; subst; auto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto; rewrite update_elections_data_appendEntries_leaderLogs; eauto; subst; auto.
+
eauto.
-
subst.
simpl in *.
unfold handleAppendEntries in *.
Admitted.

Lemma append_entries_leaderLogs_appendEntriesReply : refined_raft_net_invariant_append_entries_reply append_entries_leaderLogs.
Proof using.
red.
unfold append_entries_leaderLogs.
intros.
subst.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
-
prove_in.
eapply_prop_hyp In In; break_exists.
intuition; eauto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto; subst; auto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto; subst; auto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto; subst; auto.
+
eauto.
-
do_in_map.
subst.
simpl in *.
unfold handleAppendEntriesReply in *.
Admitted.

Lemma append_entries_leaderLogs_requestVote : refined_raft_net_invariant_request_vote append_entries_leaderLogs.
Proof using.
red.
unfold append_entries_leaderLogs.
intros.
subst.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
-
prove_in.
eapply_prop_hyp In In; break_exists.
intuition; eauto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto; rewrite update_elections_data_requestVote_leaderLogs; eauto; subst; auto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto; rewrite update_elections_data_requestVote_leaderLogs; eauto; subst; auto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto; rewrite update_elections_data_requestVote_leaderLogs; eauto; subst; auto.
+
eauto.
-
subst.
simpl in *.
unfold handleRequestVote in *.
Admitted.

Lemma append_entries_leaderLogs_requestVoteReply : refined_raft_net_invariant_request_vote_reply append_entries_leaderLogs.
Proof using.
red.
unfold append_entries_leaderLogs.
intros.
subst.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
-
prove_in.
eapply_prop_hyp In In; break_exists.
intuition; eauto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto.
subst; auto using update_elections_data_requestVoteReply_leaderLogs.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto.
subst; auto using update_elections_data_requestVoteReply_leaderLogs.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto.
subst; auto using update_elections_data_requestVoteReply_leaderLogs.
+
Admitted.

Lemma append_entries_leaderLogs_clientRequest : refined_raft_net_invariant_client_request append_entries_leaderLogs.
Proof using.
red.
unfold append_entries_leaderLogs.
intros.
subst.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
-
eapply_prop_hyp In In; break_exists.
intuition; eauto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto.
subst.
rewrite update_elections_data_client_request_leaderLogs.
eauto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto.
subst.
rewrite update_elections_data_client_request_leaderLogs.
eauto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto.
subst.
rewrite update_elections_data_client_request_leaderLogs.
eauto.
+
eauto.
-
subst.
simpl in *.
unfold handleClientRequest in *.
Admitted.

Lemma append_entries_leaderLogs_timeout : refined_raft_net_invariant_timeout append_entries_leaderLogs.
Proof using.
red.
unfold append_entries_leaderLogs.
intros.
subst.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
-
eapply_prop_hyp In In; break_exists.
intuition; eauto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto.
subst.
rewrite update_elections_data_timeout_leaderLogs.
eauto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto.
subst.
rewrite update_elections_data_timeout_leaderLogs.
eauto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto.
subst.
rewrite update_elections_data_timeout_leaderLogs.
eauto.
+
eauto.
-
subst.
simpl in *.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Lemma append_entries_leaderLogs_doGenericServer : refined_raft_net_invariant_do_generic_server append_entries_leaderLogs.
Proof using.
red.
unfold append_entries_leaderLogs.
intros.
subst.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
-
eapply_prop_hyp In In; break_exists.
intuition; eauto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto.
subst.
replace gd with (fst (nwState net x)); eauto; repeat find_rewrite; reflexivity.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto.
subst.
replace gd with (fst (nwState net x)); eauto; repeat find_rewrite; reflexivity.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto.
subst.
replace gd with (fst (nwState net x)); eauto; repeat find_rewrite; reflexivity.
+
eauto.
-
Admitted.

Lemma doLeader_spec : forall st h os st' ms m t n pli plt es ci, doLeader st h = (os, st', ms) -> In m ms -> snd m = AppendEntries t n pli plt es ci -> t = currentTerm st /\ log st' = log st /\ type st = Leader /\ ((pli = 0 /\ plt = 0 /\ es = findGtIndex (log st) 0) \/ ((exists e, findAtIndex (log st) pli = Some e /\ eTerm e = plt) /\ es = findGtIndex (log st) pli) \/ exists h', pred (getNextIndex st h') <> 0 /\ findAtIndex (log st) (pred (getNextIndex st h')) = None).
Proof using.
intros.
unfold doLeader, advanceCommitIndex in *.
break_match; try solve [find_inversion; simpl in *; intuition].
break_if; try solve [find_inversion; simpl in *; intuition].
find_inversion.
simpl.
do_in_map.
subst.
simpl in *.
find_inversion.
intuition.
match goal with | |- context [pred ?x] => remember (pred x) as index end.
break_match; simpl in *.
-
right.
left.
eauto.
-
destruct index; intuition.
right.
right.
exists x.
match goal with | _ : S _ = pred ?x |- context [pred ?y] => assert (pred x = pred y) by auto end.
repeat find_rewrite.
Admitted.

Lemma update_elections_data_appendEntries_leaderLogs : forall h st t h' pli plt es ci, leaderLogs (update_elections_data_appendEntries h st t h' pli plt es ci) = leaderLogs (fst st).
Proof using.
intros.
unfold update_elections_data_appendEntries.
repeat break_match; subst; simpl in *; auto.
