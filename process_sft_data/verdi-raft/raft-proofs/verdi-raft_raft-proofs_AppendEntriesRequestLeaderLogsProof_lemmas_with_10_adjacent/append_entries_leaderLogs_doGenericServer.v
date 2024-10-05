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

Lemma update_elections_data_timeout_leaderLogs : forall h st, leaderLogs (update_elections_data_timeout h st) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_timeout.
intros.
Admitted.

Lemma update_elections_data_appendEntries_leaderLogs : forall h st t h' pli plt es ci, leaderLogs (update_elections_data_appendEntries h st t h' pli plt es ci) = leaderLogs (fst st).
Proof using.
intros.
unfold update_elections_data_appendEntries.
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

Lemma lift_nextIndex_safety : forall net, refined_raft_intermediate_reachable net -> nextIndex_safety (deghost net).
Proof using nisi rri.
intros.
Admitted.

Lemma nextIndex_sanity : forall net h h', refined_raft_intermediate_reachable net -> type (snd (nwState net h)) = Leader -> pred (getNextIndex (snd (nwState net h)) h') <> 0 -> exists e, findAtIndex (log (snd (nwState net h))) (pred (getNextIndex (snd (nwState net h)) h')) = Some e.
Proof using nisi lmi si rri.
intros.
find_copy_apply_lem_hyp lift_log_matching.
find_copy_apply_lem_hyp lift_nextIndex_safety.
assert (pred (getNextIndex (snd (nwState net h)) h') > 0) by omega.
unfold log_matching, log_matching_hosts in *.
unfold nextIndex_safety in *.
match goal with | H : forall _ _, type _ = _ -> _ |- _ => specialize (H h h') end.
intuition.
match goal with | H : forall _ _, _ <= _ <= _ -> _ |- _ => specialize (H h (pred (getNextIndex (snd (nwState net h)) h'))) end.
unfold raft_refined_base_params in *.
repeat find_rewrite_lem deghost_spec.
intuition.
break_exists_exists.
intuition.
Admitted.

Lemma sorted_findGtIndex_0 : forall l, (forall e, In e l -> eIndex e > 0) -> sorted l -> findGtIndex l 0 = l.
Proof using.
induction l; intros; simpl in *; intuition.
break_if; intuition.
-
f_equal.
auto.
-
do_bool.
Admitted.

Lemma entries_gt_0 : forall net h e, refined_raft_intermediate_reachable net -> In e (log (snd (nwState net h))) -> eIndex e > 0.
Proof using lmi rri.
intros.
find_apply_lem_hyp lift_log_matching.
unfold log_matching, log_matching_hosts in *.
intuition.
unfold raft_refined_base_params in *.
match goal with | H : In _ _ |- _ => rewrite <- deghost_spec in H end.
Admitted.

Lemma Prefix_refl : forall A (l : list A), Prefix l l.
Proof using.
intros.
Admitted.

Lemma findGtIndex_app_in_1 : forall l1 l2 e, sorted (l1 ++ l2) -> In e l1 -> exists l', findGtIndex (l1 ++ l2) (eIndex e) = l' /\ forall x, In x l' -> In x l1.
Proof using.
induction l1; intros; simpl in *; intuition.
-
subst.
break_if; do_bool; try omega.
eexists; repeat (simpl in *; intuition).
-
specialize (H1 e); intuition.
conclude H1 ltac:(apply in_app_iff; intuition).
break_if; do_bool; try omega.
eexists; intuition; eauto.
simpl in *.
intuition.
eapply_prop_hyp sorted sorted; eauto.
break_exists; intuition.
find_rewrite.
Admitted.

Lemma sorted_app_in_1 : forall l1 l2 e, sorted (l1 ++ l2) -> eIndex e > 0 -> In e l1 -> eIndex e > maxIndex l2.
Proof using.
induction l1; intros; simpl in *; intuition.
subst.
destruct l2; simpl in *; auto.
Admitted.

Lemma findGtIndex_Prefix : forall l i, Prefix (findGtIndex l i) l.
Proof using.
induction l; intros; simpl in *; intuition.
Admitted.

Lemma findGtIndex_app_in_2 : forall l1 l2 e, sorted (l1 ++ l2) -> In e l2 -> exists l', findGtIndex (l1 ++ l2) (eIndex e) = l1 ++ l' /\ Prefix l' l2.
Proof using.
induction l1; intros; simpl in *; intuition.
-
eexists; intuition eauto using findGtIndex_Prefix.
-
break_if; simpl in *; intuition.
+
eapply_prop_hyp sorted sorted; eauto.
break_exists; intuition; find_rewrite; eauto.
+
do_bool.
specialize (H1 e); conclude H1 ltac:(apply in_app_iff; intuition).
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
unfold doGenericServer in *; repeat break_match; find_inversion; do_in_map; simpl in *; intuition; subst; simpl in *; do_in_map; subst; simpl in *; congruence.
