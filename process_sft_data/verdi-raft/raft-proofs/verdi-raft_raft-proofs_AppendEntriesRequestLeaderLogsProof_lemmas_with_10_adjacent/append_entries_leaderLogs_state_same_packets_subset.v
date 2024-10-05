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

Lemma findGtIndex_app_eq : forall l1 l2 e, sorted (l1 ++ l2) -> In e l2 -> findGtIndex (l1 ++ l2) (eIndex e) = l1 -> eIndex e = maxIndex l2.
Proof using.
induction l1; intros; simpl in *.
-
destruct l2; simpl in *; intuition; subst; auto.
break_if; try congruence.
do_bool.
find_apply_hyp_hyp.
intuition.
omega.
-
simpl in *.
break_if; try congruence.
do_bool.
find_inversion.
Admitted.

Lemma append_entries_leaderLogs_doLeader : refined_raft_net_invariant_do_leader append_entries_leaderLogs.
Proof using nisi lmi si rri lhllsi.
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
do_in_map.
subst.
assert (sorted (log (snd (nwState net h)))) by eauto using lift_logs_sorted.
assert (forall e, In e (log (snd (nwState net h))) -> eIndex e > 0) by eauto using entries_gt_0.
simpl in *.
find_eapply_lem_hyp doLeader_spec; [|eauto|eauto].
intuition.
+
subst.
match goal with | H : doLeader ?d ?h = _, H' : type ?d = _ |- _ => replace d with (snd (nwState net h)) in H by (repeat find_rewrite; reflexivity); replace d with (snd (nwState net h)) in H' by (repeat find_rewrite; reflexivity) end.
find_eapply_lem_hyp leaders_have_leaderLogs_strong_invariant; eauto.
exists h.
break_exists_exists.
repeat find_rewrite.
eexists; intuition eauto using Prefix_refl; auto.
*
simpl in *.
repeat find_rewrite.
eapply sorted_findGtIndex_0; eauto.
*
simpl in *.
repeat find_higher_order_rewrite.
rewrite_update.
eauto.
+
subst.
break_exists.
intuition.
find_apply_lem_hyp findAtIndex_elim.
intuition.
subst.
match goal with | H : doLeader ?d ?h = _, H' : type ?d = _, H'' : context [log ?d] |- _ => replace d with (snd (nwState net h)) in H by (repeat find_rewrite; reflexivity); replace d with (snd (nwState net h)) in H' by (repeat find_rewrite; reflexivity); replace d with (snd (nwState net h)) in H'' by (repeat find_rewrite; reflexivity); replace d with (snd (nwState net h)) by (repeat find_rewrite; reflexivity) end.
find_copy_apply_lem_hyp lift_log_matching.
unfold log_matching, log_matching_hosts in *.
intuition.
match goal with | H : forall _ _, In _ _ -> _ |- _ => specialize (H h x0); conclude H ltac:(unfold deghost in *; repeat (break_match; simpl in *); repeat (simpl in *; find_rewrite); auto) end.
find_eapply_lem_hyp leaders_have_leaderLogs_strong_invariant; eauto.
exists h.
break_exists.
intuition.
exists x1.
repeat (find_rewrite; simpl in *).
do_in_app.
intuition.
*
find_copy_eapply_lem_hyp findGtIndex_app_in_1; eauto.
break_exists_exists.
exists nil.
intuition; simpl in *; auto; eauto using sorted_app_in_1; [rewrite app_nil_r; auto|].
clear H18.
find_higher_order_rewrite.
rewrite_update.
simpl in *.
auto.
*
{
find_copy_eapply_lem_hyp findGtIndex_app_in_2; eauto.
exists x2.
break_exists_exists.
intuition; simpl in *; auto; intuition eauto.
-
clear H18.
find_higher_order_rewrite.
rewrite_update.
auto.
-
right.
left.
eexists; intuition; eauto.
match goal with | |- Prefix_sane ?l _ _ => unfold Prefix_sane; destruct l; intuition end; try rewrite app_nil_r in *; eauto using findGtIndex_app_eq.
left.
intuition.
congruence.
}
+
exfalso.
break_exists.
intuition.
replace d with (snd (nwState net h)) in * by (repeat find_rewrite; reflexivity).
find_eapply_lem_hyp nextIndex_sanity; eauto.
break_exists.
Admitted.

Lemma append_entries_leaderLogs_init : refined_raft_net_invariant_init append_entries_leaderLogs.
Proof using.
red.
unfold append_entries_leaderLogs, step_async_init.
intros.
simpl in *.
Admitted.

Lemma append_entries_leaderLogs_reboot : refined_raft_net_invariant_reboot append_entries_leaderLogs.
Proof using.
red.
unfold append_entries_leaderLogs.
intros.
repeat find_rewrite.
eapply_prop_hyp In In; eauto.
Admitted.

Theorem append_entries_leaderLogs_invariant : forall net, refined_raft_intermediate_reachable net -> append_entries_leaderLogs net.
Proof using nisi lmi si rri lhllsi.
intros.
apply refined_raft_net_invariant; auto.
-
apply append_entries_leaderLogs_init.
-
apply append_entries_leaderLogs_clientRequest.
-
apply append_entries_leaderLogs_timeout.
-
apply append_entries_leaderLogs_appendEntries.
-
apply append_entries_leaderLogs_appendEntriesReply.
-
apply append_entries_leaderLogs_requestVote.
-
apply append_entries_leaderLogs_requestVoteReply.
-
apply append_entries_leaderLogs_doLeader.
-
apply append_entries_leaderLogs_doGenericServer.
-
apply append_entries_leaderLogs_state_same_packets_subset.
-
Admitted.

Instance aerlli : append_entries_leaderLogs_interface.
split.
Admitted.

Lemma append_entries_leaderLogs_state_same_packets_subset : refined_raft_net_invariant_state_same_packet_subset append_entries_leaderLogs.
Proof using.
red.
unfold append_entries_leaderLogs.
intros.
find_apply_hyp_hyp.
eapply_prop_hyp In In; eauto.
break_exists_exists; intuition; eauto; repeat find_reverse_higher_order_rewrite; eauto.
