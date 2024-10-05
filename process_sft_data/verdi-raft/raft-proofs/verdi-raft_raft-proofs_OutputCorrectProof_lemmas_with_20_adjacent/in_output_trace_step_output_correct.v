Require Import Verdi.TraceRelations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.OutputCorrectInterface.
Require Import VerdiRaft.AppliedEntriesMonotonicInterface.
Require Import VerdiRaft.TraceUtil.
Require Import VerdiRaft.StateMachineCorrectInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LastAppliedCommitIndexMatchingInterface.
Require Import VerdiRaft.LogMatchingInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Section OutputCorrect.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {aemi : applied_entries_monotonic_interface}.
Context {smci : state_machine_correct_interface}.
Context {si : sorted_interface}.
Context {lacimi : lastApplied_commitIndex_match_interface}.
Context {lmi : log_matching_interface}.
Section inner.
Variable client : clientId.
Variables id : nat.
Variable out : output.
Ltac intermediate_networks := match goal with | Hdgs : doGenericServer ?h ?st' = _, Hdl : doLeader ?st ?h = _ |- context [update _ (nwState ?net) ?h ?st''] => replace st with (update name_eq_dec (nwState net) h st h) in Hdl by eauto using update_eq; replace st' with (update name_eq_dec (update name_eq_dec (nwState net) h st) h st' h) in Hdgs by eauto using update_eq; let H := fresh "H" in assert (update name_eq_dec (nwState net) h st'' = update name_eq_dec (update name_eq_dec (update name_eq_dec (nwState net) h st) h st') h st'') by (repeat rewrite update_overwrite; auto); unfold data in *; simpl in *; rewrite H; clear H end.
Program Instance TR : TraceRelation step_failure := { init := step_failure_init; T := in_output_trace client id out ; T_dec := in_output_trace_dec ; R := fun s => let (_, net) := s in output_correct client id out (applied_entries (nwState net)) }.
Next Obligation.
repeat break_let.
subst.
find_eapply_lem_hyp applied_entries_monotonic'; eauto using step_failure_star_raft_intermediate_reachable.
unfold output_correct in *.
break_exists.
repeat find_rewrite.
match goal with | [ |- context [ deduplicate_log (?l ++ ?l') ] ] => pose proof deduplicate_log_app l l'; break_exists; find_rewrite end.
repeat eexists; intuition eauto; repeat find_rewrite; auto.
rewrite app_ass.
simpl.
repeat f_equal.
Defined.
Next Obligation.
unfold in_output_trace in *.
intuition.
break_exists; intuition.
Defined.
Next Obligation.
find_apply_lem_hyp in_output_changed; auto.
eauto using in_output_trace_step_output_correct, step_failure_star_raft_intermediate_reachable.
Defined.
End inner.
Instance oci : output_correct_interface.
Proof using smci si lmi lacimi aemi.
split.
exact output_correct.
End OutputCorrect.

Lemma applyEntry_stateMachine_correct : forall st e l st' es, applyEntry st e = (l, st') -> stateMachine st = snd (execute_log (deduplicate_log es)) -> (forall e', In e' es -> eClient e' = eClient e -> eId e' < eId e) -> stateMachine st' = snd (execute_log (deduplicate_log es ++ [e])).
Proof using.
unfold applyEntry.
intros.
repeat break_match; repeat find_inversion.
simpl.
rewrite execute_log_app.
simpl.
repeat break_let.
simpl in *.
Admitted.

Lemma deduplicate_log_cases : forall es e, (deduplicate_log (es ++ [e]) = deduplicate_log es /\ exists e', In e' es /\ eClient e' = eClient e /\ eId e <= eId e') \/ (deduplicate_log (es ++ [e]) = deduplicate_log es ++ [e] /\ (forall e', In e' es -> eClient e' = eClient e -> eId e' < eId e)).
Proof using.
intros.
destruct (find (fun e' => andb (if clientId_eq_dec (eClient e') (eClient e) then true else false) (eId e <=? eId e')) es) eqn:?.
-
left.
find_apply_lem_hyp find_some.
break_if; repeat (break_and; do_bool); try congruence.
intuition eauto using deduplicate_log_snoc_drop.
-
right.
match goal with | |- _ /\ ?P => assert P; [|intuition; eauto using deduplicate_log_snoc_split] end.
intros.
find_eapply_lem_hyp find_none; eauto.
simpl in *.
Admitted.

Lemma assoc_None : forall K V K_eq_dec (l : list (K * V)) k v, assoc K_eq_dec l k = None -> In (k, v) l -> False.
Proof using.
intros; induction l; simpl in *; intuition.
-
subst.
break_if; congruence.
-
break_match.
subst.
break_if; try congruence.
Admitted.

Lemma getLastId_None : forall st c i o, getLastId st c = None -> In (c, (i, o)) (clientCache st) -> False.
Proof using.
intros.
unfold getLastId in *.
Admitted.

Lemma output_correct_monotonic : forall c i o xs ys, output_correct c i o xs -> output_correct c i o (xs ++ ys).
Proof using.
unfold output_correct.
intros.
break_exists.
intuition.
pose proof (deduplicate_log_app xs ys).
break_exists.
repeat find_rewrite.
rewrite app_ass in *.
simpl in *.
eexists.
eexists.
eexists.
eexists.
eexists.
Admitted.

Lemma applyEntry_output_correct : forall st e l st' o es, applyEntry st e = (l, st') -> In o l -> stateMachine st = snd (execute_log (deduplicate_log es)) -> (forall e', In e' es -> eClient e' = eClient e -> eId e' < eId e) -> output_correct (eClient e) (eId e) o (es ++ [e]).
Proof using.
unfold applyEntry.
intros.
repeat break_match; repeat find_inversion.
simpl in *.
intuition.
subst.
unfold output_correct.
rewrite deduplicate_log_snoc_split by auto.
destruct (execute_log (deduplicate_log es)) eqn:?.
eexists.
eexists.
exists [].
eexists.
eexists.
intuition eauto.
-
rewrite execute_log_app.
repeat find_rewrite.
simpl in *.
find_rewrite.
eauto.
-
rewrite rev_app_distr.
simpl.
Admitted.

Lemma cacheApplyEntry_output_correct : forall e es st l st' o, cacheApplyEntry st e = (l, st') -> In o l -> (forall c i o, getLastId st c = Some (i, o) -> output_correct c i o es) -> stateMachine st = snd (execute_log (deduplicate_log es)) -> (forall c i o e', getLastId st c = Some (i, o) -> In e' es -> eClient e' = c -> eId e' <= i) -> (forall e', In e' es -> exists i o, getLastId st (eClient e') = Some (i, o) /\ eId e' <= i) -> output_correct (eClient e) (eId e) o (es ++ [e]).
Proof using.
unfold cacheApplyEntry.
intros.
repeat break_match; repeat find_inversion; simpl in *; intuition.
-
do_bool.
subst.
eauto using output_correct_monotonic, getLastId_Some_In.
-
eapply applyEntry_output_correct; eauto.
do_bool.
assert (n < eId e) by auto with *.
intros.
assert (eId e' <= n) by eauto.
omega.
-
eapply applyEntry_output_correct; eauto.
intros.
find_apply_hyp_hyp.
break_exists.
break_and.
repeat find_rewrite.
Admitted.

Lemma cacheApplyEntry_stateMachine_correct : forall st e l st' es, cacheApplyEntry st e = (l, st') -> stateMachine st = snd (execute_log (deduplicate_log es)) -> (forall c i o, getLastId st c = Some (i, o) -> exists e, In e es /\ eClient e = c /\ eId e = i) -> (forall c i o e', getLastId st c = Some (i, o) -> In e' es -> eClient e' = c -> eId e' <= i) -> (forall e', In e' es -> exists i o, getLastId st (eClient e') = Some (i, o) /\ eId e' <= i) -> stateMachine st' = snd (execute_log (deduplicate_log (es ++ [e]))).
Proof using.
intros.
unfold cacheApplyEntry in *.
repeat break_match; repeat find_inversion.
-
find_apply_hyp_hyp.
break_exists.
break_and.
erewrite deduplicate_log_snoc_drop; eauto.
do_bool.
omega.
-
find_apply_hyp_hyp.
break_exists.
break_and.
erewrite deduplicate_log_snoc_drop; eauto.
do_bool.
omega.
-
find_copy_apply_hyp_hyp.
break_exists.
break_and.
pose proof (deduplicate_log_cases es e).
intuition; break_exists; intuition; repeat find_rewrite.
+
do_bool.
assert (eId x0 <= n) by eauto.
omega.
+
eapply applyEntry_stateMachine_correct; eauto.
-
pose proof (deduplicate_log_cases es e).
intuition; break_exists; intuition; repeat find_rewrite.
+
eapply_prop_hyp In In.
break_exists.
break_and.
repeat find_rewrite.
discriminate.
+
Admitted.

Lemma deduplicate_log_In_if : forall e l, In e (deduplicate_log l) -> In e l.
Proof using.
unfold deduplicate_log.
intros.
Admitted.

Lemma applyEntry_clientCache : forall st e l st', applyEntry st e = (l, st') -> let (out, _) := handler (eInput e) (stateMachine st) in (clientCache st' = assoc_set clientId_eq_dec (clientCache st) (eClient e) (eId e, out) /\ In out l).
Proof using.
unfold applyEntry.
intros.
repeat break_match; repeat find_inversion.
Admitted.

Lemma cacheApplyEntry_clientCache : forall st e l st', cacheApplyEntry st e = (l, st') -> (clientCache st' = clientCache st /\ (exists i o, getLastId st (eClient e) = Some (i, o) /\ eId e <= i) ) \/ ((let (out, _) := handler (eInput e) (stateMachine st) in (clientCache st' = assoc_set clientId_eq_dec (clientCache st) (eClient e) (eId e, out) /\ In out l)) /\ (getLastId st (eClient e) = None \/ (exists i o, getLastId st (eClient e) = Some (i, o) /\ i < eId e))).
Proof using.
unfold cacheApplyEntry.
intros.
repeat break_match_hyp; repeat find_inversion; do_bool; intuition eauto with *; right; (split; [solve [apply applyEntry_clientCache; auto]|]); auto.
right.
do_bool.
eexists.
eexists.
intuition eauto.
Admitted.

Lemma getLastId_ext : forall st st' c, clientCache st' = clientCache st -> getLastId st' c = getLastId st c.
Proof using.
unfold getLastId.
intros.
Admitted.

Lemma cacheAppliedEntry_clientCache_preserved : forall st e l st' c i o, cacheApplyEntry st e = (l, st') -> getLastId st c = Some (i, o) -> exists i' o', getLastId st' c = Some (i', o') /\ i <= i'.
Proof using.
intros.
unfold cacheApplyEntry in *.
repeat break_match; try find_inversion; simpl in *; repeat find_rewrite; eauto.
-
do_bool.
unfold applyEntry in *.
repeat break_match; find_inversion.
unfold getLastId in *.
simpl in *.
destruct (clientId_eq_dec (eClient e) c); subst.
+
rewrite get_set_same.
find_rewrite.
find_inversion.
eauto.
+
rewrite get_set_diff in *; auto.
repeat find_rewrite.
eauto.
-
unfold applyEntry in *.
repeat break_match; find_inversion.
unfold getLastId in *.
simpl in *.
destruct (clientId_eq_dec (eClient e) c); subst.
+
repeat find_rewrite.
congruence.
+
rewrite get_set_diff in *; auto.
repeat find_rewrite.
Admitted.

Lemma cacheAppliedEntry_clientCache_nondecreasing : forall st e l st' c i o i' o', cacheApplyEntry st e = (l, st') -> getLastId st c = Some (i, o) -> getLastId st' c = Some (i', o') -> i <= i'.
Proof using.
intros.
eapply cacheAppliedEntry_clientCache_preserved in H; eauto.
break_exists.
intuition.
repeat find_rewrite.
find_inversion.
Admitted.

Lemma applyEntries_output_correct : forall l c i o h st os st' es, applyEntries h st l = (os, st') -> in_output_list c i o os -> (stateMachine st = snd (execute_log (deduplicate_log es))) -> (forall c i o, getLastId st c = Some (i, o) -> output_correct c i o es) -> (forall c i o e', getLastId st c = Some (i, o) -> In e' es -> eClient e' = c -> eId e' <= i) -> (forall e', In e' es -> exists i o, getLastId st (eClient e') = Some (i, o) /\ eId e' <= i) -> output_correct c i o (es ++ l).
Proof using out id client.
induction l; intros; simpl in *.
-
find_inversion.
exfalso.
eapply in_output_list_empty; eauto.
-
repeat break_let.
find_inversion.
find_apply_lem_hyp in_output_list_app_or.
break_or_hyp.
+
break_if.
*
unfold in_output_list in *.
do_in_map.
find_inversion.
rewrite middle_app_assoc.
apply output_correct_monotonic.
eapply cacheApplyEntry_output_correct; eauto.
*
exfalso.
eapply in_output_list_empty; eauto.
+
rewrite middle_app_assoc.
eapply IHl.
*
eauto.
*
auto.
*
eapply cacheApplyEntry_stateMachine_correct; eauto.
intros.
find_apply_hyp_hyp.
unfold output_correct in *.
break_exists.
break_and.
eexists.
intuition eauto.
eapply deduplicate_log_In_if.
eauto with *.
*
find_copy_apply_lem_hyp cacheApplyEntry_clientCache.
{
intros.
break_or_hyp.
-
break_and.
apply output_correct_monotonic.
unfold getLastId in *.
repeat find_rewrite.
eauto.
-
break_let.
break_and.
unfold getLastId in *.
repeat find_rewrite.
destruct (clientId_eq_dec (eClient a) c0).
+
subst.
rewrite get_set_same in *.
find_inversion.
eapply cacheApplyEntry_output_correct; eauto.
+
rewrite get_set_diff in * by auto.
eauto using output_correct_monotonic.
}
*
intros.
do_in_app.
simpl in *.
{
intuition.
-
eapply_prop_hyp In In.
break_exists.
break_and.
subst.
eauto using le_trans, cacheAppliedEntry_clientCache_nondecreasing.
-
subst.
find_copy_apply_lem_hyp cacheApplyEntry_clientCache.
intuition.
+
break_exists.
break_and.
eauto using le_trans, cacheAppliedEntry_clientCache_nondecreasing.
+
unfold getLastId in *.
break_let.
break_and.
repeat find_rewrite.
rewrite get_set_same in *.
find_inversion.
auto.
+
unfold getLastId in *.
break_let.
break_and.
repeat find_rewrite.
rewrite get_set_same in *.
find_inversion.
auto.
}
*
intros.
do_in_app.
simpl in *.
{
intuition.
-
eapply_prop_hyp In In.
break_exists.
break_and.
find_copy_eapply_lem_hyp cacheAppliedEntry_clientCache_preserved; eauto.
break_exists_exists.
intuition.
-
subst.
find_copy_apply_lem_hyp cacheApplyEntry_clientCache.
intuition.
+
break_exists.
break_and.
find_copy_eapply_lem_hyp cacheAppliedEntry_clientCache_preserved; eauto.
break_exists_exists.
intuition.
+
break_let.
break_and.
unfold getLastId.
repeat find_rewrite.
eexists.
eexists.
rewrite get_set_same.
intuition eauto.
+
break_let.
break_and.
unfold getLastId.
repeat find_rewrite.
eexists.
eexists.
rewrite get_set_same.
intuition eauto.
Admitted.

Lemma cacheApplyEntry_spec : forall st a l st', cacheApplyEntry st a = (l, st') -> log st' = log st /\ lastApplied st' = lastApplied st /\ commitIndex st' = commitIndex st.
Proof using.
intros.
unfold cacheApplyEntry, applyEntry in *.
Admitted.

Lemma applyEntries_spec : forall es h st os st', applyEntries h st es = (os, st') -> log st' = log st /\ lastApplied st' = lastApplied st /\ commitIndex st' = commitIndex st.
Proof using.
induction es; intros; simpl in *.
-
find_inversion.
auto.
-
Admitted.

Lemma output_correct_prefix : forall l1 l2 client id out, Prefix l1 l2 -> output_correct client id out l1 -> output_correct client id out l2.
Proof using.
intros.
find_apply_lem_hyp Prefix_exists_rest.
break_exists.
subst.
Admitted.

Lemma entries_contiguous : forall net, raft_intermediate_reachable net -> (forall h, contiguous_range_exact_lo (log (nwState net h)) 0).
Proof using lmi.
intros.
find_apply_lem_hyp log_matching_invariant.
unfold log_matching, log_matching_hosts in *.
intuition.
unfold contiguous_range_exact_lo.
intuition; eauto.
find_apply_hyp_hyp.
Admitted.

Lemma doGenericServer_output_correct : forall h ps sigma os st' ms, raft_intermediate_reachable (mkNetwork ps sigma) -> doGenericServer h (sigma h) = (os, st', ms) -> in_output_list client id out os -> output_correct client id out (applied_entries (update name_eq_dec sigma h st')).
Proof using lmi lacimi si smci.
intros.
find_copy_apply_lem_hyp logs_sorted_invariant.
pose proof entries_contiguous.
match goal with | H : context [contiguous_range_exact_lo] |- _ => specialize (H ({| nwPackets := ps; nwState := sigma |})) end.
concludes.
simpl in *.
find_copy_apply_lem_hyp state_machine_correct_invariant.
unfold state_machine_correct in *.
intuition.
unfold logs_sorted in *.
intuition.
unfold doGenericServer in *.
break_let.
find_inversion.
find_copy_apply_lem_hyp applyEntries_spec.
intuition.
repeat find_rewrite.
eapply applyEntries_output_correct with (es := rev (removeAfterIndex (log (sigma h)) (lastApplied (sigma h)))) in Heqp; eauto.
-
rewrite <- rev_app_distr in *.
eapply output_correct_prefix; eauto.
break_if.
+
do_bool.
erewrite findGtIndex_removeAfterIndex_i_lt_i' in *; eauto.
match goal with | |- context [applied_entries (update _ ?sigma ?h ?st)] => pose proof applied_entries_update sigma h st end.
conclude_using intuition.
intuition; simpl in *; unfold raft_data in *; simpl in *; find_rewrite; auto using Prefix_refl.
unfold applied_entries in *.
break_exists.
intuition.
repeat find_rewrite.
eapply contiguous_sorted_subset_prefix; eauto using removeAfterIndex_contiguous, removeAfterIndex_sorted.
intros.
find_copy_apply_lem_hyp removeAfterIndex_In_le; eauto.
find_apply_lem_hyp removeAfterIndex_in.
apply removeAfterIndex_le_In; eauto; try omega.
find_copy_apply_lem_hyp commitIndex_lastApplied_match_invariant.
unfold commitIndex_lastApplied_match in *.
simpl in *.
match goal with | _ : ?x >= ?y |- _ => assert (y <= x) by omega end.
eapply_prop_hyp le le; eauto.
intuition.
+
do_bool.
erewrite findGtIndex_removeAfterIndex_i'_le_i in *; eauto.
match goal with | |- context [applied_entries (update _ ?sigma ?h ?st)] => pose proof applied_entries_update sigma h st end.
conclude_using intuition.
intuition; simpl in *; unfold raft_data in *; simpl in *; find_rewrite; auto using Prefix_refl.
unfold applied_entries in *.
break_exists.
intuition.
repeat find_rewrite.
eapply contiguous_sorted_subset_prefix; eauto using removeAfterIndex_contiguous, removeAfterIndex_sorted.
intros.
find_copy_apply_lem_hyp removeAfterIndex_In_le; eauto.
find_apply_lem_hyp removeAfterIndex_in.
apply removeAfterIndex_le_In; eauto; try omega.
find_copy_apply_lem_hyp lastApplied_lastApplied_match_invariant.
unfold lastApplied_lastApplied_match in *.
simpl in *.
match goal with | _ : ?x >= ?y |- _ => assert (y <= x) by omega end.
eapply_prop_hyp le le; eauto.
intuition.
-
unfold client_cache_complete in *.
simpl in *.
intros.
subst.
find_apply_lem_hyp In_rev.
find_apply_hyp_hyp.
break_exists.
intuition.
repeat find_rewrite.
match goal with | H : Some _ = Some _ |- _ => invcs H end.
auto.
-
intros.
find_apply_lem_hyp In_rev.
Admitted.

Theorem output_correct : forall failed net tr, step_failure_star step_failure_init (failed, net) tr -> in_output_trace client id out tr -> output_correct client id out (applied_entries (nwState net)).
Proof using lmi lacimi si smci aemi.
intros.
pose proof (trace_relations_work (failed, net) tr).
repeat concludes.
Admitted.

Instance oci : output_correct_interface.
Proof using smci si lmi lacimi aemi.
split.
Admitted.

Lemma in_output_trace_step_output_correct : forall failed failed' (net net' : network (params := @multi_params _ _ raft_params)) os, in_output_trace client id out os -> @raft_intermediate_reachable _ _ raft_params net -> step_failure (failed, net) (failed', net') os -> output_correct client id out (applied_entries (nwState net')).
Proof using lmi lacimi si smci.
intros.
match goal with | [ H : context [ step_failure _ _ _ ] |- _ ] => invcs H end.
-
unfold RaftNetHandler in *.
repeat break_let.
repeat find_inversion.
find_apply_lem_hyp in_output_trace_singleton_inv.
find_apply_lem_hyp in_output_list_app_or.
intuition.
+
exfalso.
eapply doLeader_key_in_output_list; eauto.
+
find_copy_eapply_lem_hyp RIR_handleMessage; eauto.
find_copy_eapply_lem_hyp RIR_doLeader; simpl; rewrite_update; eauto.
intermediate_networks.
find_copy_apply_lem_hyp doLeader_appliedEntries.
eapply doGenericServer_output_correct; eauto.
-
unfold RaftInputHandler in *.
repeat break_let.
repeat find_inversion.
find_apply_lem_hyp in_output_trace_inp_inv.
find_apply_lem_hyp in_output_trace_singleton_inv.
find_apply_lem_hyp in_output_list_app_or.
intuition.
+
exfalso.
eapply handleInput_in_output_list; eauto.
+
find_apply_lem_hyp in_output_list_app_or.
intuition.
*
exfalso.
eapply doLeader_key_in_output_list; eauto.
*
find_copy_eapply_lem_hyp RIR_handleInput; eauto.
find_copy_eapply_lem_hyp RIR_doLeader; simpl; rewrite_update; eauto.
intermediate_networks.
find_copy_apply_lem_hyp doLeader_appliedEntries.
eapply doGenericServer_output_correct; eauto.
-
exfalso.
eauto using in_output_trace_not_nil.
-
exfalso.
eauto using in_output_trace_not_nil.
-
exfalso.
eauto using in_output_trace_not_nil.
-
exfalso.
eauto using in_output_trace_not_nil.
