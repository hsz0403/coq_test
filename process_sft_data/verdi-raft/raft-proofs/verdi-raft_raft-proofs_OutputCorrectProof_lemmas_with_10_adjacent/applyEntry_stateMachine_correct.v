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

Lemma in_output_list_cons_or : forall a b c l, in_output_list client id out (ClientResponse a b c :: l) -> (a = client /\ b = id /\ c = out) \/ in_output_list client id out l.
Proof using.
unfold in_output_list.
simpl.
intuition.
find_inversion.
Admitted.

Lemma assoc_Some_In : forall K V (K_eq_dec : forall k k' : K, {k = k'} + {k <> k'}) k v l, assoc (V:=V) K_eq_dec l k = Some v -> In (k, v) l.
Proof using.
induction l; simpl; intros; repeat break_match.
-
discriminate.
-
find_inversion.
auto.
-
Admitted.

Lemma getLastId_Some_In : forall st c n o, getLastId st c = Some (n, o) -> In (c, (n, o)) (clientCache st).
Proof using.
unfold getLastId.
Admitted.

Lemma middle_app_assoc : forall A xs (y : A) zs, xs ++ y :: zs = (xs ++ [y]) ++ zs.
Proof using.
Admitted.

Lemma deduplicate_log'_snoc_drop_keys : forall es ks e n, assoc clientId_eq_dec ks (eClient e) = Some n -> eId e <= n -> deduplicate_log' (es ++ [e]) ks = deduplicate_log' es ks.
Proof using.
induction es; simpl; intuition; repeat break_match; repeat find_inversion; do_bool.
-
omega.
-
auto.
-
discriminate.
-
f_equal.
destruct (clientId_eq_dec (eClient a) (eClient e)).
+
repeat find_rewrite.
find_injection.
eapply IHes with (n := eId a); auto with *.
now rewrite get_set_same.
+
eapply IHes; eauto.
rewrite get_set_diff by auto.
auto.
-
eauto.
-
f_equal.
destruct (clientId_eq_dec (eClient a) (eClient e)).
+
repeat find_rewrite.
discriminate.
+
eapply IHes; eauto.
rewrite get_set_diff by auto.
Admitted.

Lemma deduplicate_log'_snoc_drop_es : forall es ks e e', In e' es -> eClient e = eClient e' -> eId e <= eId e' -> deduplicate_log' (es ++ [e]) ks = deduplicate_log' es ks.
Proof using.
induction es; simpl; intuition; repeat break_match; eauto using f_equal; repeat find_reverse_rewrite.
-
f_equal.
subst.
eapply deduplicate_log'_snoc_drop_keys; eauto.
now rewrite get_set_same.
-
subst.
do_bool.
eapply deduplicate_log'_snoc_drop_keys; eauto; auto with *.
-
f_equal.
subst.
eapply deduplicate_log'_snoc_drop_keys; eauto.
Admitted.

Lemma deduplicate_log_snoc_drop : forall es e e', In e' es -> eClient e = eClient e' -> eId e <= eId e' -> deduplicate_log (es ++ [e]) = deduplicate_log es.
Proof using.
intros.
Admitted.

Lemma deduplicate_log'_snoc_split : forall es ks e, (forall e', In e' es -> eClient e' = eClient e -> eId e' < eId e) -> (forall i, assoc clientId_eq_dec ks (eClient e) = Some i -> i < eId e) -> deduplicate_log' (es ++ [e]) ks = deduplicate_log' es ks ++ [e].
Proof using.
induction es; intros; simpl in *; intuition.
-
break_match; simpl in *; auto.
break_if; simpl in *; auto.
do_bool.
find_insterU.
conclude_using eauto.
omega.
-
repeat break_match; simpl in *; auto.
+
f_equal.
eapply IHes; eauto.
intros.
do_bool.
destruct (clientId_eq_dec (eClient a) (eClient e)).
*
repeat find_rewrite.
find_rewrite_lem get_set_same.
find_injection.
find_insterU.
conclude_using eauto.
intuition.
*
find_erewrite_lem get_set_diff.
eauto.
+
f_equal.
eapply IHes; eauto.
intros.
do_bool.
destruct (clientId_eq_dec (eClient a) (eClient e)).
*
repeat find_rewrite.
find_rewrite_lem get_set_same.
find_injection.
match goal with | H : forall _, ?x = _ \/ _ -> _ |- _ => specialize (H x) end.
intuition.
*
find_erewrite_lem get_set_diff.
Admitted.

Lemma deduplicate_log_snoc_split : forall es e, (forall e', In e' es -> eClient e' = eClient e -> eId e' < eId e) -> deduplicate_log (es ++ [e]) = deduplicate_log es ++ [e].
Proof using.
intros.
eapply deduplicate_log'_snoc_split; eauto.
intros.
simpl in *.
Admitted.

Lemma execute_log_app : forall xs ys, execute_log (xs ++ ys) = let (tr, st) := execute_log xs in execute_log' ys st tr.
Proof using.
unfold execute_log.
intros.
rewrite execute_log'_app.
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
congruence.
