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
eauto.
