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

Theorem in_output_trace_dec : forall tr : list (name * (raft_input + list raft_output)), {in_output_trace client id out tr} + {~ in_output_trace client id out tr}.
Proof using.
unfold in_output_trace.
intros.
destruct (find (fun p => match snd p with | inr l => match find (is_client_response client id out) l with | Some x => true | None => false end | _ => false end) tr) eqn:?.
-
find_apply_lem_hyp find_some.
break_and.
repeat break_match; try discriminate.
find_apply_lem_hyp find_some.
break_and.
unfold is_client_response, in_output_list in *.
break_match; try discriminate.
break_if; try discriminate.
do_bool.
break_and.
do_bool.
subst.
left.
exists l, (fst p).
clean.
break_and.
do_bool.
break_if; try congruence.
subst.
intuition.
find_reverse_rewrite.
rewrite <- surjective_pairing.
auto.
-
right.
intro.
break_exists.
break_and.
eapply find_none in Heqo; eauto.
simpl in *.
break_match; try discriminate.
unfold in_output_list in *.
break_exists.
find_eapply_lem_hyp find_none; eauto.
simpl in *.
find_apply_lem_hyp Bool.andb_false_elim.
break_if; repeat (intuition; do_bool).
Admitted.

Lemma in_output_changed : forall tr o, ~ in_output_trace client id out tr -> in_output_trace client id out (tr ++ o) -> in_output_trace client id out o.
Proof using.
intros.
unfold in_output_trace in *.
break_exists_exists.
intuition.
do_in_app; intuition.
exfalso.
Admitted.

Lemma in_output_list_split : forall l l', in_output_list client id out (l ++ l') -> in_output_list client id out l \/ in_output_list client id out l'.
Proof using.
intros.
unfold in_output_list in *.
Admitted.

Lemma in_output_list_empty : ~ in_output_list client id out [].
Proof using.
Admitted.

Lemma handleInput_key_in_output_list : forall st h i os st' m, handleInput h i st = (os, st', m) -> ~ in_output_list client id out os.
Proof using.
intros.
unfold handleInput, handleTimeout, handleClientRequest, tryToBecomeLeader in *.
Admitted.

Lemma deduplicate_log'_app : forall l l' ks, exists l'', deduplicate_log' (l ++ l') ks = deduplicate_log' l ks ++ l''.
Proof using.
induction l; intros; simpl in *; intuition; eauto.
Admitted.

Lemma deduplicate_log_app : forall l l', exists l'', deduplicate_log (l ++ l') = deduplicate_log l ++ l''.
Proof using.
Admitted.

Lemma in_output_trace_not_nil : in_output_trace client id out [] -> False.
Proof using.
unfold in_output_trace.
simpl.
intros.
break_exists.
Admitted.

Lemma in_output_trace_singleton_inv : forall h l, in_output_trace client id out [(h, inr l)] -> in_output_list client id out l.
Proof using.
unfold in_output_trace.
intuition.
break_exists.
simpl in *.
intuition.
find_inversion.
Admitted.

Lemma in_output_list_app_or : forall c i o l1 l2, in_output_list c i o (l1 ++ l2) -> in_output_list c i o l1 \/ in_output_list c i o l2.
Proof using.
unfold in_output_list.
Admitted.

Lemma in_output_trace_inp_inv : forall h i tr, in_output_trace client id out ((h, inl i) :: tr) -> in_output_trace client id out tr.
Proof using.
unfold in_output_trace.
intuition.
break_exists_exists.
simpl in *.
intuition.
Admitted.

Lemma in_output_list_not_leader_singleton : forall a b, ~ in_output_list client id out [NotLeader a b].
Proof using.
unfold in_output_list.
simpl.
intuition.
Admitted.

Lemma handleInput_in_output_list : forall h i st os st' ms, handleInput h i st = (os, st', ms) -> ~ in_output_list client id out os.
Proof using.
unfold handleInput, handleTimeout, handleInput, tryToBecomeLeader, handleClientRequest.
intuition.
repeat break_match; repeat find_inversion; eauto using in_output_trace_not_nil.
-
exfalso.
eapply in_output_list_not_leader_singleton; eauto.
-
exfalso.
Admitted.

Lemma in_output_list_cons_or : forall a b c l, in_output_list client id out (ClientResponse a b c :: l) -> (a = client /\ b = id /\ c = out) \/ in_output_list client id out l.
Proof using.
unfold in_output_list.
simpl.
intuition.
find_inversion.
Admitted.

Lemma doLeader_key_in_output_list : forall st h os st' m, doLeader st h = (os, st', m) -> ~ in_output_list client id out os.
Proof using.
intros.
unfold doLeader, advanceCommitIndex in *.
repeat break_match; find_inversion; intuition eauto using key_in_output_list_empty.
