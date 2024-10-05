Require Import Verdi.TraceRelations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.AppliedEntriesMonotonicInterface.
Require Import VerdiRaft.MaxIndexSanityInterface.
Require Import VerdiRaft.StateMachineCorrectInterface.
Require Import VerdiRaft.LastAppliedCommitIndexMatchingInterface.
Require Import VerdiRaft.TraceUtil.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.OutputGreatestIdInterface.
Section OutputGreatestId.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {lmi : log_matching_interface}.
Context {si : sorted_interface}.
Context {aemi : applied_entries_monotonic_interface}.
Context {smsi : state_machine_safety_interface}.
Context {misi : max_index_sanity_interface}.
Context {smci : state_machine_correct_interface}.
Context {lacimi : lastApplied_commitIndex_match_interface}.
Section inner.
Variable client : clientId.
Variables id id' : nat.
Variable id_lt_id' : id < id'.
Program Instance TR : TraceRelation step_failure := { init := step_failure_init; T := key_in_output_trace client id ; T_dec := key_in_output_trace_dec client id ; R := fun s => before_func (has_key client id) (has_key client id') (applied_entries (nwState (snd s))) }.
Next Obligation.
simpl in *.
find_apply_lem_hyp step_failure_star_raft_intermediate_reachable.
find_eapply_lem_hyp applied_entries_monotonic'; eauto.
break_exists; repeat find_rewrite.
eauto using before_func_app.
Defined.
Next Obligation.
unfold key_in_output_trace in *.
intuition.
break_exists; intuition.
Defined.
Next Obligation.
find_apply_lem_hyp step_failure_star_raft_intermediate_reachable.
find_apply_lem_hyp in_output_changed; auto.
eauto using output_implies_greatest.
Defined.
End inner.
Instance ogii : output_greatest_id_interface.
Proof.
split.
unfold greatest_id_for_client.
intros.
eauto using output_greatest_id.
End OutputGreatestId.

Lemma applyEntries_cache : forall l h st os st' o client id id' o', id < id' -> applyEntries h st l = (os, st') -> In (ClientResponse client id o) os -> getLastId st client <> Some (id', o').
Proof using.
induction l; intros; simpl in *; intuition.
-
find_inversion.
simpl in *.
intuition.
-
unfold cacheApplyEntry, applyEntry in *.
repeat break_match; repeat find_inversion; simpl in *; intuition; eauto; try solve [find_inversion; find_rewrite; find_inversion; do_bool; omega]; try solve [find_inversion; repeat find_rewrite; congruence].
+
do_bool.
destruct (clientId_eq_dec (eClient a) client).
*
subst.
find_rewrite.
find_inversion.
eapply IHl; [eapply lt_le_trans; eauto|idtac|idtac|]; eauto.
unfold getLastId.
simpl.
eauto using get_set_same.
*
eapply IHl; eauto.
unfold getLastId in *.
simpl.
rewrite get_set_diff; eauto.
+
do_bool.
destruct (clientId_eq_dec (eClient a) client).
*
repeat find_rewrite.
congruence.
*
eapply IHl; eauto.
unfold getLastId in *.
simpl.
rewrite get_set_diff; eauto.
+
do_bool.
destruct (clientId_eq_dec (eClient a) client).
*
repeat find_rewrite.
find_inversion.
eapply IHl; [eapply lt_le_trans; eauto|idtac|idtac|]; eauto.
unfold getLastId.
simpl.
eauto using get_set_same.
*
eapply IHl; eauto.
unfold getLastId in *.
simpl.
rewrite get_set_diff; eauto.
+
do_bool.
destruct (clientId_eq_dec (eClient a) client).
*
repeat find_rewrite.
congruence.
*
eapply IHl; eauto.
unfold getLastId in *.
simpl.
rewrite get_set_diff; eauto.
