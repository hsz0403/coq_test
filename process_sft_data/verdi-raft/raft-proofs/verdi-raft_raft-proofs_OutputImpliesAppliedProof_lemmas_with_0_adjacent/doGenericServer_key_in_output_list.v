Require Import Verdi.TraceRelations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.AppliedEntriesMonotonicInterface.
Require Import VerdiRaft.MaxIndexSanityInterface.
Require Import VerdiRaft.TraceUtil.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.OutputImpliesAppliedInterface.
Section OutputImpliesApplied.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {lmi : log_matching_interface}.
Context {si : sorted_interface}.
Context {aemi : applied_entries_monotonic_interface}.
Context {smsi : state_machine_safety_interface}.
Context {misi : max_index_sanity_interface}.
Section inner.
Variable client : clientId.
Variable id : nat.
Program Instance TR : TraceRelation step_failure := { init := step_failure_init; T := key_in_output_trace client id ; T_dec := key_in_output_trace_dec client id ; R := fun s => in_applied_entries client id (snd s) }.
Next Obligation.
unfold in_applied_entries in *.
break_exists; eexists; intuition eauto.
eapply applied_entries_monotonic; eauto.
eauto using refl_trans_1n_n1_trace, step_failure_star_raft_intermediate_reachable.
Defined.
Next Obligation.
unfold key_in_output_trace in *.
intuition.
break_exists; intuition.
Defined.
Next Obligation.
simpl in *.
find_apply_lem_hyp step_failure_star_raft_intermediate_reachable.
find_apply_lem_hyp in_output_changed; auto.
eauto using output_implies_in_applied_entries.
Defined.
End inner.
Instance oiai : output_implies_applied_interface.
Proof.
split.
intros.
eapply output_implies_applied; eauto.
End OutputImpliesApplied.

Lemma doGenericServer_key_in_output_list : forall net h os st' ms, raft_intermediate_reachable net -> doGenericServer h (nwState net h) = (os, st', ms) -> key_in_output_list client id os -> exists e : entry, eClient e = client /\ eId e = id /\ In e (applied_entries (update name_eq_dec (nwState net) h st')).
Proof using misi smsi lmi.
intros.
unfold key_in_output_list in *.
match goal with | H : exists _, _ |- _ => destruct H as [o] end.
unfold doGenericServer in *.
break_let.
simpl in *.
find_inversion.
simpl in *.
pose proof Heqp as Happ.
find_eapply_lem_hyp applyEntries_In; eauto.
use_applyEntries_spec; subst_max; simpl in *.
eexists; intuition eauto.
find_apply_lem_hyp In_rev.
find_apply_lem_hyp filter_In.
intuition.
repeat (do_bool; intuition).
break_if; simpl in *; do_bool; [|try omega].
match goal with | |- context [update _ ?st ?h ?st'] => pose proof applied_entries_update st h st' end.
forwards; [simpl in *; intuition|].
concludes.
intuition.
-
simpl in *.
unfold raft_data in *.
simpl in *.
find_rewrite.
match goal with | H : applied_entries _ = applied_entries _ |- _ => clear H end.
break_exists.
intuition.
unfold applied_entries in *.
find_rewrite.
match goal with | |- In _ (rev ?l') => apply in_rev with (l := l') end.
apply removeAfterIndex_le_In; intuition.
find_copy_apply_lem_hyp log_matching_invariant.
find_copy_apply_lem_hyp max_index_sanity_invariant.
find_apply_lem_hyp state_machine_safety_invariant.
unfold state_machine_safety, log_matching, log_matching_hosts, maxIndex_sanity in *.
intuition.
match goal with | [ e : entry, H : forall _ _, _ <= _ <= _ -> _, Hm : maxIndex_lastApplied _ |- In _ (log (_ _ ?h)) ] => specialize (H h (eIndex e)); specialize (Hm h); forward H; intuition end.
break_exists.
intuition.
find_apply_lem_hyp findGtIndex_necessary.
intuition.
match goal with | _ : In ?e1 (log _), _ : In ?e2 (log _) |- _ => cut (e1 = e2); [intros; subst; auto|] end.
eapply_prop state_machine_safety_host; unfold commit_recorded; intuition eauto.
omega.
-
simpl in *.
unfold raft_data in *.
simpl in *.
find_rewrite.
match goal with | |- In _ (rev ?l') => apply in_rev with (l := l') end.
find_apply_lem_hyp findGtIndex_necessary.
intuition.
eauto using removeAfterIndex_le_In.
