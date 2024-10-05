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

Lemma doLeader_key_in_output_list : forall st h out st' m, doLeader st h = (out, st', m) -> ~ key_in_output_list client id out.
Proof using.
intros.
unfold doLeader, advanceCommitIndex in *.
repeat break_match; find_inversion; intuition eauto using key_in_output_list_empty.
