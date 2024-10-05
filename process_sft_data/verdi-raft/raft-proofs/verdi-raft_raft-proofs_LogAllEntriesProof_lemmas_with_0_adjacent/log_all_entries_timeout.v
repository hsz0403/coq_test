Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.LogAllEntriesInterface.
Section LogAllEntries.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {tsi : term_sanity_interface}.
Ltac rewrite_goal := match goal with | H: _ = _ |- _ => rewrite H end.
Definition no_entries_past_current_term_host_lifted net := forall (h : name) e, In e (log (snd (nwState net h))) -> eTerm e <= currentTerm (snd (nwState net h)).
Instance laei : log_all_entries_interface.
split.
auto using log_all_entries_invariant.
End LogAllEntries.

Lemma log_all_entries_timeout : refined_raft_net_invariant_timeout log_all_entries.
Proof using tsi rri.
red.
unfold log_all_entries.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto; [|copy_eapply_prop_hyp In In; repeat find_rewrite; auto].
find_copy_apply_lem_hyp handleTimeout_log_same.
rewrite update_elections_data_timeout_allEntries.
find_apply_lem_hyp handleTimeout_type_strong.
intuition; repeat find_rewrite; copy_eapply_prop_hyp In In; repeat find_rewrite; auto.
find_apply_lem_hyp no_entries_past_current_term_host_lifted_invariant; auto.
repeat find_rewrite.
unfold raft_data in *.
simpl in *.
unfold raft_data in *.
simpl in *.
omega.
