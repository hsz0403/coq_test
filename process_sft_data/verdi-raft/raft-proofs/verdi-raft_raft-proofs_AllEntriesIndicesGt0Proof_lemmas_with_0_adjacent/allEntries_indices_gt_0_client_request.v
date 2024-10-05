Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.TermsAndIndicesFromOneLogInterface.
Require Import VerdiRaft.AllEntriesIndicesGt0Interface.
Section AllEntriesIndicesGt0.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {taifoli : terms_and_indices_from_one_log_interface}.
Instance aeigt0 : allEntries_indices_gt_0_interface.
Proof.
constructor.
exact allEntries_indices_gt_0_invariant.
End AllEntriesIndicesGt0.

Lemma allEntries_indices_gt_0_client_request : refined_raft_net_invariant_client_request allEntries_indices_gt_0.
Proof using.
unfold refined_raft_net_invariant_client_request, allEntries_indices_gt_0.
intros.
simpl in *.
repeat find_higher_order_rewrite.
update_destruct_max_simplify; eauto.
find_apply_lem_hyp update_elections_data_client_request_allEntries.
intuition.
-
find_rewrite.
eauto.
-
break_exists.
break_and.
find_rewrite.
simpl in *.
intuition eauto.
subst.
omega.
