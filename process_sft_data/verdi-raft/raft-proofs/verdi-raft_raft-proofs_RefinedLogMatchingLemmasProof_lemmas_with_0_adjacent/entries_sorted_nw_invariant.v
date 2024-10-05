Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.AllEntriesIndicesGt0Interface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Section RefinedLogMatchingLemmas.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {lmi : log_matching_interface}.
Context {si : sorted_interface}.
Context {aeigt0 : allEntries_indices_gt_0_interface}.
Ltac forward_invariant := match goal with | [ H : refined_raft_intermediate_reachable _, H' : _ |- _ ] => apply H' in H; clear H' end.
Ltac forward_nw_invariant := match goal with | [ H : forall _ _ _ _ _ _ _, In _ _ -> pBody _ = _ -> _, H' : In _ _, H'' : pBody _ = _ |- _ ] => specialize (H _ _ _ _ _ _ _ H' H'') end.
Instance rlmli : refined_log_matching_lemmas_interface.
Proof.
constructor.
-
apply entries_contiguous_nw_invariant.
-
apply entries_gt_0_nw_invariant.
-
apply entries_sorted_nw_invariant.
-
apply entries_gt_0_invariant.
-
apply entries_contiguous_invariant.
-
apply entries_sorted_invariant.
-
apply entries_match_invariant.
-
apply entries_match_nw_1_invariant.
-
apply entries_match_nw_host_invariant.
-
apply allEntries_gt_0_invariant.
End RefinedLogMatchingLemmas.

Lemma entries_sorted_nw_invariant : forall net, refined_raft_intermediate_reachable net -> entries_sorted_nw net.
Proof using si rri.
intros.
pose proof (lift_prop _ logs_sorted_invariant).
forward_invariant.
unfold log_matching, log_matching_nw, entries_sorted_nw in *.
intuition.
find_apply_lem_hyp ghost_packet.
unfold logs_sorted in *.
break_and.
unfold logs_sorted_nw in *.
eauto.
