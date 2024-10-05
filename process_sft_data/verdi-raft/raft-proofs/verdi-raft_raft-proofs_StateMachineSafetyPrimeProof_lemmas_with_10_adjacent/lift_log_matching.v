Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.StateMachineSafetyPrimeInterface.
Require Import VerdiRaft.LeaderCompletenessInterface.
Require Import VerdiRaft.LeaderLogsContiguousInterface.
Require Import VerdiRaft.AllEntriesLeaderLogsInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.UniqueIndicesInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.LeaderLogsLogMatchingInterface.
Require Import VerdiRaft.LogsLeaderLogsInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.
Section StateMachineSafety'.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {lci : leader_completeness_interface}.
Context {aelli : all_entries_leader_logs_interface}.
Context {lmi : log_matching_interface}.
Context {uii : unique_indices_interface}.
Context {aerlli : append_entries_leaderLogs_interface}.
Context {llsi : leaderLogs_sorted_interface}.
Context {lsi : sorted_interface}.
Context {llci : leaderLogs_contiguous_interface}.
Context {lllmi : leaderLogs_entries_match_interface}.
Context {llli : logs_leaderLogs_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Ltac copy_eapply_prop_hyp P Q := match goal with | [ H : context [ P ], H' : context [ Q ] |- _ ] => copy_eapply H H' end.
Ltac get_invariant i := match goal with | H : refined_raft_intermediate_reachable _ |- _ => copy_apply i H end.
Set Bullet Behavior "Strict Subproofs".
Instance sms'i : state_machine_safety'interface.
Proof.
split.
intuition.
split.
-
auto using state_machine_safety_host'_invariant.
-
auto using state_machine_safety_nw'_invariant.
End StateMachineSafety'.

Theorem lift_sorted : forall net, refined_raft_intermediate_reachable net -> logs_sorted (deghost net).
Proof using lsi rri.
intros.
Admitted.

Theorem lift_entries_match : forall net h h', refined_raft_intermediate_reachable net -> entries_match (log (snd (nwState net h))) (log (snd (nwState net h'))).
Proof using lmi rri.
intros.
find_apply_lem_hyp lift_log_matching.
unfold log_matching, log_matching_hosts in *.
intuition.
unfold deghost in *.
simpl in *.
Admitted.

Theorem lift_UniqueIndices : forall net, refined_raft_intermediate_reachable net -> UniqueIndices (deghost net).
Proof using uii rri.
intros.
Admitted.

Theorem lift_uniqueIndices_log : forall net h, refined_raft_intermediate_reachable net -> uniqueIndices (log (snd (nwState net h))).
Proof using uii rri.
intros.
find_apply_lem_hyp lift_UniqueIndices.
unfold UniqueIndices, uniqueIndices_host_invariant in *.
intuition.
unfold deghost in *.
simpl in *.
Admitted.

Theorem lift_logs_sorted : forall net h, refined_raft_intermediate_reachable net -> sorted (log (snd (nwState net h))).
Proof using lsi rri.
intros.
find_apply_lem_hyp lift_sorted.
unfold logs_sorted, logs_sorted_host in *.
intuition.
unfold deghost in *.
simpl in *.
Admitted.

Theorem state_machine_safety_host'_invariant : forall net, refined_raft_intermediate_reachable net -> state_machine_safety_host' net.
Proof using uii lmi aelli lci rri.
unfold state_machine_safety_host'.
intros.
find_copy_apply_lem_hyp leader_completeness_invariant.
unfold leader_completeness in *.
intuition.
unfold committed in *.
break_exists.
intuition.
repeat match goal with | [ H : directly_committed _ ?e |- _ ] => try match goal with | H' : context [ allEntries ] |- _ => match type of H' with | context [ e ] => fail 3 end end; let Hnew := fresh "H" in remember H as Hnew; unfold directly_committed in Hnew; match goal with | [ Heq : Hnew = H |- _ ] => clear Heq end end.
break_exists.
intuition.
assert (NoDup nodes) by eauto using all_fin_NoDup.
match goal with | H : NoDup nodes, _ : NoDup ?l1, _ : NoDup ?l2 |- _ => eapply pigeon with (l := nodes) (sub1 := l1) (sub2 := l2) in H end; eauto using all_fin_all, name_eq_dec, div2_correct.
break_exists.
intuition.
repeat find_apply_hyp_hyp.
do 2 find_apply_lem_hyp all_entries_leader_logs_invariant; auto.
intuition; try solve [break_exists; intuition; find_false; eauto].
match goal with | [ _ : eIndex ?e <= eIndex ?x, _ : eIndex ?e' <= eIndex ?x', _ : In ?x ?l |- ?e = ?e' ] => cut (In e l /\ In e' l) end; [intros; intuition; eapply uniqueIndices_elim_eq; eauto using lift_uniqueIndices_log|].
Admitted.

Lemma entries_contiguous : forall net p t n pli plt es ci, refined_raft_intermediate_reachable net -> In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> contiguous_range_exact_lo es pli.
Proof using rlmli.
intros.
find_apply_lem_hyp entries_contiguous_nw_invariant.
unfold entries_contiguous_nw in *.
Admitted.

Lemma exists_deghosted_packet : forall net (p : packet (params := raft_refined_multi_params (raft_params := raft_params))), In p (nwPackets net) -> exists q, In q (nwPackets (deghost net)) /\ q = deghost_packet p.
Proof using.
unfold deghost.
simpl.
intros.
eexists; intuition eauto.
apply in_map_iff.
Admitted.

Lemma network_host_entries : forall net p t n pli plt es ci h e e', refined_raft_intermediate_reachable net -> In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> In e (log (snd (nwState net h))) -> In e' es -> eIndex e = eIndex e' -> eTerm e = eTerm e' -> In e es.
Proof using uii lmi rri.
intros.
pose proof lift_uniqueIndices_log net h; intuition.
find_copy_apply_lem_hyp lift_log_matching.
unfold log_matching, log_matching_nw in *.
intuition.
find_apply_lem_hyp exists_deghosted_packet.
break_exists.
intuition.
subst.
destruct p; simpl in *; subst.
eapply_prop_hyp In In; simpl; eauto.
intuition.
match goal with | H : forall _ _ _, _ |- _ => specialize (H h e' e) end; intuition.
repeat break_match.
simpl in *.
repeat find_rewrite.
simpl in *.
intuition.
match goal with | H : forall _, _ <= _ -> _ |- _ => specialize (H e'); conclude H ltac:(omega) end.
intuition.
Admitted.

Lemma sorted_app_in_gt : forall l1 l2 e e', sorted (l1 ++ l2) -> In e l1 -> In e' l2 -> eIndex e' < eIndex e.
Proof using.
intros; induction l1; simpl in *; intuition.
subst_max.
specialize (H2 e').
assert (In e' (l1 ++ l2)) by auto with datatypes.
concludes.
Admitted.

Theorem lift_log_matching : forall net, refined_raft_intermediate_reachable net -> log_matching (deghost net).
Proof using lmi rri.
intros.
eapply lift_prop; eauto using log_matching_invariant.
