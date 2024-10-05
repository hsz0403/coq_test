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

Lemma exists_deghosted_packet : forall net (p : packet (params := raft_refined_multi_params (raft_params := raft_params))), In p (nwPackets net) -> exists q, In q (nwPackets (deghost net)) /\ q = deghost_packet p.
Proof using.
unfold deghost.
simpl.
intros.
eexists; intuition eauto.
apply in_map_iff.
eexists; eauto.
