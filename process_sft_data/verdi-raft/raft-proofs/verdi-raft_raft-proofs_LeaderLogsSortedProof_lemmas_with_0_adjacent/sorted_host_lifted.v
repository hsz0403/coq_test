Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.SortedInterface.
Section LeaderLogsSorted.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {si : sorted_interface}.
Instance llsi : leaderLogs_sorted_interface.
Proof.
split.
eauto using leaderLogs_sorted_invariant.
Defined.
End LeaderLogsSorted.

Lemma sorted_host_lifted : forall net h, refined_raft_intermediate_reachable net -> sorted (log (snd (nwState net h))).
Proof using si rri.
intros.
pose proof (lift_prop _ logs_sorted_invariant).
find_insterU.
conclude_using eauto.
unfold logs_sorted, logs_sorted_host in *.
break_and.
unfold deghost in *.
simpl in *.
break_match.
eauto.
