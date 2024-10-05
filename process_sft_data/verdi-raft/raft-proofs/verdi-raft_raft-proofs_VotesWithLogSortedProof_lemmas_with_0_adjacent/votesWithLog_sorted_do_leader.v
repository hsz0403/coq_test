Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.VotesWithLogSortedInterface.
Require Import VerdiRaft.SortedInterface.
Section VotesWithLogSorted.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {si : sorted_interface}.
Instance vwlsi : votesWithLog_sorted_interface.
Proof.
split.
exact votesWithLog_sorted_invariant.
End VotesWithLogSorted.

Lemma votesWithLog_sorted_do_leader : refined_raft_net_invariant_do_leader votesWithLog_sorted.
Proof using.
unfold refined_raft_net_invariant_do_leader, votesWithLog_sorted.
intros.
subst.
simpl in *.
find_higher_order_rewrite.
update_destruct_simplify.
-
match goal with | [ H : _, H' : _ |- _ ] => eapply H; rewrite H'; simpl; eauto end.
-
eauto.
