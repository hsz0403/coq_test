Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeadersHaveLeaderLogsInterface.
Require Import VerdiRaft.AppendEntriesRequestsCameFromLeadersInterface.
Section AppendEntriesRequestsCameFromLeaders.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {lhlli : leaders_have_leaderLogs_interface}.
Context {rri : raft_refinement_interface}.
Ltac start := red; unfold append_entries_came_from_leaders; intros; subst; simpl in *; find_higher_order_rewrite; update_destruct_hyp; subst; rewrite_update; eauto; simpl in *.
Ltac prove_in := match goal with | [ _ : nwPackets ?net = _, _ : In (?p : packet) _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition) | [ _ : nwPackets ?net = _, _ : pBody ?p = _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; intuition) end.
Ltac contra := (exfalso; intuition; find_false; repeat eexists; eauto).
Instance aercfli : append_entries_came_from_leaders_interface.
split.
exact append_entries_came_from_leaders_invariant.
End AppendEntriesRequestsCameFromLeaders.

Lemma append_entries_came_from_leaders_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset append_entries_came_from_leaders.
Proof using.
red.
unfold append_entries_came_from_leaders.
intros.
find_apply_hyp_hyp.
find_apply_hyp_hyp.
repeat find_higher_order_rewrite.
eauto.
