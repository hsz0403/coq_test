Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CandidatesVoteForSelvesInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Section CroniesCorrectProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {vci : votes_correct_interface}.
Context {cvfsi : candidates_vote_for_selves_interface}.
Instance cci : cronies_correct_interface.
Proof.
split.
auto using cronies_correct_invariant.
End CroniesCorrectProof.

Lemma cronies_correct_append_entries : refined_raft_net_invariant_append_entries cronies_correct.
Proof using.
unfold refined_raft_net_invariant_append_entries.
intros.
unfold cronies_correct in *; intuition.
-
unfold votes_received_cronies, handleAppendEntries in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
unfold update_elections_data_appendEntries.
repeat break_match; repeat find_inversion; subst; simpl in *; eauto; repeat find_higher_order_rewrite; repeat (break_if; simpl in *); intuition; try congruence.
-
unfold cronies_votes in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
unfold update_elections_data_appendEntries in *.
repeat break_match; repeat find_inversion; subst; simpl in *; eauto.
-
unfold votes_nw in *.
intros.
simpl in *.
assert (In p0 (xs ++ ys)) by eauto using handleAppendEntries_rvr.
assert (In p0 (nwPackets net)) by (repeat find_rewrite; in_crush).
repeat find_apply_hyp_hyp.
repeat find_higher_order_rewrite.
unfold update_elections_data_appendEntries in *.
repeat break_match; subst; repeat find_rewrite; simpl in *; intuition.
-
unfold votes_received_leaders in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
repeat break_if; eauto.
subst.
simpl in *.
unfold handleAppendEntries in *.
repeat break_match; find_inversion; subst; simpl in *; try discriminate; eauto.
