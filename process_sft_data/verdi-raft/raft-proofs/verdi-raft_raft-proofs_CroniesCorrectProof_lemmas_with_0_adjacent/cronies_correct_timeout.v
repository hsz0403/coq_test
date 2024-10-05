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

Lemma cronies_correct_timeout : refined_raft_net_invariant_timeout cronies_correct.
Proof using.
unfold refined_raft_net_invariant_timeout.
intros.
unfold cronies_correct, update_elections_data_timeout in *; intuition.
-
unfold votes_received_cronies, handleTimeout, tryToBecomeLeader in *.
intros.
simpl in *.
repeat break_match; repeat find_inversion; subst; simpl in *; eauto; repeat find_higher_order_rewrite; repeat (break_if; simpl in *); auto; congruence.
-
unfold cronies_votes, handleTimeout, tryToBecomeLeader in *.
intros.
simpl in *.
repeat break_match; repeat find_inversion; subst; simpl in *; eauto; repeat find_higher_order_rewrite; repeat (break_if; simpl in *); auto; repeat find_inversion; subst; intuition; congruence.
-
unfold votes_nw in *.
intros.
simpl in *.
assert (In p (nwPackets net)) by eauto using handleTimeout_rvr.
repeat find_apply_hyp_hyp.
repeat find_higher_order_rewrite.
repeat break_match; subst; repeat find_rewrite; simpl in *; intuition.
-
unfold votes_received_leaders in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
unfold handleTimeout, tryToBecomeLeader in *.
simpl in *.
repeat (break_match; subst; simpl in *; repeat find_inversion; try discriminate); intuition eauto.
