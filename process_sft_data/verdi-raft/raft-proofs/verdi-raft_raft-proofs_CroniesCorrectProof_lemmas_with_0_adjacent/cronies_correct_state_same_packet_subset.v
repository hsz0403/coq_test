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

Lemma cronies_correct_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset cronies_correct.
Proof using.
unfold refined_raft_net_invariant_state_same_packet_subset.
intros.
unfold cronies_correct in *; intuition.
-
unfold votes_received_cronies in *.
intros.
repeat find_reverse_higher_order_rewrite.
eauto.
-
unfold cronies_votes in *.
intros.
repeat find_reverse_higher_order_rewrite.
eauto.
-
unfold votes_nw in *.
intros.
repeat find_reverse_higher_order_rewrite.
eauto.
-
unfold votes_received_leaders in *.
intros.
repeat find_reverse_higher_order_rewrite.
eauto.
