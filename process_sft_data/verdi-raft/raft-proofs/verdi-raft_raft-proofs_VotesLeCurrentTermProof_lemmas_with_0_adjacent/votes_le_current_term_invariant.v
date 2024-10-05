Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.VotesLeCurrentTermInterface.
Set Bullet Behavior "Strict Subproofs".
Section VotesLeCurrentTerm.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Ltac start_proof := cbn [nwState]; intros; subst; repeat find_higher_order_rewrite; update_destruct; rewrite_update; cbn [fst snd] in *; eauto.
Instance vlcti : votes_le_current_term_interface.
Proof.
split.
auto using votes_le_current_term_invariant.
End VotesLeCurrentTerm.

Theorem votes_le_current_term_invariant : forall net, refined_raft_intermediate_reachable net -> votes_le_currentTerm net.
Proof using rri.
intros.
eapply refined_raft_net_invariant; eauto.
-
apply votes_le_current_term_init.
-
apply votes_le_current_term_client_request.
-
apply votes_le_current_term_timeout.
-
apply votes_le_current_term_append_entries.
-
apply votes_le_current_term_append_entries_reply.
-
apply votes_le_current_term_request_vote.
-
apply votes_le_current_term_request_vote_reply.
-
apply votes_le_current_term_do_leader.
-
apply votes_le_current_term_do_generic_server.
-
apply votes_le_current_term_state_same_packet_subset.
-
apply votes_le_current_term_reboot.
