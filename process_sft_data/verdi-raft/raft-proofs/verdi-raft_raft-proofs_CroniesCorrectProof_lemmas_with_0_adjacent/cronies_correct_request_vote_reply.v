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

Lemma cronies_correct_request_vote_reply : refined_raft_net_invariant_request_vote_reply cronies_correct.
Proof using cvfsi vci rri.
unfold refined_raft_net_invariant_request_vote_reply.
intros.
assert (candidates_vote_for_selves (deghost net)) by eauto using candidates_vote_for_selves_l_invariant.
assert (votes_correct net) by eauto using votes_correct_invariant.
unfold cronies_correct in *; intuition.
-
unfold votes_received_cronies, update_elections_data_requestVoteReply in *.
intros.
simpl in *.
repeat break_match; repeat find_inversion; subst; simpl in *; eauto; repeat find_higher_order_rewrite; repeat (break_if; simpl in *); auto; try congruence; unfold raft_data in *; repeat find_rewrite; intuition; congruence.
-
unfold update_elections_data_requestVoteReply, cronies_votes in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
repeat (repeat break_match; simpl in *; subst; intuition eauto); try discriminate.
+
match goal with | H : type ?x = _ |- _ => remember x as cst; symmetry in Heqcst end; find_copy_apply_lem_hyp handleRequestVoteReply_candidate; auto; repeat find_rewrite; unfold votes_correct, currentTerm_votedFor_votes_correct in *; intuition; unfold candidates_vote_for_selves in *; match goal with | H : _ |- _ => apply H end; intuition; match goal with | H : forall _, type _ = _ -> votedFor _ = _ |- _ = Some ?h => specialize (H h) end; match goal with | [ H : _ |- _ ] => rewrite deghost_spec in H end; intuition eauto.
+
match goal with | H : type ?x = Leader |- _ => remember x as cst; symmetry in Heqcst end.
find_copy_apply_lem_hyp handleRequestVoteReply_leader; auto.
intuition; [repeat find_rewrite; eauto|].
find_eapply_lem_hyp handleRequestVoteReply_votesReceived; eauto.
intuition.
*
unfold votes_nw in *.
match goal with | H : _ = true |- _ => rewrite H in *; clear H end.
match goal with | H : pBody _ = _, Hpbody : forall _ _, pBody _ = _ -> _ |- _ => apply Hpbody in H end; [|solve [repeat find_rewrite; in_crush]].
repeat find_rewrite; eauto.
*
repeat find_rewrite.
unfold votes_received_cronies in *.
eauto.
+
match goal with | H : type ?x = _ |- _ => remember x as cst; symmetry in Heqcst end.
find_copy_apply_lem_hyp handleRequestVoteReply_leader; auto.
intuition.
find_eapply_lem_hyp handleRequestVoteReply_votesReceived; eauto.
intuition.
*
unfold votes_nw in *.
match goal with | H : _ = true |- _ => rewrite H in *; clear H end.
match goal with | H : pBody _ = _, Hpbody : forall _ _, pBody _ = _ -> _ |- _ => apply Hpbody in H end; [|solve [repeat find_rewrite; in_crush]].
repeat find_rewrite; eauto.
*
repeat find_rewrite.
unfold votes_received_cronies in *.
eauto.
+
match goal with | H : type ?x = _ |- _ => remember x as cst; symmetry in Heqcst end.
find_copy_apply_lem_hyp handleRequestVoteReply_candidate; auto.
find_eapply_lem_hyp handleRequestVoteReply_votesReceived; eauto.
intuition; repeat find_rewrite; eauto.
+
match goal with | H : type ?x = Leader |- _ => remember x as cst; symmetry in Heqcst end.
find_copy_apply_lem_hyp handleRequestVoteReply_leader; auto.
intuition; [repeat find_rewrite; eauto|].
find_eapply_lem_hyp handleRequestVoteReply_votesReceived; eauto.
intuition.
*
unfold votes_nw in *.
match goal with | H : _ = true |- _ => rewrite H in *; clear H end.
match goal with | H : pBody _ = _, Hpbody : forall _ _, pBody _ = _ -> _ |- _ => apply Hpbody in H end; [|solve [repeat find_rewrite; in_crush]].
repeat find_rewrite; eauto.
*
repeat find_rewrite.
unfold votes_received_cronies in *.
eauto.
+
match goal with | H : type ?x = Leader |- _ => remember x as cst; symmetry in Heqcst end.
find_copy_apply_lem_hyp handleRequestVoteReply_leader; auto.
intuition.
find_eapply_lem_hyp handleRequestVoteReply_votesReceived; eauto.
intuition.
*
unfold votes_nw in *.
match goal with | H : _ = true |- _ => rewrite H in *; clear H end.
match goal with | H : pBody _ = _, Hpbody : forall _ _, pBody _ = _ -> _ |- _ => apply Hpbody in H end; [|solve [repeat find_rewrite; in_crush]].
repeat find_rewrite; eauto.
*
repeat find_rewrite.
unfold votes_received_cronies in *.
eauto.
-
unfold votes_nw in *.
intros.
simpl in *.
find_apply_hyp_hyp.
match goal with | H : nwPackets ?net = _, H' : In ?p _ |- _ => assert (In p (nwPackets net)) by (repeat find_rewrite; in_crush); clear H H' end.
find_apply_hyp_hyp.
match goal with | H : In ?x ?y |- In ?x ?z => cut (z = y); [intros; repeat find_rewrite; auto|] end.
repeat find_higher_order_rewrite.
subst.
unfold update_elections_data_requestVoteReply in *.
repeat break_match; subst; simpl in *; repeat find_rewrite; auto.
-
unfold votes_received_leaders in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
break_if; [|eauto].
simpl in *.
find_apply_lem_hyp handleRequestVoteReply_leader; auto.
intuition; subst.
eauto.
