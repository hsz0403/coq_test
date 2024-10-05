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

Lemma handleRequestVoteReply_leader : forall h st src t v st', handleRequestVoteReply h st src t v = st' -> type st' = Leader -> (st' = st \/ (type st = Candidate /\ wonElection (dedup name_eq_dec (votesReceived st')) = true /\ currentTerm st' = currentTerm st)).
Proof using.
intros.
unfold handleRequestVoteReply in *.
Admitted.

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
Admitted.

Lemma doLeader_st : forall st h os st' ms, doLeader st h = (os, st', ms) -> votesReceived st' = votesReceived st /\ currentTerm st' = currentTerm st /\ type st' = type st.
Proof using.
intros.
unfold doLeader, advanceCommitIndex in *.
Admitted.

Lemma do_leader_rvr : forall st h os st' ms p t ps ps', doLeader st h = (os, st', ms) -> (forall p : packet, In p ps' -> In p ps \/ In p (send_packets h ms)) -> pBody p = RequestVoteReply t true -> In p ps' -> In p ps.
Proof using.
intros.
unfold doLeader in *; repeat break_match; repeat find_inversion; simpl in *; find_apply_hyp_hyp; intuition.
in_crush.
Admitted.

Lemma cronies_correct_do_leader : refined_raft_net_invariant_do_leader cronies_correct.
Proof using.
unfold refined_raft_net_invariant_do_leader.
intros.
unfold cronies_correct in *; intuition.
-
unfold votes_received_cronies in *.
simpl in *.
intros.
find_apply_lem_hyp doLeader_st.
repeat find_higher_order_rewrite.
repeat break_match; simpl in *; repeat find_rewrite; intuition eauto; repeat find_rewrite; match goal with | _ : nwState _ ?h = _, H : forall _ _ : name, _ |- _ => specialize (H h) end; repeat find_rewrite; simpl in *; intuition eauto.
-
unfold cronies_votes in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
repeat break_if; simpl in *; subst; eauto; match goal with | [ H : forall (_ : term) (_ _ : name), _ |- In (?t, ?h) _ ] => specialize (H t h) end; repeat find_rewrite; simpl in *; find_apply_hyp_hyp; repeat find_rewrite; intuition eauto.
-
unfold votes_nw in *.
intros.
simpl in *.
find_eapply_lem_hyp do_leader_rvr; eauto.
find_apply_hyp_hyp.
find_higher_order_rewrite.
break_if; auto; subst; simpl in *; repeat find_rewrite; simpl in *; auto.
-
unfold votes_received_leaders in *.
intros.
find_apply_lem_hyp doLeader_st.
intuition.
find_higher_order_rewrite.
simpl in *.
repeat break_if; simpl in *; subst; eauto.
repeat find_rewrite.
match goal with | H : ?t = (?x, ?y) |- context [ ?y ] => assert (y = (snd t)) by (rewrite H; reflexivity); clear H; subst end.
Admitted.

Lemma do_generic_server_pkts : forall h st os st' ms ps ps' p t v, doGenericServer h st = (os, st', ms) -> (forall p, In p ps' -> In p ps \/ In p (send_packets h ms)) -> pBody p = RequestVoteReply t v -> In p ps' -> In p ps.
Proof using.
intros.
find_apply_hyp_hyp.
intuition.
unfold doGenericServer in *.
Admitted.

Lemma cronies_correct_do_generic_server : refined_raft_net_invariant_do_generic_server cronies_correct.
Proof using.
unfold refined_raft_net_invariant_do_generic_server.
intros.
unfold cronies_correct in *; intuition.
-
unfold votes_received_cronies in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
unfold doGenericServer in *.
repeat break_match; find_inversion; subst; simpl in *; eauto; match goal with | H : ?t = (?x, ?y) |- context [ ?x ] => assert (x = (fst t)) by (rewrite H; reflexivity); assert (y = (snd t)) by (rewrite H; reflexivity); clear H; subst end; use_applyEntries_spec; subst; simpl in *; intuition eauto.
-
unfold cronies_votes in *.
intros.
simpl in *.
find_higher_order_rewrite.
repeat break_match; repeat find_inversion; subst; simpl in *; eauto; try match goal with | H : ?t = (?x, ?y) |- _ => assert (x = (fst t)) by (rewrite H; reflexivity); assert (y = (snd t)) by (rewrite H; reflexivity); clear H; subst end; intuition eauto.
-
unfold votes_nw in *.
intros.
simpl in *.
find_eapply_lem_hyp do_generic_server_pkts; eauto.
find_apply_hyp_hyp.
find_higher_order_rewrite.
repeat break_if; subst; simpl in *; auto; find_rewrite; simpl in *; auto.
-
unfold votes_received_leaders in *.
intros.
simpl in *.
find_higher_order_rewrite.
unfold doGenericServer in *.
Admitted.

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
Admitted.

Lemma cronies_correct_reboot : refined_raft_net_invariant_reboot cronies_correct.
Proof using.
unfold refined_raft_net_invariant_reboot, reboot.
intros.
subst.
unfold cronies_correct in *; intuition.
-
unfold votes_received_cronies in *.
intros.
repeat find_higher_order_rewrite.
simpl in *.
repeat break_if; simpl in *; intuition eauto.
-
unfold cronies_votes in *.
intros.
repeat find_higher_order_rewrite.
simpl in *.
repeat break_if; subst; simpl in *; intuition eauto; try match goal with | H : ?t = (?x, ?y) |- _ => assert (x = (fst t)) by (rewrite H; reflexivity); assert (y = (snd t)) by (rewrite H; reflexivity); clear H; subst end; intuition eauto.
-
unfold votes_nw in *.
intros.
repeat find_higher_order_rewrite.
simpl in *.
repeat break_if; subst; simpl in *; intuition eauto; try match goal with | H : ?t = (?x, ?y) |- _ => assert (x = (fst t)) by (rewrite H; reflexivity); assert (y = (snd t)) by (rewrite H; reflexivity); clear H; subst end; intuition eauto.
-
unfold votes_received_leaders in *.
intros.
repeat find_higher_order_rewrite.
simpl in *.
Admitted.

Lemma cronies_correct_init : refined_raft_net_invariant_init cronies_correct.
Proof using.
unfold refined_raft_net_invariant_init, cronies_correct, step_async_init.
unfold votes_received_cronies, cronies_votes, votes_nw, votes_received_leaders.
simpl.
intuition.
Admitted.

Instance cci : cronies_correct_interface.
Proof.
split.
Admitted.

Theorem cronies_correct_invariant : forall (net : network), refined_raft_intermediate_reachable net -> cronies_correct net.
Proof using cvfsi vci rri.
intros.
eapply refined_raft_net_invariant; eauto.
-
apply cronies_correct_init.
-
apply cronies_correct_client_request.
-
apply cronies_correct_timeout.
-
apply cronies_correct_append_entries.
-
apply cronies_correct_append_entries_reply.
-
apply cronies_correct_request_vote.
-
apply cronies_correct_request_vote_reply.
-
apply cronies_correct_do_leader.
-
apply cronies_correct_do_generic_server.
-
apply cronies_correct_state_same_packet_subset.
-
apply cronies_correct_reboot.
