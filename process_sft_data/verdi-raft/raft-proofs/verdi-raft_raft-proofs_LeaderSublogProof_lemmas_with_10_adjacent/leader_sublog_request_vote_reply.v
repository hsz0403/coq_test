Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.OneLeaderPerTermInterface.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.LeaderSublogInterface.
Hint Extern 4 (@BaseParams) => apply base_params : typeclass_instances.
Hint Extern 4 (@MultiParams _) => apply multi_params : typeclass_instances.
Hint Extern 4 (@FailureParams _ _) => apply failure_params : typeclass_instances.
Section LeaderSublogProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cei : candidate_entries_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Context {olpti : one_leader_per_term_interface}.
Ltac prove_in := match goal with | [ _ : nwPackets ?net = _, _ : In (?p : packet) _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition) | [ _ : nwPackets ?net = _, _ : pBody ?p = _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; intuition) end.
Notation is_append_entries m := (exists t n prevT prevI entries c, m = AppendEntries t n prevT prevI entries c).
Definition CandidateEntriesLowered net e h := currentTerm (nwState net h) = eTerm e -> wonElection (dedup name_eq_dec (votesReceived (nwState net h))) = true -> type (nwState net h) <> Candidate.
Definition CandidateEntriesLowered_rvr net e p := In p (nwPackets net) -> pBody p = RequestVoteReply (eTerm e) true -> currentTerm (nwState net (pDst p)) = eTerm e -> wonElection (dedup name_eq_dec (pSrc p :: votesReceived (nwState net (pDst p)))) = true -> type (nwState net (pDst p)) <> Candidate.
Instance lsi : leader_sublog_interface.
Proof.
split.
auto using leader_sublog_invariant_invariant.
End LeaderSublogProof.

Lemma leader_sublog_request_vote : raft_net_invariant_request_vote leader_sublog_invariant.
Proof using.
unfold raft_net_invariant_request_vote.
intros.
unfold leader_sublog_invariant, leader_sublog_nw_invariant, leader_sublog_host_invariant, handleRequestVote, advanceCurrentTerm in *.
intuition idtac; simpl in *.
-
repeat find_higher_order_rewrite; repeat break_match; repeat find_inversion; subst; simpl in *; intuition eauto; try solve_by_inversion.
-
Admitted.

Lemma candidate_entries_lowered' : forall net, CandidateEntries net -> votes_correct net -> cronies_correct net -> forall h h' e, In e (log (snd (nwState net h'))) -> CandidateEntriesLowered (deghost net) e h.
Proof using rri.
unfold CandidateEntriesLowered, CandidateEntries, votes_correct, cronies_correct.
intros.
break_and.
rewrite deghost_spec.
apply_prop_hyp candidateEntries_host_invariant In.
Admitted.

Lemma candidate_entries_lowered : forall net, raft_intermediate_reachable net -> forall h h' e, In e (log (nwState net h')) -> CandidateEntriesLowered net e h.
Proof using cci vci cei rri.
intros net H.
pattern net.
apply lower_prop; auto.
clear H net.
intros.
repeat match goal with | [ H : _ |- _ ] => rewrite deghost_spec in H end.
Admitted.

Lemma deghost_packet_exists : forall net p, In p (nwPackets (deghost net)) -> exists (q : packet (params := raft_refined_multi_params (raft_params := raft_params))), In q (nwPackets net) /\ p = deghost_packet q.
Proof using.
unfold deghost.
simpl.
intros.
do_in_map.
Admitted.

Lemma candidate_entries_lowered_rvr' : forall net, CandidateEntries net -> votes_correct net -> cronies_correct net -> forall p h e, In e (log (snd (nwState net h))) -> CandidateEntriesLowered_rvr (deghost net) e p.
Proof using rri.
unfold CandidateEntriesLowered_rvr, CandidateEntries.
intros.
break_and.
rewrite deghost_spec.
find_apply_lem_hyp deghost_packet_exists.
break_exists.
break_and.
subst.
apply_prop_hyp candidateEntries_host_invariant In.
Admitted.

Lemma candidate_entries_lowered_rvr : forall net, raft_intermediate_reachable net -> forall p h e, In e (log (nwState net h)) -> CandidateEntriesLowered_rvr net e p.
Proof using cci vci cei rri.
intros net H.
pattern net.
apply lower_prop; auto.
clear H net.
intros.
repeat match goal with | [ H : _ |- _ ] => rewrite deghost_spec in H end.
Admitted.

Lemma candidate_entries_lowered_nw' : forall net, CandidateEntries net -> votes_correct net -> cronies_correct net -> forall h p e t li pli plt es lc, pBody p = AppendEntries t li pli plt es lc -> In p (nwPackets (deghost net)) -> In e es -> CandidateEntriesLowered (deghost net) e h.
Proof using rri.
unfold CandidateEntriesLowered, CandidateEntries, votes_correct, cronies_correct.
intros.
break_and.
rewrite deghost_spec.
find_apply_lem_hyp deghost_packet_exists.
break_exists.
break_and.
subst.
eapply_prop_hyp candidateEntries_nw_invariant In; eauto.
unfold candidateEntries in *.
break_exists.
break_and.
match goal with | H : wonElection _ = _ |- _ => eapply wonElection_one_in_common in H; [|clear H; eauto] end.
break_exists.
break_and.
repeat match goal with | [ H : _ |- _ ] => rewrite deghost_spec in H end.
intro.
assert (h = x0).
{
eapply_prop one_vote_per_term; eapply_prop cronies_votes.
-
eapply_prop votes_received_cronies; eauto.
-
find_reverse_rewrite.
auto.
}
subst.
concludes.
Admitted.

Lemma candidate_entries_lowered_nw : forall net, raft_intermediate_reachable net -> forall h p e t li pli plt es lc, pBody p = AppendEntries t li pli plt es lc -> In p (nwPackets net) -> In e es -> CandidateEntriesLowered net e h.
Proof using cci vci cei rri.
intros net H.
pattern net.
apply lower_prop; auto.
clear H net.
intros.
repeat match goal with | [ H : _ |- _ ] => rewrite deghost_spec in H end.
Admitted.

Lemma candidate_entries_lowered_nw_rvr' : forall net, CandidateEntries net -> votes_correct net -> cronies_correct net -> forall p' p e t li pli plt es lc, pBody p = AppendEntries t li pli plt es lc -> In p (nwPackets (deghost net)) -> In e es -> CandidateEntriesLowered_rvr (deghost net) e p'.
Proof using rri.
unfold CandidateEntriesLowered_rvr, CandidateEntries, votes_correct, cronies_correct.
intros.
break_and.
rewrite deghost_spec.
find_apply_lem_hyp deghost_packet_exists.
find_apply_lem_hyp deghost_packet_exists.
break_exists.
break_and.
subst.
eapply_prop_hyp votes_nw pBody.
concludes.
eapply_prop_hyp candidateEntries_nw_invariant pBody; auto.
find_insterU.
conclude_using eauto.
unfold candidateEntries in *.
break_exists.
break_and.
match goal with | H : wonElection _ = _ |- _ => eapply wonElection_one_in_common in H; [|clear H; eauto] end.
break_exists.
break_and.
repeat match goal with | [ H : _ |- _ ] => rewrite deghost_spec in H end.
simpl in *.
break_or_hyp.
-
apply_prop_hyp cronies_votes In.
assert (pDst x = x1) by (eapply_prop one_vote_per_term; eauto).
subst.
auto.
-
intro.
assert (pDst x = x1).
{
eapply_prop one_vote_per_term; eapply_prop cronies_votes.
-
eapply_prop votes_received_cronies; eauto.
-
repeat find_reverse_rewrite.
auto.
}
subst.
concludes.
Admitted.

Lemma candidate_entries_lowered_nw_rvr : forall net, raft_intermediate_reachable net -> forall p' p e t li pli plt es lc, pBody p = AppendEntries t li pli plt es lc -> In p (nwPackets net) -> In e es -> CandidateEntriesLowered_rvr net e p'.
Proof using cci vci cei rri.
intros net H.
pattern net.
apply lower_prop; auto.
clear H net.
intros.
repeat match goal with | [ H : _ |- _ ] => rewrite deghost_spec in H end.
Admitted.

Lemma leader_sublog_do_generic_server : raft_net_invariant_do_generic_server leader_sublog_invariant.
Proof using.
unfold raft_net_invariant_do_generic_server.
intros.
unfold leader_sublog_invariant, leader_sublog_nw_invariant, leader_sublog_host_invariant, doGenericServer in *.
intuition idtac; simpl in *.
-
repeat find_higher_order_rewrite; repeat break_match; repeat find_inversion; use_applyEntries_spec; subst; simpl in *; intuition eauto; try solve_by_inversion.
-
Admitted.

Lemma leader_sublog_state_same_packet_subset : raft_net_invariant_state_same_packet_subset leader_sublog_invariant.
Proof using.
unfold raft_net_invariant_state_same_packet_subset.
intros.
unfold leader_sublog_invariant, leader_sublog_nw_invariant, leader_sublog_host_invariant in *.
Admitted.

Lemma leader_sublog_reboot : raft_net_invariant_reboot leader_sublog_invariant.
Proof using.
unfold raft_net_invariant_reboot.
intros.
unfold leader_sublog_invariant, leader_sublog_nw_invariant, leader_sublog_host_invariant, reboot in *.
intuition idtac.
-
repeat find_higher_order_rewrite.
simpl in *.
repeat break_match; subst; simpl in *; intuition eauto; discriminate.
-
repeat find_higher_order_rewrite.
simpl in *.
repeat find_rewrite.
Admitted.

Theorem leader_sublog_init : raft_net_invariant_init leader_sublog_invariant.
Proof using.
Admitted.

Theorem leader_sublog_invariant_invariant : forall net, raft_intermediate_reachable net -> leader_sublog_invariant net.
Proof using olpti cci vci cei rri.
intros.
eapply raft_net_invariant; eauto.
-
apply leader_sublog_init.
-
apply leader_sublog_client_request.
-
apply leader_sublog_timeout.
-
apply leader_sublog_append_entries.
-
apply leader_sublog_append_entries_reply.
-
apply leader_sublog_request_vote.
-
apply leader_sublog_request_vote_reply.
-
apply leader_sublog_do_leader.
-
apply leader_sublog_do_generic_server.
-
apply leader_sublog_state_same_packet_subset.
-
Admitted.

Instance lsi : leader_sublog_interface.
Proof.
split.
Admitted.

Lemma leader_sublog_request_vote_reply : raft_net_invariant_request_vote_reply leader_sublog_invariant.
Proof using cci vci cei rri.
unfold raft_net_invariant_request_vote_reply.
unfold leader_sublog_invariant, leader_sublog_nw_invariant, leader_sublog_host_invariant, handleRequestVoteReply, advanceCurrentTerm.
intuition idtac; simpl in *.
-
repeat find_higher_order_rewrite; repeat break_match; repeat find_inversion; subst; simpl in *; intuition eauto; try discriminate.
+
exfalso.
eapply candidate_entries_lowered; eauto.
+
rewrite dedup_not_in_cons in * by auto.
exfalso.
eapply candidate_entries_lowered_rvr; eauto.
do_bool.
find_rewrite.
f_equal.
omega.
-
repeat find_higher_order_rewrite; repeat break_match; repeat find_inversion; subst; simpl in *; intuition eauto; find_apply_hyp_hyp; intuition eauto; subst; try discriminate.
+
exfalso.
eapply candidate_entries_lowered_nw; eauto.
+
rewrite dedup_not_in_cons in * by auto.
exfalso.
eapply candidate_entries_lowered_nw_rvr; eauto.
do_bool.
find_rewrite.
f_equal.
omega.
