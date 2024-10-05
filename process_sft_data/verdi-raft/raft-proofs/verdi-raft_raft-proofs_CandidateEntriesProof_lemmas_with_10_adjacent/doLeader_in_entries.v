Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.CroniesTermInterface.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CandidateEntriesInterface.
Section CandidateEntriesProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cti : cronies_term_interface}.
Context {tsi : term_sanity_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Ltac prove_in := match goal with | [ _ : nwPackets ?net = _, _ : In (?p : packet) _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition) | [ _ : nwPackets ?net = _, _ : pBody ?p = _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; intuition) end.
Instance cei : candidate_entries_interface.
Proof.
split.
auto using candidate_entries_invariant.
End CandidateEntriesProof.

Lemma handleAppendEntriesReply_spec : forall h st h' t es r st' ms, handleAppendEntriesReply h st h' t es r = (st', ms) -> log st' = log st /\ ((currentTerm st' = currentTerm st /\ type st' = type st) \/ type st' = Follower) /\ (forall m, In m ms -> ~ is_append_entries (snd m)).
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Lemma handleAppendEntriesReply_preserves_candidate_entries : forall net h h' t es r st' ms e, handleAppendEntriesReply h (snd (nwState net h)) h' t es r = (st', ms) -> refined_raft_intermediate_reachable net -> candidateEntries e (nwState net) -> candidateEntries e (update name_eq_dec (nwState net) h (fst (nwState net h), st')).
Proof using.
unfold candidateEntries.
intros.
break_exists.
break_and.
exists x.
split.
-
rewrite update_fun_comm.
simpl.
rewrite update_fun_comm.
simpl.
update_destruct; subst; rewrite_update; auto.
-
intros.
update_destruct; subst; rewrite_update; auto.
simpl in *.
find_apply_lem_hyp handleAppendEntriesReply_spec.
intuition; repeat find_rewrite; intuition.
Admitted.

Lemma candidate_entries_append_entries_reply : refined_raft_net_invariant_append_entries_reply CandidateEntries.
Proof using.
red.
unfold CandidateEntries.
intros.
intuition.
-
unfold candidateEntries_host_invariant in *.
intros.
simpl in *.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
find_rewrite_lem update_fun_comm.
simpl in *.
update_destruct.
+
subst.
rewrite_update.
unfold candidateEntries in *.
find_apply_lem_hyp handleAppendEntriesReply_spec.
break_and.
repeat find_rewrite.
find_apply_hyp_hyp.
break_exists; exists x; eauto.
update_destruct; intuition; subst; rewrite_update; simpl in *; auto; repeat find_rewrite; intuition; congruence.
+
rewrite_update.
find_apply_hyp_hyp.
eauto using handleAppendEntriesReply_preserves_candidate_entries.
-
unfold candidateEntries_nw_invariant in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
+
prove_in.
eapply candidateEntries_ext; eauto.
find_eapply_lem_hyp handleAppendEntriesReply_preserves_candidate_entries; eauto.
subst.
auto.
+
exfalso.
do_in_map.
find_eapply_lem_hyp handleAppendEntriesReply_spec; eauto.
subst.
simpl in *.
find_rewrite.
match goal with | H : ~ is_append_entries _ |- _ => apply H end.
Admitted.

Lemma update_elections_data_requestVote_cronies_same : forall h h' t lli llt st, cronies (update_elections_data_requestVote h h' t h' lli llt st) = cronies (fst st).
Proof using.
unfold update_elections_data_requestVote.
intros.
Admitted.

Lemma advanceCurrentTerm_same_or_type_follower : forall st t, advanceCurrentTerm st t = st \/ type (advanceCurrentTerm st t) = Follower.
Proof using.
unfold advanceCurrentTerm.
intros.
Admitted.

Lemma handleRV_advanceCurrentTerm_preserves_candidateEntries : forall net h h' t lli llt e, candidateEntries e (nwState net) -> candidateEntries e (update name_eq_dec (nwState net) h (update_elections_data_requestVote h h' t h' lli llt (nwState net h), advanceCurrentTerm (snd (nwState net h)) t)).
Proof using.
intros.
unfold candidateEntries in *.
break_exists.
break_and.
exists x.
split; update_destruct; subst; rewrite_update; auto; simpl.
+
rewrite update_elections_data_requestVote_cronies_same.
auto.
+
intros.
match goal with | [ |- context [advanceCurrentTerm ?st ?t] ] => pose proof advanceCurrentTerm_same_or_type_follower st t end.
intuition; try congruence.
repeat find_rewrite.
Admitted.

Lemma handleRequestVote_preserves_candidateEntries : forall net h h' t lli llt d e m, handleRequestVote h (snd (nwState net h)) t h' lli llt = (d, m) -> candidateEntries e (nwState net) -> candidateEntries e (update name_eq_dec (nwState net) h (update_elections_data_requestVote h h' t h' lli llt (nwState net h), d)).
Proof using.
unfold handleRequestVote.
intros.
repeat break_match; repeat find_inversion; auto using handleRV_advanceCurrentTerm_preserves_candidateEntries.
-
eapply candidateEntries_same; eauto; intros; repeat (rewrite update_fun_comm; simpl in * ); update_destruct; subst; rewrite_update; auto using update_elections_data_requestVote_cronies_same.
-
do_bool.
intuition.
congruence.
-
unfold candidateEntries in *.
break_exists.
break_and.
exists x.
simpl.
split.
+
rewrite update_fun_comm with (f := fst).
simpl.
rewrite update_fun_comm with (f := cronies).
simpl.
rewrite update_elections_data_requestVote_cronies_same.
update_destruct; subst; rewrite_update; auto.
+
rewrite update_fun_comm with (f := snd).
simpl.
rewrite update_fun_comm with (f := currentTerm).
simpl.
rewrite update_fun_comm with (f := type).
simpl.
update_destruct; subst; rewrite_update; auto.
match goal with | [ |- context [advanceCurrentTerm ?st ?t] ] => pose proof advanceCurrentTerm_same_or_type_follower st t end.
intuition; try congruence.
repeat find_rewrite.
Admitted.

Lemma handleRequestVote_only_sends_RVR : forall d h h' t lli llt d' m, handleRequestVote h d t h' lli llt = (d', m) -> is_request_vote_reply m.
Proof using.
unfold handleRequestVote.
intros.
Admitted.

Lemma candidate_entries_request_vote : refined_raft_net_invariant_request_vote CandidateEntries.
Proof using.
red.
unfold CandidateEntries.
intros.
subst.
intuition; simpl in *.
-
unfold candidateEntries_host_invariant in *.
intros.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
find_rewrite_lem update_fun_comm.
simpl in *.
update_destruct; subst; rewrite_update; simpl in *; try find_erewrite_lem handleRequestVote_same_log; eapply handleRequestVote_preserves_candidateEntries; eauto.
-
unfold candidateEntries_nw_invariant in *.
intros.
simpl in *.
eapply candidateEntries_ext; eauto.
find_apply_hyp_hyp.
intuition.
+
eauto using handleRequestVote_preserves_candidateEntries.
+
subst.
simpl in *.
find_apply_lem_hyp handleRequestVote_only_sends_RVR.
subst.
break_exists.
Admitted.

Lemma candidate_entries_request_vote_reply : refined_raft_net_invariant_request_vote_reply CandidateEntries.
Proof using cci.
red.
unfold CandidateEntries.
intros.
intuition.
-
unfold candidateEntries_host_invariant in *.
intros.
simpl in *.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
find_rewrite_lem update_fun_comm.
simpl in *.
update_destruct.
+
subst.
rewrite_update.
match goal with | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?r] => remember (handleRequestVoteReply h st h' t r) as new_state end.
find_copy_apply_lem_hyp handleRequestVoteReply_spec.
break_and.
match goal with | H : log _ = log _ |- _ => rewrite H in * end.
find_apply_hyp_hyp.
eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
+
rewrite_update.
eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
-
unfold candidateEntries_nw_invariant in *.
intros.
simpl in *.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
Admitted.

Lemma candidate_entries_do_leader : refined_raft_net_invariant_do_leader CandidateEntries.
Proof using.
red.
unfold CandidateEntries.
intros.
intuition; simpl in *.
-
unfold candidateEntries_host_invariant in *.
intros.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update.
+
simpl in *.
find_erewrite_lem doLeader_same_log.
repeat match goal with | [ H : nwState ?net ?h = (_, ?d), H' : context [ log ?d ] |- _ ] => replace (log d) with (log (snd (nwState net h))) in H' by (repeat find_rewrite; auto) end.
eauto using doLeader_preserves_candidateEntries.
+
eauto using doLeader_preserves_candidateEntries.
-
unfold candidateEntries_nw_invariant in *.
intros.
simpl in *.
eapply candidateEntries_ext; eauto.
find_apply_hyp_hyp.
intuition.
+
eauto using doLeader_preserves_candidateEntries.
+
do_in_map.
subst.
simpl in *.
eapply doLeader_preserves_candidateEntries; eauto.
eapply_prop candidateEntries_host_invariant.
match goal with | [ H : _ |- _ ] => rewrite H end.
simpl.
Admitted.

Lemma doGenericServer_same_type : forall h d os d' ms, doGenericServer h d = (os, d', ms) -> type d' = type d.
Proof using.
unfold doGenericServer.
intros.
Admitted.

Lemma doGenericServer_spec : forall h d os d' ms, doGenericServer h d = (os, d', ms) -> (log d' = log d /\ currentTerm d' = currentTerm d /\ (forall m, In m ms -> ~ is_append_entries (snd m))).
Proof using.
intros.
unfold doGenericServer in *.
Admitted.

Lemma doGenericServer_preserves_candidateEntries : forall net gd d h os d' ms e, nwState net h = (gd, d) -> doGenericServer h d = (os, d', ms) -> candidateEntries e (nwState net) -> candidateEntries e (update name_eq_dec (nwState net) h (gd, d')).
Proof using.
intros.
eapply candidateEntries_same; eauto; intros; repeat (rewrite update_fun_comm; simpl in * ); update_destruct; subst; rewrite_update; auto; repeat find_rewrite; simpl; auto.
-
find_copy_apply_lem_hyp doGenericServer_spec.
break_and.
auto.
-
Admitted.

Lemma candidate_entries_do_generic_server : refined_raft_net_invariant_do_generic_server CandidateEntries.
Proof using.
red.
unfold CandidateEntries.
intros.
intuition; simpl in *.
-
unfold candidateEntries_host_invariant in *.
intros.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update.
+
simpl in *.
find_copy_apply_lem_hyp doGenericServer_spec.
break_and.
find_rewrite.
repeat match goal with | [ H : nwState ?net ?h = (_, ?d), H' : context [ log ?d ] |- _ ] => replace (log d) with (log (snd (nwState net h))) in H' by (repeat find_rewrite; auto) end.
eauto using doGenericServer_preserves_candidateEntries.
+
eauto using doGenericServer_preserves_candidateEntries.
-
unfold candidateEntries_nw_invariant in *.
intros.
simpl in *.
eapply candidateEntries_ext; eauto.
find_apply_hyp_hyp.
intuition.
+
eauto using doGenericServer_preserves_candidateEntries.
+
do_in_map.
find_copy_apply_lem_hyp doGenericServer_spec.
break_and.
subst.
simpl in *.
find_apply_hyp_hyp.
exfalso.
find_rewrite.
Admitted.

Lemma candidate_entries_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset CandidateEntries.
Proof using.
red.
unfold CandidateEntries.
intros.
intuition.
-
unfold candidateEntries_host_invariant in *.
intros.
repeat find_reverse_higher_order_rewrite.
apply candidateEntries_ext with (sigma := nwState net); eauto.
-
unfold candidateEntries_nw_invariant in *.
intros.
find_apply_hyp_hyp.
eapply_prop_hyp In In; eauto.
Admitted.

Lemma reboot_log_same : forall d, log (reboot d) = log d.
Proof using.
unfold reboot.
Admitted.

Lemma reboot_preservers_candidateEntries : forall net h d gd e, nwState net h = (gd, d) -> candidateEntries e (nwState net) -> candidateEntries e (update name_eq_dec (nwState net) h (gd, reboot d)).
Proof using.
unfold reboot, candidateEntries.
intros.
break_exists.
exists x.
break_and.
rewrite update_fun_comm.
simpl in *.
update_destruct; subst; rewrite_update; auto.
repeat find_rewrite.
simpl in *.
intuition.
Admitted.

Lemma candidate_entries_reboot : refined_raft_net_invariant_reboot CandidateEntries.
Proof using.
red.
unfold CandidateEntries.
intros.
intuition.
-
unfold candidateEntries_host_invariant in *.
intros.
repeat find_higher_order_rewrite.
eapply candidateEntries_ext; eauto.
subst.
find_rewrite_lem update_fun_comm.
simpl in *.
find_rewrite_lem update_fun_comm.
simpl in *.
update_destruct; subst; rewrite_update.
+
repeat match goal with | [ H : nwState ?net ?h = (_, ?d), H' : context [ log ?d ] |- _ ] => replace (log d) with (log (snd (nwState net h))) in H' by (repeat find_rewrite; auto) end.
find_apply_hyp_hyp.
eauto using reboot_preservers_candidateEntries.
+
eauto using reboot_preservers_candidateEntries.
-
unfold candidateEntries_nw_invariant in *.
intros.
repeat find_reverse_rewrite.
eapply_prop_hyp In In; eauto.
eapply candidateEntries_ext; eauto.
Admitted.

Lemma candidate_entries_init : refined_raft_net_invariant_init CandidateEntries.
Proof using.
red.
unfold CandidateEntries.
unfold candidateEntries_host_invariant, candidateEntries_nw_invariant.
Admitted.

Lemma doLeader_in_entries : forall (h : name) d h os d' ms m t li pli plt es ci e, doLeader d h = (os, d', ms) -> snd m = AppendEntries t li pli plt es ci -> In m ms -> In e es -> In e (log d).
Proof using.
unfold doLeader.
intros.
repeat break_match; repeat find_inversion; simpl in *; intuition.
do_in_map.
unfold replicaMessage in *.
simpl in *.
subst.
simpl in *.
find_inversion.
eauto using findGtIndex_in.
