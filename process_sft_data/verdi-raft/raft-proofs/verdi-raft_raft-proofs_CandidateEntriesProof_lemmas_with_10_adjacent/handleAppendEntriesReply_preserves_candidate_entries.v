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

Lemma update_elections_data_timeout_cronies : forall h d out d' l t, handleTimeout h (snd d) = (out, d', l) -> cronies (update_elections_data_timeout h d) t = cronies (fst d) t \/ (t = currentTerm d' /\ cronies (update_elections_data_timeout h d) t = votesReceived d').
Proof using.
unfold update_elections_data_timeout.
intros.
repeat break_match; repeat find_inversion; simpl; auto.
Admitted.

Lemma handleTimeout_preserves_candidateEntries : forall net h e out d l, refined_raft_intermediate_reachable net -> handleTimeout h (snd (nwState net h)) = (out, d, l) -> candidateEntries e (nwState net) -> candidateEntries e (update name_eq_dec (nwState net) h (update_elections_data_timeout h (nwState net h), d)).
Proof using cti.
intros.
destruct (serverType_eq_dec (type (snd (A:=electionsData) (B:=raft_data) (nwState net h))) Leader).
+
unfold handleTimeout, tryToBecomeLeader in *.
simpl in *.
find_rewrite.
find_inversion.
eapply candidateEntries_same; eauto; intros; repeat (rewrite update_fun_comm; simpl in * ); update_destruct; subst; rewrite_update; auto using update_elections_data_timeout_leader_cronies_same.
+
unfold candidateEntries in *.
break_exists.
break_and.
exists x.
rewrite update_fun_comm; simpl.
rewrite update_fun_comm; simpl.
rewrite update_fun_comm; simpl.
rewrite update_fun_comm; simpl.
rewrite update_fun_comm with (f := type); simpl.
update_destruct; subst; rewrite_update; auto.
split.
*
match goal with | [ H : handleTimeout _ _ = _ |- _ ] => pose proof H; apply update_elections_data_timeout_cronies with (t := eTerm e) in H end.
intuition; find_rewrite; auto.
find_apply_lem_hyp wonElection_exists_voter.
break_exists.
find_apply_lem_hyp in_dedup_was_in.
find_copy_apply_lem_hyp cronies_term_invariant; auto.
find_copy_apply_lem_hyp handleTimeout_not_leader_inc_term; auto.
simpl in *.
omega.
*
intros.
find_apply_lem_hyp wonElection_exists_voter.
break_exists.
find_apply_lem_hyp in_dedup_was_in.
find_copy_apply_lem_hyp cronies_term_invariant; auto.
find_copy_apply_lem_hyp handleTimeout_not_leader_inc_term; auto.
simpl in *.
Admitted.

Lemma candidate_entries_timeout : refined_raft_net_invariant_timeout CandidateEntries.
Proof using cti.
unfold refined_raft_net_invariant_timeout, CandidateEntries.
intros.
subst.
intuition; simpl in *.
-
unfold candidateEntries_host_invariant in *.
intros.
eapply candidateEntries_ext; try eassumption.
repeat find_higher_order_rewrite.
find_rewrite_lem update_fun_comm.
simpl in *.
find_rewrite_lem update_fun_comm.
simpl in *.
find_erewrite_lem handleTimeout_log_same.
find_rewrite_lem_by update_nop_ext' auto.
find_apply_hyp_hyp.
eauto using handleTimeout_preserves_candidateEntries.
-
unfold candidateEntries_nw_invariant in *.
intros.
simpl in *.
eapply candidateEntries_ext; eauto.
find_apply_hyp_hyp.
break_or_hyp.
+
eapply_prop_hyp pBody pBody; eauto.
eauto using handleTimeout_preserves_candidateEntries.
+
do_in_map.
subst.
simpl in *.
eapply handleTimeout_only_sends_RequestVotes in H8; eauto.
break_exists.
Admitted.

Lemma update_elections_data_appendEntries_cronies_same : forall h d t n pli plt es ci, cronies (update_elections_data_appendEntries h d t n pli plt es ci) = cronies (fst d).
Proof using.
unfold update_elections_data_appendEntries.
intros.
Admitted.

Lemma handleAppendEntries_spec : forall h st t n pli plt es ci st' m, handleAppendEntries h st t n pli plt es ci = (st', m) -> (currentTerm st <= currentTerm st' /\ (forall e, In e (log st') -> In e (log st) \/ In e es /\ currentTerm st' = t) /\ ~ is_append_entries m).
Proof using.
intros.
unfold handleAppendEntries, advanceCurrentTerm in *.
Admitted.

Lemma handleAppendEntries_term_same_or_type_follower : forall h t n pli plt es ci d m st, handleAppendEntries h st t n pli plt es ci = (d, m) -> (currentTerm d = currentTerm st /\ type d = type st) \/ type d = Follower.
Proof using.
unfold handleAppendEntries in *.
intros.
Admitted.

Lemma handleAppendEntries_preserves_candidate_entries : forall net h t n pli plt es ci d m e, handleAppendEntries h (snd (nwState net h)) t n pli plt es ci = (d, m) -> refined_raft_intermediate_reachable net -> candidateEntries e (nwState net) -> candidateEntries e (update name_eq_dec (nwState net) h (update_elections_data_appendEntries h (nwState net h) t n pli plt es ci, d)).
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
rewrite update_elections_data_appendEntries_cronies_same.
destruct (name_eq_dec x h); subst; rewrite_update; auto.
-
intros.
rewrite update_fun_comm.
simpl.
find_rewrite_lem update_fun_comm.
simpl in *.
destruct (name_eq_dec x h); subst; rewrite_update; auto.
find_apply_lem_hyp handleAppendEntries_term_same_or_type_follower.
Admitted.

Lemma is_append_entries_intro : forall t n plt pli es ci, is_append_entries (AppendEntries t n pli plt es ci).
Proof using.
Admitted.

Lemma candidate_entries_append_entries : refined_raft_net_invariant_append_entries CandidateEntries.
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
update_destruct; subst; rewrite_update; eapply handleAppendEntries_preserves_candidate_entries; eauto.
find_copy_apply_lem_hyp handleAppendEntries_spec.
break_and.
find_apply_hyp_hyp.
intuition eauto.
-
unfold candidateEntries_nw_invariant in *.
intros.
simpl in *.
eapply candidateEntries_ext; eauto.
find_apply_hyp_hyp.
intuition.
+
eapply handleAppendEntries_preserves_candidate_entries; eauto.
+
subst.
simpl in *.
find_apply_lem_hyp handleAppendEntries_spec.
break_and.
subst.
exfalso.
Admitted.

Lemma handleAppendEntriesReply_spec : forall h st h' t es r st' ms, handleAppendEntriesReply h st h' t es r = (st', ms) -> log st' = log st /\ ((currentTerm st' = currentTerm st /\ type st' = type st) \/ type st' = Follower) /\ (forall m, In m ms -> ~ is_append_entries (snd m)).
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
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
congruence.
