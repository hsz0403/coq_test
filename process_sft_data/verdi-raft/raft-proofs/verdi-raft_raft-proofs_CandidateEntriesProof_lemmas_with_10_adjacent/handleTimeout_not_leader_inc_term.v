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

Lemma handleClientRequest_spec : forall h d client id c out d' l, handleClientRequest h d client id c = (out, d', l) -> currentTerm d' = currentTerm d /\ type d' = type d /\ l = [] /\ (forall e, In e (log d') -> (In e (log d) \/ (e = (mkEntry h client id (S (maxIndex (log d))) (currentTerm d) c) /\ log d' = e :: log d /\ type d' = Leader))).
Proof using.
intros.
unfold handleClientRequest in *.
break_match; find_inversion; intuition.
simpl in *.
intuition.
subst.
Admitted.

Lemma candidate_entries_client_request : refined_raft_net_invariant_client_request CandidateEntries.
Proof using cci.
unfold refined_raft_net_invariant_client_request, CandidateEntries.
intros.
subst.
intuition.
-
unfold candidateEntries_host_invariant in *.
intros; simpl in *.
eapply candidateEntries_ext; try eassumption.
repeat find_higher_order_rewrite.
unfold update_elections_data_client_request in *.
repeat break_let.
simpl in *.
destruct (name_eq_dec h0 h); subst.
+
rewrite_update.
unfold update_elections_data_client_request in *.
repeat break_let.
simpl in *.
simpl in *.
find_inversion.
find_apply_lem_hyp handleClientRequest_spec; intuition eauto.
find_apply_hyp_hyp.
intuition.
*
rewrite_update.
eapply candidateEntries_same; eauto; intuition; destruct (name_eq_dec h0 h); subst; rewrite_update; auto.
repeat break_match; simpl; auto.
*
find_apply_lem_hyp cronies_correct_invariant.
unfold candidateEntries.
exists h.
intuition; rewrite_update; simpl in *; try congruence.
repeat find_rewrite.
simpl in *.
repeat break_match; simpl; eauto using won_election_cronies.
+
rewrite_update.
find_apply_lem_hyp handleClientRequest_spec.
eapply candidateEntries_same; eauto; intuition; destruct (name_eq_dec h1 h); subst; rewrite_update; auto; tuple_inversion; repeat find_rewrite; repeat break_match; simpl; auto.
-
unfold candidateEntries_nw_invariant in *.
intros.
simpl in *.
eapply candidateEntries_ext; try eassumption.
find_apply_lem_hyp handleClientRequest_spec.
intuition.
subst.
simpl in *.
eapply_prop_hyp candidateEntries AppendEntries; eauto.
+
eapply candidateEntries_same; eauto; intuition; destruct (name_eq_dec h h0); subst; rewrite_update; auto.
unfold update_elections_data_client_request; repeat break_match; simpl; auto.
+
find_apply_hyp_hyp.
Admitted.

Lemma update_elections_data_timeout_leader_cronies_same : forall sigma h, type (snd (sigma h)) = Leader -> cronies (update_elections_data_timeout h (sigma h)) = cronies (fst (sigma h)).
Proof using.
unfold update_elections_data_timeout.
intros.
repeat break_match; subst; simpl in *; auto.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Lemma handleTimeout_only_sends_RequestVotes : forall h d out d' l p, handleTimeout h d = (out, d', l) -> In p l -> exists t h' maxi maxt, snd p = RequestVote t h' maxi maxt.
Proof using.
unfold handleTimeout, tryToBecomeLeader.
intros.
Admitted.

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

Lemma handleTimeout_not_leader_inc_term : forall h d out d' l, handleTimeout h d = (out, d', l) -> type d <> Leader -> currentTerm d' = S (currentTerm d).
Proof using.
unfold handleTimeout, tryToBecomeLeader.
intros.
simpl in *.
repeat break_match; try congruence; repeat find_inversion; auto.
