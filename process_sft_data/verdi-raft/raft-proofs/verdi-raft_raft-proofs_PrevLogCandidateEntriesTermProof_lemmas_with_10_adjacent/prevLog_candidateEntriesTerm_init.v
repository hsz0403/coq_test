Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CroniesTermInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.RefinementCommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.PrevLogCandidateEntriesTermInterface.
Section PrevLogCandidateEntriesTerm.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cei : candidate_entries_interface}.
Context {cti : cronies_term_interface}.
Context {cci : cronies_correct_interface}.
Instance plceti : prevLog_candidateEntriesTerm_interface.
Proof.
constructor.
apply prevLog_candidateEntriesTerm_invariant.
End PrevLogCandidateEntriesTerm.

Lemma candidateEntriesTerm_ext : forall t sigma sigma', (forall h, sigma' h = sigma h) -> candidateEntriesTerm t sigma -> candidateEntriesTerm t sigma'.
Proof using.
unfold candidateEntriesTerm.
intros.
break_exists_exists.
repeat find_higher_order_rewrite.
Admitted.

Lemma candidateEntriesTerm_same : forall st st' t, candidateEntriesTerm t st -> (forall h, cronies (fst (st' h)) = cronies (fst (st h))) -> (forall h, currentTerm (snd (st' h)) = currentTerm (snd (st h))) -> (forall h, type (snd (st' h)) = type (snd (st h))) -> candidateEntriesTerm t st'.
Proof using.
unfold candidateEntriesTerm.
intros.
break_exists_exists.
repeat find_higher_order_rewrite.
Admitted.

Lemma prevLog_candidateEntriesTerm_client_request : refined_raft_net_invariant_client_request prevLog_candidateEntriesTerm.
Proof using.
unfold refined_raft_net_invariant_client_request, prevLog_candidateEntriesTerm.
simpl.
intros.
find_apply_hyp_hyp.
break_or_hyp.
-
eapply candidateEntriesTerm_ext; eauto.
eapply candidateEntriesTerm_same; eauto; intros; update_destruct_simplify; auto.
+
now erewrite update_elections_data_client_request_cronies by eauto.
+
find_apply_lem_hyp handleClientRequest_type.
intuition.
+
find_apply_lem_hyp handleClientRequest_type.
intuition.
-
find_apply_lem_hyp in_map_iff.
break_exists.
break_and.
subst.
simpl in *.
exfalso.
eapply handleClientRequest_no_append_entries; eauto.
find_rewrite.
Admitted.

Lemma update_elections_data_timeout_cronies : forall h d out d' l t, handleTimeout h (snd d) = (out, d', l) -> cronies (update_elections_data_timeout h d) t = cronies (fst d) t \/ (t = currentTerm d' /\ type d' = Candidate /\ cronies (update_elections_data_timeout h d) t = votesReceived d').
Proof using.
unfold update_elections_data_timeout.
intros.
repeat break_match; repeat find_inversion; simpl; auto.
Admitted.

Lemma handleClientRequest_preserves_candidateEntriesTerm: forall net h d t out l, refined_raft_intermediate_reachable net -> handleTimeout h (snd (nwState net h)) = (out, d, l) -> candidateEntriesTerm t (nwState net) -> candidateEntriesTerm t (update name_eq_dec (nwState net) h (update_elections_data_timeout h (nwState net h), d)).
Proof using cti.
unfold candidateEntriesTerm.
intros.
break_exists_exists.
break_and.
match goal with | [ H : handleTimeout _ _ = _ |- _ ] => pose proof H; eapply update_elections_data_timeout_cronies with (t := t) in H end.
break_or_hyp.
-
update_destruct_simplify; auto.
find_copy_apply_lem_hyp handleTimeout_type_strong.
intuition; repeat find_rewrite; auto.
find_apply_lem_hyp wonElection_exists_voter.
break_exists.
find_apply_lem_hyp in_dedup_was_in.
find_copy_apply_lem_hyp cronies_term_invariant; auto.
simpl in *.
omega.
-
update_destruct_simplify; auto.
find_copy_apply_lem_hyp handleTimeout_type_strong.
find_apply_lem_hyp wonElection_exists_voter.
break_exists.
find_apply_lem_hyp in_dedup_was_in.
find_copy_apply_lem_hyp cronies_term_invariant; auto.
Admitted.

Lemma prevLog_candidateEntriesTerm_timeout : refined_raft_net_invariant_timeout prevLog_candidateEntriesTerm.
Proof using cti.
unfold refined_raft_net_invariant_timeout, prevLog_candidateEntriesTerm.
simpl.
intros.
find_apply_hyp_hyp.
break_or_hyp.
-
eapply candidateEntriesTerm_ext; eauto.
eapply handleClientRequest_preserves_candidateEntriesTerm; eauto.
-
find_apply_lem_hyp in_map_iff.
break_exists.
break_and.
subst.
simpl in *.
exfalso.
eapply handleTimeout_not_is_append_entries; eauto.
find_rewrite.
Admitted.

Lemma handleAppendEntries_preserves_candidateEntriesTerm : forall net h t n pli plt es ci d m t', handleAppendEntries h (snd (nwState net h)) t n pli plt es ci = (d, m) -> refined_raft_intermediate_reachable net -> candidateEntriesTerm t' (nwState net) -> candidateEntriesTerm t' (update name_eq_dec (nwState net) h (update_elections_data_appendEntries h (nwState net h) t n pli plt es ci, d)).
Proof using.
unfold candidateEntriesTerm.
intros.
break_exists_exists.
break_and.
update_destruct_simplify.
-
rewrite update_elections_data_appendEntries_cronies.
find_apply_lem_hyp handleAppendEntries_type.
intuition; subst; repeat find_rewrite; auto.
discriminate.
-
Admitted.

Lemma prevLog_candidateEntriesTerm_append_entries : refined_raft_net_invariant_append_entries prevLog_candidateEntriesTerm.
Proof using.
unfold refined_raft_net_invariant_append_entries, prevLog_candidateEntriesTerm.
simpl.
intros.
find_apply_hyp_hyp.
break_or_hyp.
-
find_eapply_lem_hyp app_cons_in_rest; [|solve[eauto]].
eapply candidateEntriesTerm_ext; eauto.
eapply handleAppendEntries_preserves_candidateEntriesTerm; eauto.
-
exfalso.
eapply handleAppendEntries_not_append_entries; eauto.
simpl in *.
subst.
Admitted.

Lemma handleAppendEntriesReply_preserves_candidateEntriesTerm : forall net h h' t es r st' ms t', handleAppendEntriesReply h (snd (nwState net h)) h' t es r = (st', ms) -> refined_raft_intermediate_reachable net -> candidateEntriesTerm t' (nwState net) -> candidateEntriesTerm t' (update name_eq_dec (nwState net) h (fst (nwState net h), st')).
Proof using.
unfold candidateEntriesTerm.
intros.
break_exists_exists.
find_apply_lem_hyp handleAppendEntriesReply_type.
update_destruct_simplify.
-
intuition; repeat find_rewrite; auto.
discriminate.
-
Admitted.

Lemma prevLog_candidateEntriesTerm_append_entries_reply : refined_raft_net_invariant_append_entries_reply prevLog_candidateEntriesTerm.
Proof using.
unfold refined_raft_net_invariant_append_entries_reply, prevLog_candidateEntriesTerm.
simpl.
intros.
find_apply_hyp_hyp.
break_or_hyp.
-
find_eapply_lem_hyp app_cons_in_rest; [|solve[eauto]].
eapply candidateEntriesTerm_ext; eauto.
eauto using handleAppendEntriesReply_preserves_candidateEntriesTerm.
-
find_apply_lem_hyp in_map_iff.
break_exists.
break_and.
find_apply_lem_hyp handleAppendEntriesReply_packets.
subst.
simpl in *.
Admitted.

Lemma prevLog_candidateEntriesTerm_init : refined_raft_net_invariant_init prevLog_candidateEntriesTerm.
Proof using.
unfold refined_raft_net_invariant_init, prevLog_candidateEntriesTerm.
simpl.
intuition.
