Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.CommitRecordedCommittedInterface.
Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.StateMachineSafetyPrimeInterface.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.MaxIndexSanityInterface.
Require Import VerdiRaft.LeaderCompletenessInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.PrevLogLeaderSublogInterface.
Require Import VerdiRaft.CurrentTermGtZeroInterface.
Require Import VerdiRaft.LastAppliedLeCommitIndexInterface.
Require Import VerdiRaft.MatchIndexAllEntriesInterface.
Require Import VerdiRaft.LeadersHaveLeaderLogsInterface.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.TermsAndIndicesFromOneLogInterface.
Require Import VerdiRaft.GhostLogCorrectInterface.
Require Import VerdiRaft.GhostLogsLogPropertiesInterface.
Require Import VerdiRaft.GhostLogLogMatchingInterface.
Require Import VerdiRaft.TransitiveCommitInterface.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.RaftMsgRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Section StateMachineSafetyProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {si : sorted_interface}.
Context {lmi : log_matching_interface}.
Context {smspi : state_machine_safety'interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Context {pllsi : prevLog_leader_sublog_interface}.
Context {ctgt0 : current_term_gt_zero_interface}.
Context {lalcii : lastApplied_le_commitIndex_interface}.
Context {miaei : match_index_all_entries_interface}.
Context {lhlli : leaders_have_leaderLogs_interface}.
Context {lci : leader_completeness_interface}.
Context {lsi : leader_sublog_interface}.
Context {taifoli : terms_and_indices_from_one_log_interface}.
Context {glci : ghost_log_correct_interface}.
Context {lphogli : log_properties_hold_on_ghost_logs_interface}.
Context {glemi : ghost_log_entries_match_interface}.
Context {tci : transitive_commit_interface}.
Context {tsi : term_sanity_interface}.
Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {rmri : raft_msg_refinement_interface}.
Definition ghost_log_network : Type := @network _ raft_msg_refined_multi_params.
Definition ghost_log_packet : Type := @packet _ raft_msg_refined_multi_params.
Definition lifted_maxIndex_sanity (net : ghost_log_network) : Prop := (forall h, lastApplied (snd (nwState net h)) <= maxIndex (log (snd (nwState net h)))) /\ (forall h, commitIndex (snd (nwState net h)) <= maxIndex (log (snd (nwState net h)))).
Definition lifted_no_entries_past_current_term_host net := forall (h : name) e, In e (log (snd (nwState net h))) -> eTerm e <= currentTerm (snd (nwState net h)).
Definition lifted_entries_contiguous (net : ghost_log_network) : Prop := forall h, contiguous_range_exact_lo (log (snd (nwState net h))) 0.
Definition lifted_entries_contiguous_nw (net : ghost_log_network) : Prop := forall p t n pli plt es ci, In p (nwPackets net) -> snd (pBody p) = AppendEntries t n pli plt es ci -> contiguous_range_exact_lo es pli.
Definition lifted_entries_gt_0 (net : ghost_log_network) : Prop := forall h e, In e (log (snd (nwState net h))) -> eIndex e > 0.
Definition lifted_directly_committed (net : ghost_log_network) (e : entry) : Prop := exists quorum, NoDup quorum /\ length quorum > div2 (length nodes) /\ (forall h, In h quorum -> In (eTerm e, e) (allEntries (fst (nwState net h)))).
Definition lifted_committed (net : ghost_log_network) (e : entry) (t : term) : Prop := exists h e', eTerm e' <= t /\ lifted_directly_committed net e' /\ eIndex e <= eIndex e' /\ In e (log (snd (nwState net h))) /\ In e' (log (snd (nwState net h))).
Definition commit_invariant_host (net : ghost_log_network) : Prop := forall h e, In e (log (snd (nwState net h))) -> eIndex e <= commitIndex (snd (nwState net h)) -> lifted_committed net e (currentTerm (snd (nwState net h))).
Definition commit_invariant_nw (net : ghost_log_network) : Prop := forall p t lid pli plt es lci e, In p (nwPackets net) -> snd (pBody p) = AppendEntries t lid pli plt es lci -> In e (fst (pBody p)) -> eIndex e <= lci -> lifted_committed net e t.
Definition commit_invariant (net : ghost_log_network) : Prop := commit_invariant_host net /\ commit_invariant_nw net.
Definition lifted_prevLog_leader_sublog (net : network) : Prop := forall leader p t leaderId prevLogIndex prevLogTerm entries leaderCommit, type (snd (nwState net leader)) = Leader -> In p (nwPackets net) -> snd (pBody p) = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit -> currentTerm (snd (nwState net leader)) = prevLogTerm -> 0 < prevLogIndex -> 0 < prevLogTerm -> exists ple, eIndex ple = prevLogIndex /\ eTerm ple = prevLogTerm /\ In ple (log (snd (nwState net leader))).
Definition lifted_state_machine_safety_nw' net := forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit e t', In p (nwPackets net) -> snd (pBody p) = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit -> lifted_committed net e t' -> t >= t' -> (prevLogIndex > eIndex e \/ (prevLogIndex = eIndex e /\ prevLogTerm = eTerm e) \/ eIndex e > maxIndex entries \/ In e entries).
Definition lifted_entries_gt_0_nw (net : ghost_log_network) : Prop := forall p t n pli plt es ci e, In p (nwPackets net) -> snd (pBody p) = AppendEntries t n pli plt es ci -> In e es -> eIndex e > 0.
Definition lifted_entries_sorted_nw' (net : ghost_log_network) := forall p t n pli plt es ci, In p (nwPackets net) -> snd (pBody p) = AppendEntries t n pli plt es ci -> sorted es.
Definition lifted_leaders_have_leaderLogs_strong (net : ghost_log_network) := forall h, type (snd (nwState net h)) = Leader -> exists ll es, In (currentTerm (snd (nwState net h)), ll) (leaderLogs (fst (nwState net h))) /\ log (snd (nwState net h)) = es ++ ll /\ (forall e : entry, In e es -> eTerm e = currentTerm (snd (nwState net h))).
Definition lifted_one_leaderLog_per_term (net : ghost_log_network) : Prop := forall h h' t ll ll', In (t, ll) (leaderLogs (fst (nwState net h))) -> In (t, ll') (leaderLogs (fst (nwState net h'))) -> h = h' /\ ll = ll'.
Definition lifted_leaders_have_leaderLogs (net : ghost_log_network) : Prop := forall h, type (snd (nwState net h)) = Leader -> exists ll, In (currentTerm (snd (nwState net h)), ll) (leaderLogs (fst (nwState net h))).
Definition lifted_leader_completeness_directly_committed (net : ghost_log_network) : Prop := forall t e log h, lifted_directly_committed net e -> t > eTerm e -> In (t, log) (leaderLogs (fst (nwState net h))) -> In e log.
Definition lifted_leader_completeness_committed (net : ghost_log_network) : Prop := forall t t' e log h, lifted_committed net e t -> t' > t -> In (t', log) (leaderLogs (fst (nwState net h))) -> In e log.
Definition lifted_leader_completeness (net : ghost_log_network) : Prop := lifted_leader_completeness_directly_committed net /\ lifted_leader_completeness_committed net.
Definition msg_lifted_leader_sublog_host (net : ghost_log_network) : Prop := forall leader e h, type (snd (nwState net leader)) = Leader -> In e (log (snd (nwState net h))) -> eTerm e = currentTerm (snd (nwState net leader)) -> In e (log (snd (nwState net leader))).
Definition everything (net : ghost_log_network) : Prop := lifted_maxIndex_sanity net /\ commit_invariant net /\ state_machine_safety (deghost (mgv_deghost net)).
Instance smsi : state_machine_safety_interface.
Proof.
split.
exact state_machine_safety_invariant.
Instance misi : max_index_sanity_interface.
Proof.
split.
exact maxIndex_sanity_invariant.
Instance crci : commit_recorded_committed_interface.
Proof.
split.
intros.
find_apply_lem_hyp commit_recorded_committed_invariant.
unfold commit_invariant, commit_recorded_committed, commit_recorded in *.
intros.
find_rewrite_lem (deghost_spec net h).
intuition; repeat match goal with | [ H : forall _, _, h : entry |- _ ] => specialize (H h) | [ H : forall _, _, h : Net.name |- _ ] => specialize (H h) end; repeat find_rewrite_lem deghost_spec; auto.
End StateMachineSafetyProof.

Lemma msg_deghost_spec' : forall base multi ghost (net : @network (@mgv_refined_base_params base) (@mgv_refined_multi_params base multi ghost)) h, nwState (mgv_deghost net) h = nwState net h.
Proof using.
unfold mgv_deghost.
intros.
simpl.
destruct net.
Admitted.

Lemma commit_invariant_lower_commit_recorded_committed : forall net : ghost_log_network, msg_refined_raft_intermediate_reachable net -> commit_invariant net -> commit_recorded_committed (mgv_deghost net).
Proof using rmri lalcii rri.
unfold commit_invariant, commit_recorded_committed, commit_recorded, commit_invariant_host.
intuition; repeat find_rewrite_lem deghost_spec; repeat find_rewrite_lem msg_deghost_spec'; rewrite msg_deghost_spec'; apply lifted_committed_committed; auto.
Admitted.

Lemma handleClientRequest_currentTerm : forall h st client id c out st' ms, handleClientRequest h st client id c = (out, st', ms) -> currentTerm st' = currentTerm st.
Proof using.
unfold handleClientRequest.
intros.
Admitted.

Lemma handleClientRequest_commitIndex : forall h st client id c out st' ms, handleClientRequest h st client id c = (out, st', ms) -> commitIndex st' = commitIndex st.
Proof using.
unfold handleClientRequest.
intros.
Admitted.

Lemma directly_committed_allEntries_preserved : forall net net' e, directly_committed net e -> (forall h, In (eTerm e, e) (allEntries (fst (nwState net h))) -> In (eTerm e, e) (allEntries (fst (nwState net' h)))) -> directly_committed net' e.
Proof using.
unfold directly_committed.
intuition.
break_exists_exists.
Admitted.

Lemma update_elections_data_client_request_allEntries : forall h st client id c out st' ms, handleClientRequest h (snd st) client id c = (out, st', ms) -> allEntries (update_elections_data_client_request h st client id c) = allEntries (fst st) \/ (exists e : entry, eIndex e = S (maxIndex (log (snd st))) /\ eTerm e = currentTerm (snd st) /\ eClient e = client /\ eInput e = c /\ eId e = id /\ type (snd st) = Leader /\ allEntries (update_elections_data_client_request h st client id c) = (currentTerm st', e) :: allEntries (fst st)).
Proof using.
intros.
unfold update_elections_data_client_request.
repeat break_match; repeat find_inversion; auto.
simpl.
find_copy_apply_lem_hyp handleClientRequest_log.
intuition.
-
repeat find_rewrite.
do_bool.
omega.
-
right.
break_exists_exists.
intuition.
Admitted.

Lemma update_elections_data_client_request_allEntries_ind : forall {h st client id c out st' ps}, handleClientRequest h (snd st) client id c = (out, st', ps) -> forall (P : list (term * entry) -> Prop), P (allEntries (fst st)) -> (forall e, eIndex e = S (maxIndex (log (snd st))) -> eTerm e = currentTerm (snd st) -> eClient e = client -> eInput e = c -> eId e = id -> type (snd st) = Leader -> P ((currentTerm st', e) :: allEntries (fst st))) -> P (allEntries (update_elections_data_client_request h st client id c)).
Proof using.
intros.
find_apply_lem_hyp update_elections_data_client_request_allEntries.
intuition.
-
find_rewrite.
auto.
-
break_exists.
intuition.
repeat find_rewrite.
Admitted.

Lemma update_elections_data_client_request_preserves_allEntries : forall h st client id c out st' ms t e, handleClientRequest h (snd st) client id c = (out, st', ms) -> In (t, e) (allEntries (fst st)) -> In (t, e) (allEntries (update_elections_data_client_request h st client id c)).
Proof using.
intros.
Admitted.

Lemma handleClientRequest_preservers_log : forall h st client id c out st' ms e, handleClientRequest h st client id c = (out, st', ms) -> In e (log st) -> In e (log st').
Proof using.
intros.
Admitted.

Lemma committed_log_allEntries_preserved : forall net net' e t, committed net e t -> (forall h e', In e' (log (snd (nwState net h))) -> In e' (log (snd (nwState net' h)))) -> (forall h e' t', In (t', e') (allEntries (fst (nwState net h))) -> In (t', e') (allEntries (fst (nwState net' h)))) -> committed net' e t.
Proof using.
unfold committed.
intros.
break_exists_exists.
intuition.
Admitted.

Lemma lift_max_index_sanity : forall (net : ghost_log_network) h, msg_refined_raft_intermediate_reachable net -> maxIndex_sanity (deghost (mgv_deghost net)) -> lastApplied (snd (nwState net h)) <= maxIndex (log (snd (nwState net h))) /\ commitIndex (snd (nwState net h)) <= maxIndex (log (snd (nwState net h))).
Proof using rmri rri.
intros.
match goal with | [ H : _, H' : _ |- _ ] => apply H in H'; clear H end.
unfold maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex in *.
break_and.
repeat match goal with | [ H : _ |- _ ] => specialize (H h) end.
repeat find_rewrite_lem deghost_spec.
repeat find_rewrite_lem msg_deghost_spec'.
Admitted.

Lemma haveNewEntries_log : forall es st st', log st = log st' -> haveNewEntries st es = true -> haveNewEntries st' es = true.
Proof using.
unfold haveNewEntries.
intros.
find_rewrite.
Admitted.

Lemma hCR_preserves_committed : forall (net net' : ghost_log_network) h client id c out d l e t, handleClientRequest h (snd (nwState net h)) client id c = (out, d, l) -> (forall h', nwState net' h' = update name_eq_dec (nwState net) h (update_elections_data_client_request h (nwState net h) client id c, d) h') -> lifted_committed net e t -> lifted_committed net' e t.
Proof using rmri.
intros.
eapply lifted_committed_log_allEntries_preserved; simpl; eauto.
-
intros.
find_higher_order_rewrite.
update_destruct_simplify; eauto using handleClientRequest_preservers_log.
-
intros.
find_higher_order_rewrite.
Admitted.

Lemma not_empty_intro : forall A (l : list A), l <> [] -> not_empty l = true.
Proof using.
unfold not_empty.
intros.
Admitted.

Lemma haveNewEntries_true_intro : forall st es, es <> [] -> (forall e, findAtIndex (log st) (maxIndex es) = Some e -> eTerm e <> maxTerm es) -> haveNewEntries st es = true.
Proof using.
unfold haveNewEntries.
intros.
do_bool.
split.
-
auto using not_empty_intro.
-
break_match; auto.
apply Bool.negb_true_iff.
do_bool.
Admitted.

Lemma prevLog_leader_sublog_lifted : forall net, msg_refined_raft_intermediate_reachable net -> lifted_prevLog_leader_sublog net.
Proof using rmri pllsi rri.
intros.
pose proof (msg_lift_prop _ (lift_prop _ prevLog_leader_sublog_invariant)).
find_insterU.
conclude_using eauto.
unfold prevLog_leader_sublog, lifted_prevLog_leader_sublog in *.
intros.
find_apply_lem_hyp in_mgv_ghost_packet.
find_apply_lem_hyp in_ghost_packet.
unfold deghost in *.
simpl in *.
break_match.
simpl in *.
subst.
specialize (H0 leader).
destruct (nwState leader).
simpl in *.
Admitted.

Lemma commit_invariant_client_request : forall h (net : ghost_log_network) st' ps' gd out d l client id c, handleClientRequest h (snd (nwState net h)) client id c = (out, d, l) -> gd = update_elections_data_client_request h (nwState net h) client id c -> commit_invariant net -> maxIndex_sanity (deghost (mgv_deghost net)) -> msg_refined_raft_intermediate_reachable net -> (forall h', st' h' = update name_eq_dec (nwState net) h (gd, d) h') -> (forall p', In p' ps' -> In p' (nwPackets net) \/ In p' (send_packets h (add_ghost_msg (msg_ghost_params := ghost_log_params) h (gd, d) l))) -> commit_invariant (mkNetwork ps' st').
Proof using rmri rri.
unfold msg_refined_raft_net_invariant_client_request, commit_invariant.
intros.
split.
-
{
unfold commit_invariant_host in *.
break_and.
unfold commit_recorded_committed, commit_recorded in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
rewrite update_fun_comm with (f := snd).
repeat match goal with H : _ |- _ => rewrite update_fun_comm with (f := snd) in H end.
simpl in *.
repeat match goal with | [H : _ |- _] => rewrite (update_fun_comm _ raft_data _) in H end.
rewrite (update_fun_comm _ raft_data).
rewrite update_nop_ext' by (now erewrite <- handleClientRequest_currentTerm by eauto).
match goal with | [H : _ |- _] => rewrite update_nop_ext' in H by (now erewrite <- handleClientRequest_commitIndex by eauto) end.
update_destruct_simplify.
-
find_copy_apply_lem_hyp handleClientRequest_log.
break_and.
break_or_hyp.
+
repeat find_rewrite.
eapply lifted_committed_log_allEntries_preserved; eauto.
*
simpl.
intros.
find_higher_order_rewrite.
update_destruct_simplify; repeat find_rewrite; auto.
*
simpl.
intros.
find_higher_order_rewrite.
update_destruct_simplify; eauto using update_elections_data_client_request_preserves_allEntries.
+
break_exists.
break_and.
repeat find_rewrite.
simpl in *.
match goal with | [ H : _ \/ In _ _ |- _ ] => invc H end.
*
find_eapply_lem_hyp (lift_max_index_sanity net h0); auto.
break_and.
simpl in *.
omega.
*
{
eapply lifted_committed_log_allEntries_preserved; eauto.
-
simpl.
intros.
find_higher_order_rewrite.
update_destruct_simplify; repeat find_rewrite; auto.
find_reverse_rewrite.
eapply handleClientRequest_preservers_log; eauto.
-
simpl.
intros.
find_higher_order_rewrite.
update_destruct_simplify; eauto using update_elections_data_client_request_preserves_allEntries.
}
-
eapply lifted_committed_log_allEntries_preserved; eauto.
+
simpl.
intros.
find_higher_order_rewrite.
update_destruct_simplify; repeat find_rewrite; eauto using handleClientRequest_preservers_log.
+
simpl.
intros.
find_higher_order_rewrite.
update_destruct_simplify; eauto using update_elections_data_client_request_preserves_allEntries.
}
-
unfold commit_invariant_nw in *.
simpl.
intros.
find_apply_hyp_hyp.
intuition.
+
eapply hCR_preserves_committed; eauto.
simpl.
subst.
auto.
+
unfold send_packets in *.
do_in_map.
unfold add_ghost_msg in *.
do_in_map.
subst.
simpl in *.
exfalso.
Admitted.

Lemma handleTimeout_preserves_committed : forall h (net net' : ghost_log_network) out d' l e t, handleTimeout h (snd (nwState net h)) = (out, d', l) -> (forall h', nwState net' h' = update name_eq_dec (nwState net) h (update_elections_data_timeout h (nwState net h), d') h') -> lifted_committed net e t -> lifted_committed net' e t.
Proof using rmri.
intros.
eapply lifted_committed_log_allEntries_preserved; eauto.
-
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
+
now erewrite handleTimeout_log_same by eauto.
+
auto.
-
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
+
now rewrite update_elections_data_timeout_allEntries.
+
Admitted.

Lemma lifted_committed_monotonic : forall net t t' e, lifted_committed net e t -> t <= t' -> lifted_committed net e t'.
Proof using.
unfold lifted_committed.
intros.
break_exists_exists.
Admitted.

Lemma commit_invariant_timeout : msg_refined_raft_net_invariant_timeout commit_invariant.
Proof using rmri.
unfold msg_refined_raft_net_invariant_timeout, commit_invariant.
simpl.
intuition.
-
unfold commit_invariant_host in *.
simpl.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
+
eapply handleTimeout_preserves_committed; eauto.
match goal with | [ H : context [commitIndex] |- _ ] => erewrite handleTimeout_commitIndex in H by eauto end.
match goal with | [ H : context [log] |- _ ] => erewrite handleTimeout_log_same in H by eauto end.
eapply lifted_committed_monotonic; [eauto|].
find_apply_lem_hyp handleTimeout_type_strong.
intuition; repeat find_rewrite; auto.
+
eapply handleTimeout_preserves_committed; eauto.
-
unfold commit_invariant_nw in *.
simpl.
intros.
find_apply_hyp_hyp.
intuition.
*
eapply handleTimeout_preserves_committed; eauto.
simpl.
intros.
subst.
auto.
*
do_in_map.
subst.
simpl in *.
unfold add_ghost_msg in *.
do_in_map.
subst.
simpl in *.
find_eapply_lem_hyp handleTimeout_packets; eauto.
exfalso.
Admitted.

Lemma lifted_committed_log_allEntries_preserved : forall net net' e t, lifted_committed net e t -> (forall h e', In e' (log (snd (nwState net h))) -> In e' (log (snd (nwState net' h)))) -> (forall h e' t', In (t', e') (allEntries (fst (nwState net h))) -> In (t', e') (allEntries (fst (nwState net' h)))) -> lifted_committed net' e t.
Proof using rmri.
intros.
find_apply_lem_hyp lifted_committed_committed.
find_eapply_lem_hyp committed_log_allEntries_preserved; eauto.
apply committed_lifted_committed.
eapply committed_log_allEntries_preserved; eauto; intros; repeat find_rewrite_lem msg_deghost_spec; rewrite msg_deghost_spec; auto.
