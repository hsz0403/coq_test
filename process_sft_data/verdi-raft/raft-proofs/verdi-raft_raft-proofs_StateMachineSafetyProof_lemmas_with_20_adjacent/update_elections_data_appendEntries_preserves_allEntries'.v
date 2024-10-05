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

Lemma lifted_committed_log_allEntries_preserved : forall net net' e t, lifted_committed net e t -> (forall h e', In e' (log (snd (nwState net h))) -> In e' (log (snd (nwState net' h)))) -> (forall h e' t', In (t', e') (allEntries (fst (nwState net h))) -> In (t', e') (allEntries (fst (nwState net' h)))) -> lifted_committed net' e t.
Proof using rmri.
intros.
find_apply_lem_hyp lifted_committed_committed.
find_eapply_lem_hyp committed_log_allEntries_preserved; eauto.
apply committed_lifted_committed.
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

Lemma committed_ext : forall ps st st' t e, (forall h, st' h = st h) -> committed (mkNetwork ps st) e t -> committed (mkNetwork ps st') e t.
Proof using.
unfold committed, directly_committed.
simpl.
intros.
break_exists_exists.
find_higher_order_rewrite.
intuition.
break_exists_exists.
intuition.
find_higher_order_rewrite.
Admitted.

Lemma lifted_committed_ext : forall ps st st' t e, (forall h, st' h = st h) -> lifted_committed (mkNetwork ps st) e t -> lifted_committed (mkNetwork ps st') e t.
Proof using rmri.
intros.
apply committed_lifted_committed.
find_apply_lem_hyp lifted_committed_committed.
unfold mgv_deghost in *.
Admitted.

Lemma lifted_state_machine_safety_nw'_invariant : forall (net : @network _ raft_msg_refined_multi_params), msg_refined_raft_intermediate_reachable net -> lifted_state_machine_safety_nw' net.
Proof using rmri smspi.
intros.
unfold lifted_state_machine_safety_nw'.
intros.
find_apply_lem_hyp lifted_committed_committed.
find_apply_lem_hyp in_mgv_ghost_packet.
match goal with | _ : snd (pBody ?p) = ?x |- _ => assert (pBody (@mgv_deghost_packet _ _ ghost_log_params p) = x) by (rewrite pBody_mgv_deghost_packet; auto) end.
eapply state_machine_safety'_invariant; eauto.
Admitted.

Lemma lifted_entries_sorted_nw : forall net p t n pli plt es ci, msg_refined_raft_intermediate_reachable net -> In p (nwPackets net) -> snd (pBody p) = AppendEntries t n pli plt es ci -> sorted es.
Proof using rmri rlmli.
intros.
find_apply_lem_hyp in_mgv_ghost_packet.
match goal with | _ : snd (pBody ?p) = ?x |- _ => assert (pBody (@mgv_deghost_packet _ _ ghost_log_params p) = x) by (rewrite pBody_mgv_deghost_packet; auto) end.
find_eapply_lem_hyp entries_sorted_nw_invariant; eauto.
Admitted.

Lemma lifted_transitive_commit_invariant : forall net h e e' t, msg_refined_raft_intermediate_reachable net -> In e (log (snd (nwState net h))) -> In e' (log (snd (nwState net h))) -> eIndex e <= eIndex e' -> lifted_committed net e' t -> lifted_committed net e t.
Proof using rmri tci.
intros.
apply committed_lifted_committed.
find_apply_lem_hyp lifted_committed_committed.
repeat match goal with | H : _ |- _ => rewrite <- msg_deghost_spec with (net0 := net) in H end.
eapply transitive_commit_invariant; eauto.
Admitted.

Lemma handleAppendEntries_preserves_commit : forall net net' h p t n pli plt es ci d m e t', msg_refined_raft_intermediate_reachable net -> In p (nwPackets net) -> snd (pBody p) = AppendEntries t n pli plt es ci -> handleAppendEntries h (snd (nwState net h)) t n pli plt es ci = (d, m) -> (forall h', nwState net' h' = update name_eq_dec (nwState net) h (update_elections_data_appendEntries h (nwState net h) t n pli plt es ci, d) h') -> lifted_committed net e t' -> lifted_committed net' e t'.
Proof using rmri tsi rlmli smspi si rri.
intros.
unfold lifted_committed in *.
break_exists_name host.
break_exists_name e'.
exists host, e'.
intuition.
-
unfold lifted_directly_committed in *.
break_exists_exists; intuition.
find_higher_order_rewrite.
update_destruct_simplify; eauto using update_elections_data_appendEntries_preserves_allEntries'.
-
find_higher_order_rewrite.
update_destruct_simplify; simpl in *; eauto.
assert (lifted_committed net e (currentTerm (snd (nwState net host)))) by (unfold lifted_committed; exists host, e'; intuition; eapply lifted_no_entries_past_current_term_host_invariant; eauto).
find_eapply_lem_hyp handleAppendEntries_log_detailed.
intuition; repeat find_rewrite; eauto.
+
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
assert (eIndex e > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
intuition; try omega.
find_copy_eapply_lem_hyp msg_lifted_sorted_host.
exfalso.
enough (exists e, eIndex e = (maxIndex es) /\ In e (log (snd (nwState net host)))) by (break_exists; intuition; eapply findAtIndex_None; eauto).
eapply contiguous_range_exact_lo_elim_exists; [apply lifted_entries_contiguous_invariant; auto|].
intuition.
*
find_apply_lem_hyp maxIndex_non_empty.
break_exists; intuition; repeat find_rewrite.
enough (eIndex x > 0) by omega.
eapply lifted_entries_contiguous_nw_invariant; eauto.
*
enough (eIndex e <= maxIndex (log (snd (nwState net host)))) by omega.
apply maxIndex_is_max; auto.
+
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
assert (eIndex e > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
intuition; try omega.
break_exists.
intuition.
find_apply_lem_hyp maxIndex_non_empty.
break_exists_name maxEntry; intuition.
repeat find_rewrite.
find_false.
f_equal.
find_apply_lem_hyp findAtIndex_elim.
intuition.
eapply uniqueIndices_elim_eq; [| |eauto|]; eauto using sorted_uniqueIndices,lifted_entries_sorted_nw.
match goal with | |- In ?e _ => assert (lifted_committed net e (currentTerm (snd (nwState net host)))) by (unfold lifted_committed; exists host, e'; intuition; eapply lifted_no_entries_past_current_term_host_invariant; eauto) end.
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
assert (eIndex x > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
intuition; omega.
+
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
intuition; try solve [apply in_app_iff; right; apply removeAfterIndex_le_In; auto; omega]; [idtac].
find_copy_eapply_lem_hyp msg_lifted_sorted_host.
exfalso.
enough (exists e, eIndex e = (maxIndex es) /\ In e (log (snd (nwState net host)))) by (break_exists; intuition; eapply findAtIndex_None; eauto).
eapply contiguous_range_exact_lo_elim_exists; [apply lifted_entries_contiguous_invariant; auto|].
intuition.
*
find_apply_lem_hyp maxIndex_non_empty.
break_exists; intuition; repeat find_rewrite.
enough (eIndex x0 > 0) by omega.
enough (eIndex x0 > pli) by omega.
eapply lifted_entries_contiguous_nw_invariant; eauto.
*
enough (eIndex e <= maxIndex (log (snd (nwState net host)))) by omega.
apply maxIndex_is_max; auto.
+
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
intuition; try solve [apply in_app_iff; right; apply removeAfterIndex_le_In; auto; omega]; [idtac].
break_exists.
intuition.
find_apply_lem_hyp maxIndex_non_empty.
break_exists_name maxEntry; intuition.
repeat find_rewrite.
find_false.
f_equal.
find_apply_lem_hyp findAtIndex_elim.
intuition.
eapply uniqueIndices_elim_eq; [| |eauto|]; eauto using sorted_uniqueIndices,lifted_entries_sorted_nw.
match goal with | |- In ?e _ => assert (lifted_committed net e (currentTerm (snd (nwState net host)))) by (unfold lifted_committed; exists host, e'; intuition; eapply lifted_no_entries_past_current_term_host_invariant; eauto) end.
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
intuition; try omega; enough (pli < eIndex maxEntry) by omega; eapply lifted_entries_contiguous_nw_invariant; eauto.
-
find_higher_order_rewrite.
update_destruct_simplify; simpl in *; eauto.
assert (lifted_committed net e' (currentTerm (snd (nwState net host)))) by (unfold lifted_committed; exists host, e'; intuition; eapply lifted_no_entries_past_current_term_host_invariant; eauto).
find_eapply_lem_hyp handleAppendEntries_log_detailed.
intuition; repeat find_rewrite; eauto.
+
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
assert (eIndex e' > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
intuition; try omega.
find_copy_eapply_lem_hyp msg_lifted_sorted_host.
exfalso.
enough (exists e, eIndex e = (maxIndex es) /\ In e (log (snd (nwState net host)))) by (break_exists; intuition; eapply findAtIndex_None; eauto).
eapply contiguous_range_exact_lo_elim_exists; [apply lifted_entries_contiguous_invariant; auto|].
intuition.
*
find_apply_lem_hyp maxIndex_non_empty.
break_exists; intuition; repeat find_rewrite.
enough (eIndex x > 0) by omega.
eapply lifted_entries_contiguous_nw_invariant; eauto.
*
enough (eIndex e' <= maxIndex (log (snd (nwState net host)))) by omega.
apply maxIndex_is_max; auto.
+
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
assert (eIndex e' > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
intuition; try omega.
break_exists.
intuition.
find_apply_lem_hyp maxIndex_non_empty.
break_exists_name maxEntry; intuition.
repeat find_rewrite.
find_false.
f_equal.
find_apply_lem_hyp findAtIndex_elim.
intuition.
eapply uniqueIndices_elim_eq; [| |eauto|]; eauto using sorted_uniqueIndices,lifted_entries_sorted_nw.
match goal with | |- In ?e _ => assert (lifted_committed net e (currentTerm (snd (nwState net host)))) by (unfold lifted_committed; exists host, e'; intuition; eapply lifted_no_entries_past_current_term_host_invariant; eauto) end.
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
assert (eIndex x > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
intuition; omega.
+
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
intuition; try solve [apply in_app_iff; right; apply removeAfterIndex_le_In; auto; omega]; [idtac].
find_copy_eapply_lem_hyp msg_lifted_sorted_host.
exfalso.
enough (exists e, eIndex e = (maxIndex es) /\ In e (log (snd (nwState net host)))) by (break_exists; intuition; eapply findAtIndex_None; eauto).
eapply contiguous_range_exact_lo_elim_exists; [apply lifted_entries_contiguous_invariant; auto|].
intuition.
*
find_apply_lem_hyp maxIndex_non_empty.
break_exists; intuition; repeat find_rewrite.
enough (eIndex x0 > 0) by omega.
enough (eIndex x0 > pli) by omega.
eapply lifted_entries_contiguous_nw_invariant; eauto.
*
enough (eIndex e' <= maxIndex (log (snd (nwState net host)))) by omega.
apply maxIndex_is_max; auto.
+
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
intuition; try solve [apply in_app_iff; right; apply removeAfterIndex_le_In; auto; omega]; [idtac].
break_exists.
intuition.
find_apply_lem_hyp maxIndex_non_empty.
break_exists_name maxEntry; intuition.
repeat find_rewrite.
find_false.
f_equal.
find_apply_lem_hyp findAtIndex_elim.
intuition.
eapply uniqueIndices_elim_eq; [| |eauto|]; eauto using sorted_uniqueIndices,lifted_entries_sorted_nw.
match goal with | |- In ?e _ => assert (lifted_committed net e (currentTerm (snd (nwState net host)))) by (unfold lifted_committed; exists host, e'; intuition; eapply lifted_no_entries_past_current_term_host_invariant; eauto) end.
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
Admitted.

Lemma handleAppendEntries_currentTerm_le : forall h st t n pli plt es ci st' m, handleAppendEntries h st t n pli plt es ci = (st', m) -> currentTerm st <= currentTerm st'.
Proof using.
intros.
unfold handleAppendEntries, advanceCurrentTerm in *.
Admitted.

Theorem handleAppendEntries_log_detailed : forall h st t n pli plt es ci st' ps, handleAppendEntries h st t n pli plt es ci = (st', ps) -> (commitIndex st' = commitIndex st /\ log st' = log st) \/ (leaderId st' <> None /\ currentTerm st' = t /\ commitIndex st' = max (commitIndex st) (min ci (maxIndex es)) /\ es <> nil /\ pli = 0 /\ t >= currentTerm st /\ log st' = es /\ haveNewEntries st es = true ) \/ (leaderId st' <> None /\ currentTerm st' = t /\ commitIndex st' = max (commitIndex st) (min ci (maxIndex (es ++ (removeAfterIndex (log st) pli)))) /\ es <> nil /\ exists e, In e (log st) /\ eIndex e = pli /\ eTerm e = plt) /\ t >= currentTerm st /\ log st' = es ++ (removeAfterIndex (log st) pli) /\ haveNewEntries st es = true.
Proof using.
intros.
unfold handleAppendEntries in *.
break_if; [find_inversion; subst; eauto|].
break_if; [do_bool; break_if; find_inversion; subst; try find_apply_lem_hyp haveNewEntries_true; simpl in *; intuition eauto using advanceCurrentTerm_log, advanceCurrentTerm_commitIndex, some_none, advanceCurrentTerm_term|].
simpl in *.
intuition eauto using advanceCurrentTerm_log, advanceCurrentTerm_commitIndex.
break_match; [|find_inversion; subst; eauto].
break_if; [find_inversion; subst; eauto|].
break_if; [|find_inversion; subst; eauto using advanceCurrentTerm_log, advanceCurrentTerm_commitIndex].
find_inversion; subst; simpl in *.
right.
right.
find_apply_lem_hyp findAtIndex_elim.
Admitted.

Lemma lifted_entries_gt_0_nw_invariant : forall net, msg_refined_raft_intermediate_reachable net -> lifted_entries_gt_0_nw net.
Proof using rmri rlmli.
unfold lifted_entries_gt_0_nw.
intros.
pose proof msg_lift_prop _ entries_gt_0_nw_invariant _ ltac:(eauto).
unfold entries_gt_0_nw in *.
find_apply_lem_hyp in_mgv_ghost_packet.
Admitted.

Lemma lifted_entries_sorted_nw'_invariant : forall net, msg_refined_raft_intermediate_reachable net -> lifted_entries_sorted_nw' net.
Proof using rmri rlmli.
intros.
pose proof msg_lift_prop _ entries_sorted_nw_invariant.
find_copy_apply_hyp_hyp.
unfold entries_sorted_nw, lifted_entries_sorted_nw' in *.
intros.
find_apply_lem_hyp in_mgv_ghost_packet.
Admitted.

Lemma commit_invariant_append_entries : forall xs p ys (net : ghost_log_network) st' ps' gd d m t n pli plt es ci, handleAppendEntries (pDst p) (snd (nwState net (pDst p))) t n pli plt es ci = (d, m) -> gd = update_elections_data_appendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci -> snd (pBody p) = AppendEntries t n pli plt es ci -> commit_invariant net -> msg_refined_raft_intermediate_reachable net -> lifted_maxIndex_sanity net -> nwPackets net = xs ++ p :: ys -> (forall h, st' h = update name_eq_dec (nwState net) (pDst p) (gd, d) h) -> (forall p', In p' ps' -> In p' (xs ++ ys) \/ p' = mkPacket (pDst p) (pSrc p) (write_ghost_log (pDst p) (gd, d), m)) -> commit_invariant (mkNetwork ps' st').
Proof using rmri tsi glemi lphogli glci rlmli smspi si rri.
unfold commit_invariant.
intros.
assert (In p (nwPackets net)) by (repeat find_rewrite; auto with *).
split.
-
break_and.
match goal with | [ H : commit_invariant_host _ |- _ ] => rename H into Hhost; unfold commit_invariant_host in * end.
simpl.
intros.
eapply lifted_committed_ext; eauto.
match goal with | [ H : forall _, _ = _ |- _ ] => rewrite H in * end.
update_destruct_simplify.
+
find_copy_apply_lem_hyp handleAppendEntries_log_detailed.
break_or_hyp.
*
break_and.
repeat find_rewrite.
eapply lifted_committed_monotonic; [ solve [eapply handleAppendEntries_preserves_commit; eauto] | solve [eauto using handleAppendEntries_currentTerm_le] ].
*
{
break_or_hyp; repeat break_and.
-
repeat match goal with | [ H : _ <= _, H': _ |- _ ] => rewrite H' in H end.
find_apply_lem_hyp NPeano.Nat.max_le.
break_or_hyp.
+
assert (eIndex e > 0) by (eapply lifted_entries_gt_0_nw_invariant; eauto).
assert (exists e', eIndex e' = eIndex e /\ In e' (log (snd (nwState net (pDst p))))).
{
eapply contiguous_range_exact_lo_elim_exists.
-
eapply lifted_entries_contiguous_invariant.
auto.
-
split.
+
auto.
+
eapply le_trans; [eauto|].
eapply_prop lifted_maxIndex_sanity.
}
break_exists_name e'.
break_and.
assert (lifted_committed net e' (currentTerm (snd (nwState net (pDst p))))) as He'committed by (apply Hhost; [auto|congruence]) .
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
concludes.
assert (sorted (log d)) by (eauto using lifted_handleAppendEntries_logs_sorted).
intuition.
*
omega.
*
omega.
*
match goal with | [ H : _ |- _ ] => eapply maxIndex_is_max in H; eauto; [idtac] end.
omega.
*
assert (e = e') by (eapply uniqueIndices_elim_eq; eauto using sorted_uniqueIndices).
subst.
eapply lifted_committed_monotonic; [ solve [eapply handleAppendEntries_preserves_commit; eauto] | solve [eauto using handleAppendEntries_currentTerm_le] ].
+
match goal with | [ H : commit_invariant_nw _ |- _ ] => rename H into Hnet; unfold commit_invariant_nw in * end.
eapply_prop_hyp In In; [| eauto | | eauto using Min.min_glb_l].
*
eapply handleAppendEntries_preserves_commit; eauto.
*
find_eapply_lem_hyp ghost_log_correct_invariant; eauto.
conclude_using eauto.
{
intuition.
-
match goal with | [ H : In _ _, H' : _ |- _ ] => rewrite H' in H end.
auto.
-
break_exists.
break_and.
pose proof log_properties_hold_on_ghost_logs_invariant _ ltac:(eauto) as Hprop.
unfold log_properties_hold_on_ghost_logs in *.
unfold msg_log_property in *.
specialize (Hprop (fun l => forall e, In e l -> eIndex e > 0) p).
conclude_using ltac:(intros; eapply lifted_entries_gt_0_invariant; eauto).
conclude_using eauto.
simpl in *.
find_apply_hyp_hyp.
omega.
}
-
break_exists_name ple.
break_and.
repeat match goal with | [ H : _ <= _, H': _ |- _ ] => rewrite H' in H end.
find_apply_lem_hyp NPeano.Nat.max_le.
break_or_hyp.
+
repeat find_rewrite.
match goal with | [ H : In e (_ ++ _) |- _ ] => apply in_app_or in H; destruct H end.
*
{
assert (eIndex e > 0) by (eapply lifted_entries_gt_0_nw_invariant; eauto).
assert (exists e', eIndex e' = eIndex e /\ In e' (log (snd (nwState net (pDst p))))).
{
eapply contiguous_range_exact_lo_elim_exists.
-
eapply lifted_entries_contiguous_invariant.
auto.
-
split.
+
auto.
+
eapply le_trans; [eauto|].
eapply_prop lifted_maxIndex_sanity.
}
break_exists_name e'.
break_and.
assert (lifted_committed net e' (currentTerm (snd (nwState net (pDst p))))) as He'committed by (apply Hhost; [auto|congruence]) .
find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
concludes.
assert (sorted es) by (eapply lifted_entries_sorted_nw'_invariant; eauto).
assert (contiguous_range_exact_lo es (eIndex ple)) by (eapply lifted_entries_contiguous_nw_invariant; eauto).
find_eapply_lem_hyp contiguous_range_exact_lo_elim_lt; eauto.
intuition.
*
omega.
*
omega.
*
match goal with | [ H : _ |- _ ] => eapply maxIndex_is_max in H; eauto with *; [idtac] end.
omega.
*
assert (e = e') by (eapply uniqueIndices_elim_eq; eauto using sorted_uniqueIndices).
subst.
eapply lifted_committed_monotonic; [ solve [eapply handleAppendEntries_preserves_commit; eauto] | solve [eauto using handleAppendEntries_currentTerm_le] ].
}
*
{
eapply lifted_committed_monotonic.
-
eapply handleAppendEntries_preserves_commit; eauto.
eapply Hhost with (h := pDst p); eauto using removeAfterIndex_in.
-
eauto using handleAppendEntries_currentTerm_le.
}
+
match goal with | [ H : In e _ |- _ ] => repeat match goal with | [ H' : _ |- _ ] => rewrite H' in H end; apply in_app_or in H; destruct H end.
*
{
match goal with | [ H : commit_invariant_nw _ |- _ ] => rename H into Hnet; unfold commit_invariant_nw in * end.
match goal with | [ H : In _ (nwPackets _), H' : _ |- _ ] => eapply H' in H end; [| eauto | | eauto using Min.min_glb_l].
*
eapply handleAppendEntries_preserves_commit; eauto.
*
find_copy_eapply_lem_hyp ghost_log_correct_invariant; eauto.
conclude_using eauto.
{
intuition.
-
match goal with | [ H : In _ _, H' : _ |- _ ] => rewrite H' in H end.
auto.
-
break_exists_name gple.
break_and.
subst.
eauto using findGtIndex_in.
}
}
*
assert (eIndex e <= eIndex ple) by (eapply removeAfterIndex_In_le; eauto using msg_lifted_sorted_host).
pose proof log_properties_hold_on_ghost_logs_invariant _ ltac:(eauto) as Hprop.
unfold log_properties_hold_on_ghost_logs in *.
unfold msg_log_property in *.
specialize (Hprop (fun l => contiguous_range_exact_lo l 0) p).
conclude_using ltac:(intros; eapply lifted_entries_contiguous_invariant; eauto).
concludes.
simpl in *.
find_copy_eapply_lem_hyp ghost_log_correct_invariant; eauto.
conclude_using eauto.
{
intuition.
-
subst.
find_apply_lem_hyp removeAfterIndex_in.
pose proof lifted_entries_gt_0_invariant _ ltac:(eauto) _ _ ltac:(eauto).
omega.
-
break_exists_name gple.
break_and.
assert (exists e', eIndex e' = eIndex e /\ In e' (fst (pBody p))).
{
eapply contiguous_range_exact_lo_elim_exists; eauto.
split.
+
eapply lifted_entries_gt_0_invariant; eauto using removeAfterIndex_in.
+
eapply le_trans with (m := eIndex gple); try omega.
apply maxIndex_is_max; auto.
pose proof log_properties_hold_on_ghost_logs_invariant _ ltac:(eauto) as Hsort.
unfold log_properties_hold_on_ghost_logs in *.
unfold msg_log_property in *.
specialize (Hsort sorted p msg_lifted_sorted_host).
auto.
}
break_exists_name e'.
break_and.
find_apply_lem_hyp removeAfterIndex_in.
assert (e = e').
{
eapply uniqueIndices_elim_eq; eauto using msg_lifted_sorted_host, sorted_uniqueIndices.
pose proof ghost_log_entries_match_invariant _ ltac:(eauto) (pDst p) _ ltac:(eauto) as Hem.
specialize (Hem ple gple e').
repeat concludes.
assert (eIndex e' <= eIndex ple) by omega.
intuition.
}
subst.
match goal with | [ H : commit_invariant_nw _ |- _ ] => rename H into Hnet; unfold commit_invariant_nw in * end.
eapply handleAppendEntries_preserves_commit; eauto.
eapply Hnet; eauto using Min.min_glb_l.
}
}
+
eapply handleAppendEntries_preserves_commit; eauto.
-
break_and.
unfold commit_invariant_nw in *.
simpl.
intros.
find_apply_hyp_hyp.
intuition.
+
eapply handleAppendEntries_preserves_commit; eauto.
simpl.
subst.
auto.
+
subst.
simpl in *.
find_apply_lem_hyp handleAppendEntries_not_append_entries.
subst.
exfalso.
Admitted.

Lemma handleAppendEntriesReply_preserves_commit : forall (net net' : ghost_log_network) h src t es b st' l e t', handleAppendEntriesReply h (snd (nwState net h)) src t es b = (st', l) -> (forall h', nwState net' h' = update name_eq_dec (nwState net) h (fst (nwState net h), st') h') -> lifted_committed net e t' -> lifted_committed net' e t'.
Proof using rmri.
intros.
eapply lifted_committed_log_allEntries_preserved; eauto.
-
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
+
now erewrite handleAppendEntriesReply_same_log by eauto.
+
auto.
-
intros.
repeat find_higher_order_rewrite.
Admitted.

Lemma commit_invariant_append_entries_reply : msg_refined_raft_net_invariant_append_entries_reply commit_invariant.
Proof using rmri.
unfold msg_refined_raft_net_invariant_append_entries_reply, commit_invariant.
simpl.
intros.
split.
-
unfold commit_invariant_host in *.
simpl.
intuition.
repeat find_higher_order_rewrite.
update_destruct_simplify.
+
eapply handleAppendEntriesReply_preserves_commit; eauto.
match goal with | [ H : context [commitIndex] |- _ ] => erewrite handleAppendEntriesReply_same_commitIndex in H by eauto end.
match goal with | [ H : context [log] |- _ ] => erewrite handleAppendEntriesReply_same_log in H by eauto end.
eapply lifted_committed_monotonic; [eauto|].
find_apply_lem_hyp handleAppendEntriesReply_type_term.
intuition; repeat find_rewrite; auto.
+
eapply handleAppendEntriesReply_preserves_commit; eauto.
-
unfold commit_invariant_nw in *.
simpl.
intros.
find_apply_hyp_hyp.
intuition.
+
eapply handleAppendEntriesReply_preserves_commit; eauto.
simpl.
subst.
auto.
+
do_in_map.
unfold add_ghost_msg in *.
do_in_map.
subst.
simpl in *.
find_apply_lem_hyp handleAppendEntriesReply_packets.
subst.
simpl in *.
Admitted.

Lemma handleRequestVote_preserves_committed : forall (net net' : ghost_log_network) h t c li lt st' ms e t', handleRequestVote h (snd (nwState net h)) t c li lt = (st', ms) -> (forall h', nwState net' h' = update name_eq_dec (nwState net) h (update_elections_data_requestVote h c t c li lt (nwState net h), st') h') -> lifted_committed net e t' -> lifted_committed net' e t'.
Proof using rmri.
intros.
eapply lifted_committed_log_allEntries_preserved; eauto.
-
intros.
find_higher_order_rewrite.
update_destruct_simplify.
+
now erewrite handleRequestVote_same_log by eauto.
+
auto.
-
intros.
find_higher_order_rewrite.
update_destruct_simplify.
+
now rewrite update_elections_data_requestVote_allEntries.
+
Admitted.

Lemma commit_invariant_request_vote : msg_refined_raft_net_invariant_request_vote commit_invariant.
Proof using rmri.
unfold msg_refined_raft_net_invariant_request_vote, commit_invariant.
simpl.
intuition.
-
unfold commit_invariant_host in *.
simpl.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
+
eapply handleRequestVote_preserves_committed; eauto.
match goal with | [ H : context [commitIndex] |- _ ] => erewrite handleRequestVote_same_commitIndex in H by eauto end.
match goal with | [ H : context [log] |- _ ] => erewrite handleRequestVote_same_log in H by eauto end.
eapply lifted_committed_monotonic; eauto.
find_apply_lem_hyp handleRequestVote_currentTerm_leaderId.
intuition.
unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params in *.
simpl in *.
repeat find_rewrite.
auto.
+
eapply handleRequestVote_preserves_committed; eauto.
-
unfold commit_invariant_nw in *.
simpl.
intros.
find_apply_hyp_hyp.
intuition.
+
eapply handleRequestVote_preserves_committed; eauto.
simpl.
intros.
subst.
auto.
+
subst.
simpl in *.
unfold write_ghost_log in *.
find_apply_lem_hyp handleRequestVote_no_append_entries.
subst.
exfalso.
Admitted.

Lemma handleRequestVoteReply_preserves_committed : forall (net net' : ghost_log_network) h src t v st' e t', handleRequestVoteReply h (snd (nwState net h)) src t v = st' -> (forall h', nwState net' h' = update name_eq_dec (nwState net) h (update_elections_data_requestVoteReply h src t v (nwState net h), st') h') -> lifted_committed net e t' -> lifted_committed net' e t'.
Proof using rmri.
intros.
eapply lifted_committed_log_allEntries_preserved; eauto.
-
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
+
erewrite handleRequestVoteReply_log; eauto.
+
auto.
-
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
+
rewrite update_elections_data_requestVoteReply_allEntries.
auto.
+
Admitted.

Lemma commit_invariant_request_vote_reply : msg_refined_raft_net_invariant_request_vote_reply commit_invariant.
Proof using rmri.
unfold msg_refined_raft_net_invariant_request_vote_reply, commit_invariant.
simpl.
intuition.
-
unfold commit_invariant_host in *.
simpl.
intuition.
match goal with | [ H : forall h, st' h = _ |- _ ] => repeat rewrite H in * end.
destruct (name_eq_dec (pDst p) h).
+
subst h.
subst gd.
rewrite_update.
simpl in *.
eapply handleRequestVoteReply_preserves_committed; eauto.
find_copy_apply_lem_hyp handleRequestVoteReply_type.
subst.
match goal with | [ H : context [commitIndex] |- _ ] => rewrite handleRequestVoteReply_same_commitIndex in H end.
match goal with | [ H : context [log] |- _ ] => erewrite handleRequestVoteReply_same_log in H end.
eapply lifted_committed_monotonic; eauto.
intuition; repeat find_rewrite; auto.
+
rewrite_update.
eapply handleRequestVoteReply_preserves_committed; eauto.
simpl.
subst.
auto.
-
unfold commit_invariant_nw.
simpl.
intros.
find_apply_hyp_hyp.
eapply handleRequestVoteReply_preserves_committed; eauto.
simpl.
subst.
Admitted.

Lemma committed_ext' : forall ps ps' st st' t e, (forall h, st' h = st h) -> committed (mkNetwork ps st) e t -> committed (mkNetwork ps' st') e t.
Proof using.
unfold committed, directly_committed.
simpl.
intros.
break_exists_exists.
find_higher_order_rewrite.
intuition.
break_exists_exists.
intuition.
find_higher_order_rewrite.
Admitted.

Lemma lifted_committed_ext' : forall ps ps' st st' t e, (forall h, st' h = st h) -> lifted_committed (mkNetwork ps st) e t -> lifted_committed (mkNetwork ps' st') e t.
Proof using rmri.
intros.
apply committed_lifted_committed.
find_apply_lem_hyp lifted_committed_committed.
unfold mgv_deghost in *.
Admitted.

Lemma doLeader_spec : forall st n os st' ms, doLeader st n = (os, st', ms) -> (st' = st /\ ms = []) \/ (type st = Leader /\ log st' = log st /\ type st' = type st /\ currentTerm st' = currentTerm st /\ nextIndex st' = nextIndex st /\ commitIndex st' = commitIndex (advanceCommitIndex st n) /\ forall m, In m ms -> exists h, h <> n /\ m = replicaMessage (advanceCommitIndex st n) n h).
Proof using.
unfold doLeader.
intros.
destruct st.
simpl in *.
repeat break_match; repeat find_inversion; simpl in *; eauto.
right.
intuition.
-
intros.
do_in_map.
subst.
find_apply_lem_hyp filter_In.
break_and.
break_if; try discriminate.
eexists.
intuition eauto.
-
Admitted.

Lemma haveQuorum_directly_committed : forall net h e, refined_raft_intermediate_reachable net -> type (snd (nwState net h)) = Leader -> In e (log (snd (nwState net h))) -> haveQuorum (snd (nwState net h)) h (eIndex e) = true -> eTerm e = currentTerm (snd (nwState net h)) -> directly_committed net e.
Proof using miaei.
unfold haveQuorum, directly_committed.
intros.
do_bool.
eexists.
intuition eauto.
-
apply filter_NoDup.
pose proof no_dup_nodes.
simpl in *.
auto.
-
find_apply_lem_hyp filter_In.
break_and.
do_bool.
Admitted.

Lemma advanceCommitIndex_committed : forall h net, refined_raft_intermediate_reachable net -> type (snd (nwState net h)) = Leader -> (forall e, In e (log (snd (nwState net h))) -> eIndex e <= commitIndex (snd (nwState net h)) -> committed net e (currentTerm (snd (nwState net h)))) -> (forall e, In e (log (snd (nwState net h))) -> eIndex e <= commitIndex (advanceCommitIndex (snd (nwState net h)) h) -> committed net e (currentTerm (snd (nwState net h)))).
Proof using miaei.
unfold advanceCommitIndex.
intros.
simpl in *.
match goal with | [ H : context [fold_left Nat.max ?l ?x] |- _ ] => pose proof fold_left_maximum_cases l x end.
intuition.
break_exists.
break_and.
find_apply_lem_hyp in_map_iff.
break_exists_name witness.
break_and.
find_apply_lem_hyp filter_In.
break_and.
find_apply_lem_hyp findGtIndex_necessary.
do_bool.
break_and.
do_bool.
break_and.
do_bool.
unfold committed.
exists h, witness.
intuition.
Admitted.

Lemma lifted_advanceCommitIndex_lifted_committed : forall h net, msg_refined_raft_intermediate_reachable net -> type (snd (nwState net h)) = Leader -> (forall e, In e (log (snd (nwState net h))) -> eIndex e <= commitIndex (snd (nwState net h)) -> lifted_committed net e (currentTerm (snd (nwState net h)))) -> (forall e, In e (log (snd (nwState net h))) -> eIndex e <= commitIndex (advanceCommitIndex (snd (nwState net h)) h) -> lifted_committed net e (currentTerm (snd (nwState net h)))).
Proof using rmri miaei.
intros.
find_apply_lem_hyp msg_simulation_1.
Admitted.

Lemma and_imp_2 : forall P Q : Prop, P /\ (P -> Q) -> P /\ Q.
Proof using.
Admitted.

Lemma update_elections_data_appendEntries_preserves_allEntries' : forall st h t n pli plt es ci x, In x (allEntries (fst st)) -> In x (allEntries (update_elections_data_appendEntries h st t n pli plt es ci)).
Proof using.
unfold update_elections_data_appendEntries.
intros.
break_let.
break_match; auto.
break_if; auto.
simpl.
intuition.
