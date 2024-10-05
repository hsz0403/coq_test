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

Lemma lifted_maxIndex_sanity_state_same_packet_subset : msg_refined_raft_net_invariant_state_same_packet_subset lifted_maxIndex_sanity.
Proof using.
unfold msg_refined_raft_net_invariant_state_same_packet_subset, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
Admitted.

Lemma lifted_maxIndex_sanity_reboot : msg_refined_raft_net_invariant_reboot lifted_maxIndex_sanity.
Proof using.
unfold msg_refined_raft_net_invariant_reboot, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
unfold reboot.
Admitted.

Lemma commit_invariant_init : msg_refined_raft_net_invariant_init commit_invariant.
Proof using.
unfold msg_refined_raft_net_invariant_init, commit_invariant.
split.
-
unfold commit_invariant_host, commit_recorded_committed, commit_recorded, committed.
simpl.
intuition.
-
Admitted.

Lemma msg_lifted_lastApplied_le_commitIndex : forall net h, msg_refined_raft_intermediate_reachable net -> lastApplied (snd (nwState net h)) <= commitIndex (snd (nwState net h)).
Proof using rmri lalcii rri.
intros.
pose proof (lift_prop _ (lastApplied_le_commitIndex_invariant)).
find_apply_lem_hyp msg_simulation_1.
find_apply_hyp_hyp.
unfold lastApplied_le_commitIndex in *.
match goal with | [ H : _ |- _ ] => specialize (H h) end.
find_rewrite_lem deghost_spec.
find_rewrite_lem msg_deghost_spec.
Admitted.

Lemma lifted_directly_committed_directly_committed : forall net e, lifted_directly_committed net e -> directly_committed (mgv_deghost net) e.
Proof using rmri.
unfold lifted_directly_committed, directly_committed.
intuition.
break_exists_exists.
intuition.
rewrite msg_deghost_spec.
Admitted.

Lemma directly_committed_lifted_directly_committed : forall net e, directly_committed (mgv_deghost net) e -> lifted_directly_committed net e.
Proof using rmri.
unfold lifted_directly_committed, directly_committed.
intuition.
break_exists_exists.
intuition.
find_apply_hyp_hyp.
find_rewrite_lem msg_deghost_spec.
Admitted.

Lemma lifted_committed_committed : forall net e t, lifted_committed net e t -> committed (mgv_deghost net) e t.
Proof using rmri.
unfold lifted_committed, committed.
intros.
break_exists_exists.
rewrite msg_deghost_spec.
Admitted.

Lemma committed_lifted_committed : forall net e t, committed (mgv_deghost net) e t -> lifted_committed net e t.
Proof using rmri.
unfold lifted_committed, committed.
intros.
break_exists_exists.
find_rewrite_lem msg_deghost_spec.
Admitted.

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

Lemma handleClientRequest_currentTerm : forall h st client id c out st' ms, handleClientRequest h st client id c = (out, st', ms) -> currentTerm st' = currentTerm st.
Proof using.
unfold handleClientRequest.
intros.
repeat break_match; repeat find_inversion; auto.
