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

Lemma lifted_sorted_network : forall net p t n pli plt es ci, refined_raft_intermediate_reachable net -> In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> sorted es.
Proof using rlmli.
intros.
Admitted.

Lemma lifted_no_entries_past_current_term_host_invariant : forall (net : @network _ raft_msg_refined_multi_params), msg_refined_raft_intermediate_reachable net -> lifted_no_entries_past_current_term_host net.
Proof using rmri tsi.
intros.
enough (no_entries_past_current_term_host (deghost (mgv_deghost net))) by (unfold no_entries_past_current_term_host, lifted_no_entries_past_current_term_host, deghost, mgv_deghost in *; simpl in *; repeat break_match; simpl in *; auto).
apply msg_lift_prop_all_the_way; eauto.
intros.
Admitted.

Lemma all_the_way_deghost_spec : forall (net : ghost_log_network) h, snd (nwState net h) = nwState (deghost (mgv_deghost net)) h.
Proof using rmri rri.
intros.
rewrite deghost_spec.
rewrite msg_deghost_spec with (net0 := net).
Admitted.

Lemma all_the_way_simulation_1 : forall (net : ghost_log_network), msg_refined_raft_intermediate_reachable net -> raft_intermediate_reachable (deghost (mgv_deghost net)).
Proof using rmri rri.
Admitted.

Lemma lifted_maxIndex_sanity_client_request : msg_refined_raft_net_invariant_client_request lifted_maxIndex_sanity.
Proof using rmri si rri.
unfold msg_refined_raft_net_invariant_client_request, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
simpl.
intros.
find_copy_apply_lem_hyp handleClientRequest_maxIndex.
-
intuition; simpl in *; repeat find_higher_order_rewrite; update_destruct_simplify; auto.
+
erewrite handleClientRequest_lastApplied by eauto.
eauto using le_trans.
+
erewrite handleClientRequest_commitIndex by eauto.
eauto using le_trans.
-
match goal with H : _ |- _ => rewrite all_the_way_deghost_spec with (net := net) in H end.
eapply handleClientRequest_logs_sorted; eauto.
*
auto using all_the_way_simulation_1.
*
apply logs_sorted_invariant.
Admitted.

Lemma lifted_maxIndex_sanity_timeout : msg_refined_raft_net_invariant_timeout lifted_maxIndex_sanity.
Proof using.
unfold msg_refined_raft_net_invariant_timeout, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
intuition; simpl in *; repeat find_higher_order_rewrite; update_destruct_simplify; auto; erewrite handleTimeout_log_same by eauto.
-
erewrite handleTimeout_lastApplied; eauto.
-
Admitted.

Lemma handleAppendEntries_lastApplied : forall h st t n pli plt es ci st' m, handleAppendEntries h st t n pli plt es ci = (st', m) -> lastApplied st' = lastApplied st.
Proof using.
Admitted.

Lemma sorted_maxIndex_app : forall l1 l2, sorted (l1 ++ l2) -> maxIndex l2 <= maxIndex (l1 ++ l2).
Proof using.
induction l1; intros; simpl in *; intuition.
destruct l2; intuition.
simpl in *.
specialize (H0 e).
conclude H0 intuition.
Admitted.

Lemma max_min_thing: forall a b c, a <= c -> max a (min b c) <= c.
Proof using.
intros.
Admitted.

Lemma in_ghost_packet : forall (net : network (params := raft_refined_multi_params)) p, In p (nwPackets net) -> In (deghost_packet p) (nwPackets (deghost net)).
Proof using.
unfold deghost.
simpl.
intuition.
apply in_map_iff.
Admitted.

Lemma pBody_deghost_packet : forall (p : packet (params := raft_refined_multi_params)), pBody (deghost_packet p) = pBody p.
Proof using.
unfold deghost_packet.
simpl.
Admitted.

Lemma pDst_deghost_packet : forall (p : packet (params := raft_refined_multi_params)), pDst (deghost_packet p) = pDst p.
Proof using.
unfold deghost_packet.
simpl.
Admitted.

Lemma pDst_mgv_deghost_packet : forall (p : ghost_log_packet), pDst (mgv_deghost_packet p) = pDst p.
Proof using.
unfold mgv_deghost_packet.
simpl.
Admitted.

Lemma pBody_mgv_deghost_packet : forall (p : ghost_log_packet), pBody (mgv_deghost_packet p) = snd (pBody p).
Proof using.
unfold mgv_deghost_packet.
simpl.
Admitted.

Lemma lifted_handleAppendEntries_logs_sorted : forall (net : ghost_log_network) (p : ghost_log_packet) t n pli plt es ci st' m, msg_refined_raft_intermediate_reachable net -> handleAppendEntries (pDst p) (snd (nwState net (pDst p))) t n pli plt es ci = (st', m) -> snd (pBody p) = AppendEntries t n pli plt es ci -> In p (nwPackets net) -> sorted (log st').
Proof using rmri si rri.
intros.
eapply handleAppendEntries_logs_sorted with (p0 := deghost_packet (mgv_deghost_packet p)).
-
eauto using all_the_way_simulation_1.
-
apply lift_prop.
+
apply logs_sorted_invariant.
+
auto using msg_simulation_1.
-
rewrite <- all_the_way_deghost_spec.
rewrite pDst_deghost_packet.
rewrite pDst_mgv_deghost_packet.
eauto.
-
rewrite pBody_deghost_packet.
rewrite pBody_mgv_deghost_packet.
auto.
-
apply in_ghost_packet.
apply in_mgv_ghost_packet.
Admitted.

Lemma contiguous_range_exact_lo_elim_exists : forall es lo i, contiguous_range_exact_lo es lo -> lo < i <= maxIndex es -> exists e, eIndex e = i /\ In e es.
Proof using.
unfold contiguous_range_exact_lo.
Admitted.

Lemma contiguous_range_exact_lo_elim_lt : forall es lo e, contiguous_range_exact_lo es lo -> In e es -> lo < eIndex e.
Proof using.
unfold contiguous_range_exact_lo.
Admitted.

Lemma lifted_sms_nw : forall (net : network (params := raft_refined_multi_params)) h p t leaderId prevLogIndex prevLogTerm entries leaderCommit e, state_machine_safety (deghost net) -> In p (nwPackets net) -> pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit -> t >= currentTerm (snd (nwState net h)) -> commit_recorded (deghost net) h e -> (prevLogIndex > eIndex e \/ (prevLogIndex = eIndex e /\ prevLogTerm = eTerm e) \/ eIndex e > maxIndex entries \/ In e entries).
Proof using rri.
unfold state_machine_safety, state_machine_safety_nw.
intuition.
match goal with | [ H : _ |- _ ] => eapply H with (p := deghost_packet p) end.
-
auto using in_ghost_packet.
-
rewrite pBody_deghost_packet.
eauto.
-
rewrite deghost_spec.
eauto.
-
Admitted.

Lemma msg_lifted_sms_nw : forall (net : ghost_log_network) h p t leaderId prevLogIndex prevLogTerm entries leaderCommit e, state_machine_safety (deghost (mgv_deghost net)) -> In p (nwPackets net) -> snd (pBody p) = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit -> t >= currentTerm (snd (nwState net h)) -> commit_recorded (deghost (mgv_deghost net)) h e -> (prevLogIndex > eIndex e \/ (prevLogIndex = eIndex e /\ prevLogTerm = eTerm e) \/ eIndex e > maxIndex entries \/ In e entries).
Proof using rmri rri.
intros.
eapply lifted_sms_nw.
-
eauto.
-
eauto using in_mgv_ghost_packet.
-
rewrite pBody_mgv_deghost_packet.
eauto.
-
rewrite msg_deghost_spec with (net0 := net).
eauto.
-
Admitted.

Lemma commit_recorded_lift_intro : forall (net : network (params := raft_refined_multi_params)) h e, In e (log (snd (nwState net h))) -> (eIndex e <= lastApplied (snd (nwState net h)) \/ eIndex e <= commitIndex (snd (nwState net h))) -> commit_recorded (deghost net) h e.
Proof using rri.
unfold commit_recorded.
intros.
rewrite deghost_spec.
Admitted.

Lemma in_mgv_ghost_packet : forall (net : ghost_log_network) p, In p (nwPackets net) -> In (mgv_deghost_packet p) (nwPackets (mgv_deghost net)).
Proof using.
unfold mgv_deghost.
simpl.
intuition.
apply in_map_iff.
eexists; eauto.
