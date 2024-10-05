Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CandidateTermGtLogInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Section LeaderLogsTermSanity.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {ctgli : candidate_term_gt_log_interface}.
Ltac term_sanity_start := red; unfold leaderLogs_term_sanity; simpl; intros.
Ltac term_sanity_start_update := term_sanity_start; repeat find_higher_order_rewrite; update_destruct; rewrite_update; [|eauto].
Ltac term_sanity_unchanged' lem := red; intros; eapply leaderLogs_term_sanity_unchanged; subst; eauto using lem.
Tactic Notation "term_sanity_unchanged" constr(lem) := term_sanity_unchanged' lem.
Tactic Notation "term_sanity_unchanged" := term_sanity_unchanged' eq_refl (* bogus *).
Ltac term_sanity_break_update := term_sanity_start_update; match goal with h : _ |- _ => eapply h end; [| eauto]; match goal with h : _ |- _ => solve [rewrite h; auto] end.
Ltac currentTerm_sanity_start := red; unfold leaderLogs_currentTerm_sanity; simpl; intros.
Ltac currentTerm_sanity_start_update := currentTerm_sanity_start; repeat find_higher_order_rewrite; update_destruct; rewrite_update; [|eauto].
Ltac currentTerm_sanity_unchanged := red; intros; eapply leaderLogs_currentTerm_sanity_unchanged; subst; eauto.
Ltac currentTerm_sanity_break_update := currentTerm_sanity_start_update; match goal with h : _ |- _ => eapply h end; [| eauto]; match goal with h : _ |- _ => solve [rewrite h; auto] end.
Ltac ctsc_start := red; unfold leaderLogs_currentTerm_sanity_candidate; simpl; intros.
Ltac ctsc_start_update := ctsc_start; repeat find_higher_order_rewrite; update_destruct; rewrite_update; [|eauto].
Ltac ctsc_unchanged := red; intros; eapply leaderLogs_currentTerm_sanity_candidate_unchanged; subst; eauto.
Instance lltsi : leaderLogs_term_sanity_interface.
Proof.
split.
-
apply leaderLogs_term_sanity_invariant.
-
apply leaderLogs_currentTerm_sanity_invariant.
-
apply leaderLogs_currentTerm_sanity_candidate_invariant.
End LeaderLogsTermSanity.

Lemma candidate_term_gt_log_lifted : forall net, refined_raft_intermediate_reachable net -> candidate_term_gt_log (deghost net).
Proof using ctgli rri.
intros.
Admitted.

Lemma leaderLogs_term_sanity_unchanged : forall net st' h gd d ps', leaderLogs_term_sanity net -> (forall h' : Net.name, st' h' = update name_eq_dec (nwState net) h (gd, d) h') -> leaderLogs gd = leaderLogs (fst (nwState net h)) -> leaderLogs_term_sanity {| nwPackets := ps'; nwState := st' |}.
Proof using.
unfold leaderLogs_term_sanity.
intros.
find_higher_order_rewrite.
Admitted.

Lemma leaderLogs_term_sanity_request_vote_reply : refined_raft_net_invariant_request_vote_reply leaderLogs_term_sanity.
Proof using ctgli rri.
term_sanity_start_update.
find_copy_apply_lem_hyp handleRequestVoteReply_type.
find_copy_apply_lem_hyp handleRequestVoteReply_log.
find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; auto.
unfold ghost_data, raft_data in *.
simpl in *.
subst.
intuition; eauto; repeat find_rewrite; try discriminate.
find_apply_lem_hyp candidate_term_gt_log_lifted.
unfold candidate_term_gt_log in *.
simpl in *; repeat break_match; simpl in *.
unfold gt in *.
subst.
repeat find_rewrite.
Admitted.

Lemma leaderLogs_currentTerm_sanity_unchanged : forall net st' h gd d ps', leaderLogs_currentTerm_sanity net -> (forall h' : Net.name, st' h' = update name_eq_dec (nwState net) h (gd, d) h') -> leaderLogs gd = leaderLogs (fst (nwState net h)) -> currentTerm d >= currentTerm (snd (nwState net h)) -> leaderLogs_currentTerm_sanity {| nwPackets := ps'; nwState := st' |}.
Proof using.
unfold leaderLogs_currentTerm_sanity.
intros.
find_higher_order_rewrite.
update_destruct; subst; rewrite_update.
-
simpl in *.
find_rewrite.
find_apply_hyp_hyp.
omega.
-
Admitted.

Lemma leaderLogs_currentTerm_sanity_init : refined_raft_net_invariant_init leaderLogs_currentTerm_sanity.
Proof using.
currentTerm_sanity_start.
Admitted.

Lemma leaderLogs_currentTerm_sanity_client_request : refined_raft_net_invariant_client_request leaderLogs_currentTerm_sanity.
Proof using.
currentTerm_sanity_unchanged.
-
apply update_elections_data_client_request_leaderLogs.
-
find_apply_lem_hyp handleClientRequest_type.
Admitted.

Lemma leaderLogs_currentTerm_sanity_timeout : refined_raft_net_invariant_timeout leaderLogs_currentTerm_sanity.
Proof using.
currentTerm_sanity_unchanged.
-
apply update_elections_data_timeout_leaderLogs.
-
find_apply_lem_hyp handleTimeout_type_strong.
Admitted.

Lemma leaderLogs_currentTerm_sanity_append_entries : refined_raft_net_invariant_append_entries leaderLogs_currentTerm_sanity.
Proof using.
currentTerm_sanity_unchanged.
-
apply update_elections_data_appendEntries_leaderLogs.
-
find_apply_lem_hyp handleAppendEntries_type_term.
Admitted.

Lemma leaderLogs_currentTerm_sanity_append_entries_reply : refined_raft_net_invariant_append_entries_reply leaderLogs_currentTerm_sanity.
Proof using.
currentTerm_sanity_unchanged.
-
find_apply_lem_hyp handleAppendEntriesReply_type_term.
Admitted.

Lemma leaderLogs_currentTerm_sanity_request_vote : refined_raft_net_invariant_request_vote leaderLogs_currentTerm_sanity.
Proof using.
currentTerm_sanity_unchanged.
-
apply leaderLogs_update_elections_data_requestVote.
-
find_apply_lem_hyp handleRequestVote_type_term.
Admitted.

Lemma leaderLogs_currentTerm_sanity_request_vote_reply : refined_raft_net_invariant_request_vote_reply leaderLogs_currentTerm_sanity.
Proof using.
currentTerm_sanity_start_update.
simpl in *.
find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; [|auto].
find_copy_apply_lem_hyp handleRequestVoteReply_type.
intuition.
-
find_apply_hyp_hyp.
repeat find_rewrite.
auto.
-
find_apply_hyp_hyp.
omega.
-
find_apply_hyp_hyp.
repeat find_rewrite.
auto.
-
subst.
auto.
-
subst.
auto.
-
subst.
Admitted.

Lemma leaderLogs_currentTerm_sanity_do_leader : refined_raft_net_invariant_do_leader leaderLogs_currentTerm_sanity.
Proof using.
currentTerm_sanity_unchanged.
-
find_rewrite.
auto.
-
find_rewrite.
simpl.
find_apply_lem_hyp doLeader_type.
Admitted.

Lemma leaderLogs_currentTerm_sanity_do_generic_server : refined_raft_net_invariant_do_generic_server leaderLogs_currentTerm_sanity.
Proof using.
currentTerm_sanity_unchanged.
-
find_rewrite.
auto.
-
find_rewrite.
simpl.
find_apply_lem_hyp doGenericServer_type.
Admitted.

Lemma leaderLogs_term_sanity_invariant : forall net, refined_raft_intermediate_reachable net -> leaderLogs_term_sanity net.
Proof using ctgli rri.
intros.
apply refined_raft_net_invariant; auto.
-
term_sanity_start; contradiction.
-
term_sanity_unchanged update_elections_data_client_request_leaderLogs.
-
term_sanity_unchanged update_elections_data_timeout_leaderLogs.
-
term_sanity_unchanged update_elections_data_appendEntries_leaderLogs.
-
term_sanity_unchanged.
-
term_sanity_unchanged leaderLogs_update_elections_data_requestVote.
-
apply leaderLogs_term_sanity_request_vote_reply.
-
term_sanity_break_update.
-
term_sanity_break_update.
-
term_sanity_start; find_reverse_higher_order_rewrite; eauto.
-
term_sanity_break_update.
