Require Import Sumbool.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.RefinementCommonDefinitions.
Require Import VerdiRaft.LeaderCompletenessInterface.
Require Import VerdiRaft.PrefixWithinTermInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.LeaderLogsPreservedInterface.
Require Import VerdiRaft.EveryEntryWasCreatedInterface.
Require Import VerdiRaft.LeaderLogsVotesWithLogInterface.
Require Import VerdiRaft.AllEntriesVotesWithLogInterface.
Require Import VerdiRaft.VotesWithLogSortedInterface.
Require Import VerdiRaft.TermsAndIndicesFromOneInterface.
Require Import VerdiRaft.LeaderLogsLogMatchingInterface.
Section LeaderCompleteness.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {pwti : prefix_within_term_interface}.
Context {lltsi : leaderLogs_term_sanity_interface}.
Context {llpi : leaderLogs_preserved_interface}.
Context {eewci : every_entry_was_created_interface}.
Context {llvwli : leaderLogs_votesWithLog_interface}.
Context {aevwli : allEntries_votesWithLog_interface}.
Context {vwlsi : votesWithLog_sorted_interface}.
Context {taifoi : terms_and_indices_from_one_interface}.
Context {lllmi : leaderLogs_entries_match_interface}.
Fixpoint contradicting_leader_logs_on_leader l t e := match l with | (t', log') :: l' => if (sumbool_and _ _ _ _ (lt_dec t t') (sumbool_not _ _ (in_dec entry_eq_dec e log'))) then (t', log') :: contradicting_leader_logs_on_leader l' t e else contradicting_leader_logs_on_leader l' t e | [] => [] end.
Fixpoint contradicting_leader_logs net nodes t e : list (term * name * list entry) := match nodes with | h :: nodes' => (map (fun l => (fst l, h, snd l)) (contradicting_leader_logs_on_leader (leaderLogs (fst (nwState net h))) t e)) ++ contradicting_leader_logs net nodes' t e | [] => [] end.
Definition minimal_contradicting_leader_log net t e := argmin (fun l => fst (fst l)) (contradicting_leader_logs net nodes t e).
Instance lci : leader_completeness_interface.
Proof.
split.
exact leader_completeness_invariant.
End LeaderCompleteness.

Lemma contradicting_leader_logs_empty : forall net nodes t e, contradicting_leader_logs net nodes t e = [] -> forall h, In h nodes -> contradicting_leader_logs_on_leader (leaderLogs (fst (nwState net h))) t e = [].
Proof using.
intros.
Admitted.

Lemma minimal_contradicting_leader_log_None : forall net t e, minimal_contradicting_leader_log net t e = None -> forall t' log h, In (t', log) (leaderLogs (fst (nwState net h))) -> t' > t -> In e log.
Proof using.
intros.
find_apply_lem_hyp argmin_None.
eapply contradicting_leader_logs_on_leader_empty; eauto.
eapply contradicting_leader_logs_empty; eauto.
Admitted.

Lemma In_contradicting_logs_on_leader_elim : forall l t e t' l', In (t', l') (contradicting_leader_logs_on_leader l t e) -> In (t', l') l /\ t < t' /\ ~ In e l'.
Proof using.
Admitted.

Lemma in_contradicting_leader_logs : forall net nodes t e t' h l, In (t', h, l) (contradicting_leader_logs net nodes t e) -> In (t', l) (contradicting_leader_logs_on_leader (leaderLogs (fst (nwState net h))) t e).
Proof using.
induction nodes; intros; simpl in *; intuition.
do_in_app.
intuition.
do_in_map.
find_inversion.
rewrite <- surjective_pairing.
Admitted.

Lemma in_contradicting_leader_logs_on_leader_in_leaderLog : forall ll t e t' l, In (t', l) (contradicting_leader_logs_on_leader ll t e) -> In (t', l) ll.
Proof using.
induction ll; intros; simpl in *; intuition.
Admitted.

Lemma in_contradicting_leader_logs_on_leader_not_in_log : forall t' l ll t e, In (t', l) (contradicting_leader_logs_on_leader ll t e) -> In e l -> False.
Proof using.
induction ll; intros; simpl in *; intuition.
repeat break_match; simpl in *; intuition eauto.
find_inversion.
Admitted.

Lemma in_contradicting_leader_logs_on_leader_term_lt : forall t' l ll t e, In (t', l) (contradicting_leader_logs_on_leader ll t e) -> t < t'.
Proof using.
induction ll; intros; simpl in *; intuition.
Admitted.

Lemma contradicting_leader_logs_on_leader_complete : forall t e t' l ll, In (t', l) ll -> t < t' -> ~ In e l -> In (t', l) (contradicting_leader_logs_on_leader ll t e).
Proof using.
Admitted.

Lemma contradicting_leader_logs_complete : forall net nodes h t e l t', In h nodes -> In (t', l) (contradicting_leader_logs_on_leader (leaderLogs (fst (nwState net h))) t e) -> In (t', h, l) (contradicting_leader_logs net nodes t e).
Proof using.
induction nodes; intros; simpl in *; intuition.
apply in_or_app.
subst.
left.
apply in_map_iff.
eexists.
intuition eauto.
simpl.
Admitted.

Lemma minimal_contradicting_leader_log_elim : forall net t e t' h l, minimal_contradicting_leader_log net t e = Some (t', h, l) -> (t < t' /\ In (t', l) (leaderLogs (fst (nwState net h))) /\ ~ In e l /\ (forall h' t'' l', In (t'', l') (leaderLogs (fst (nwState net h'))) -> (t'' <= t \/ t'' >= t' \/ In e l'))).
Proof using.
unfold minimal_contradicting_leader_log.
intros.
find_apply_lem_hyp argmin_elim.
intuition.
-
eauto using in_contradicting_leader_logs_on_leader_term_lt, in_contradicting_leader_logs.
-
eauto using in_contradicting_leader_logs, in_contradicting_leader_logs_on_leader_in_leaderLog.
-
eauto using in_contradicting_leader_logs, in_contradicting_leader_logs_on_leader_not_in_log.
-
destruct (le_lt_dec t'' t); auto.
destruct (le_lt_dec t' t''); auto.
destruct (in_dec entry_eq_dec e l'); auto.
find_eapply_lem_hyp contradicting_leader_logs_on_leader_complete; eauto.
find_eapply_lem_hyp contradicting_leader_logs_complete; [|solve [apply all_fin_all]].
find_apply_hyp_hyp.
simpl in *.
Admitted.

Lemma contradicting_leader_logs_on_leader_empty : forall l t e, contradicting_leader_logs_on_leader l t e = [] -> forall t' log, In (t', log) l -> t' > t -> In e log.
Proof using.
induction l; intros; simpl in *; intuition; subst; repeat break_match; subst; simpl in *; intuition eauto; congruence.
