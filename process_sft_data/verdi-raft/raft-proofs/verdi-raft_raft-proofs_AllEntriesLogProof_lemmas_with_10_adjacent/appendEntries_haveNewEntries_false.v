Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.LogsLeaderLogsInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.AllEntriesLeaderLogsTermInterface.
Require Import VerdiRaft.LeaderLogsContiguousInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.AllEntriesTermSanityInterface.
Require Import VerdiRaft.AllEntriesLogInterface.
Section AllEntriesLog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {llli : logs_leaderLogs_interface}.
Context {aerlli : append_entries_leaderLogs_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Context {aellti : allEntries_leaderLogs_term_interface}.
Context {llci : leaderLogs_contiguous_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {llsi : leaderLogs_sorted_interface}.
Context {tsi : term_sanity_interface}.
Context {rri : raft_refinement_interface}.
Context {aetsi : allEntries_term_sanity_interface}.
Definition no_entries_past_current_term_host_lifted net := forall (h : name) e, In e (log (snd (nwState net h))) -> eTerm e <= currentTerm (snd (nwState net h)).
Ltac inList x ls := match ls with | x => idtac | (_, x) => idtac | (?LS, _) => inList x LS end.
Ltac app f ls := match ls with | (?LS, ?X) => f X || app f LS || fail 1 | _ => f ls end.
Ltac all f ls := match ls with | (?LS, ?X) => f X; all f LS | (_, _) => fail 1 | _ => f ls end.
Instance aeli : allEntries_log_interface.
split.
eauto using allEntries_log_invariant.
Defined.
End AllEntriesLog.

Lemma no_entries_past_current_term_host_lifted_invariant : forall net, refined_raft_intermediate_reachable net -> no_entries_past_current_term_host_lifted net.
Proof using rri tsi.
unfold no_entries_past_current_term_host_lifted.
pose proof deghost_spec.
do 4 intro.
repeat find_reverse_higher_order_rewrite.
eapply lift_prop; eauto.
intros.
Admitted.

Lemma maxIndex_le : forall l1 l2, sorted l1 -> contiguous_range_exact_lo l1 0 -> findAtIndex l1 (maxIndex l2) = None -> l2 = nil \/ (exists e, In e l2 /\ eIndex e = 0) \/ maxIndex l1 <= maxIndex l2.
Proof using.
intros.
destruct l2; intuition.
simpl in *.
right.
destruct l1; intuition.
find_copy_eapply_lem_hyp findAtIndex_None; simpl in *; eauto.
unfold contiguous_range_exact_lo in *.
simpl in *.
intuition.
destruct (lt_eq_lt_dec 0 (eIndex e)); intuition; eauto.
destruct (lt_eq_lt_dec (eIndex e0) (eIndex e)); intuition.
exfalso.
repeat break_if; do_bool; intuition.
match goal with | H : forall _, _ < _ <= _ -> _ |- _ => specialize (H (eIndex e)) end; conclude_using omega.
simpl in *.
break_exists.
intuition; subst; intuition.
Admitted.

Lemma maxIndex_le' : forall l1 l2 i, sorted l1 -> contiguous_range_exact_lo l1 0 -> l2 <> nil -> contiguous_range_exact_lo l2 i -> findAtIndex l1 (maxIndex l2) = None -> maxIndex l1 <= maxIndex l2.
Proof using.
intros.
find_eapply_lem_hyp maxIndex_le; intuition; eauto.
break_exists.
intuition.
unfold contiguous_range_exact_lo in *.
intuition.
find_insterU.
conclude_using eauto.
Admitted.

Lemma sorted_app_in_in : forall l1 l2 e e', sorted (l1 ++ l2) -> In e l1 -> In e' l2 -> eIndex e' < eIndex e.
Proof using.
induction l1; intros; simpl in *; intuition; eauto.
subst.
find_insterU.
conclude_using ltac:(apply in_app_iff; intuition eauto).
Admitted.

Lemma sorted_app_sorted_app_in1_in2 : forall l1 l2 l3 e e', sorted (l1 ++ l3) -> sorted (l2 ++ l3) -> In e l1 -> In e' (l2 ++ l3) -> eIndex e' = eIndex e -> In e' l2.
Proof using.
intros.
do_in_app.
intuition.
match goal with | H : sorted (?l ++ ?l'), _ : In _ ?l, _ : In _ ?l' |- _ => eapply sorted_app_in_in in H end; eauto.
Admitted.

Lemma sorted_app_sorted_app_in1_in2_prefix : forall l1 l2 l3 l4 e e', sorted (l1 ++ l3) -> sorted (l2 ++ l4) -> Prefix l4 l3 -> In e l1 -> In e' (l2 ++ l4) -> eIndex e' = eIndex e -> In e' l2.
Proof using.
intros.
do_in_app.
intuition.
find_eapply_lem_hyp Prefix_In; [|eauto].
match goal with | H : sorted (?l ++ ?l'), _ : In _ ?l, _ : In _ ?l' |- _ => eapply sorted_app_in_in in H end; eauto.
Admitted.

Lemma sorted_app_in2_in2 : forall l1 l2 e e', sorted (l1 ++ l2) -> In e' (l1 ++ l2) -> In e l2 -> eIndex e' = eIndex e -> In e' l2.
Proof using.
intros.
do_in_app.
intuition.
match goal with | H : sorted (?l ++ ?l'), _ : In _ ?l, _ : In _ ?l' |- _ => eapply sorted_app_in_in in H end; eauto.
Admitted.

Lemma sorted_term_index_le : forall l e e', sorted l -> In e l -> In e' l -> eTerm e' < eTerm e -> eIndex e' <= eIndex e.
Proof using.
induction l; intros; simpl in *; intuition; subst_max; intuition.
-
find_apply_hyp_hyp.
intuition.
-
find_apply_hyp_hyp.
Admitted.

Lemma term_ne_in_l2 : forall l e e' l1 l2, sorted l -> In e l -> (forall e', In e' l -> eTerm e' <= eTerm e) -> removeAfterIndex l (eIndex e) = l1 ++ l2 -> (forall e', In e' l1 -> eTerm e' = eTerm e) -> In e' l -> eTerm e' <> eTerm e -> In e' l2.
Proof using.
intros.
assert (eIndex e' <= eIndex e) by (eapply sorted_term_index_le; eauto; find_apply_hyp_hyp; destruct (lt_eq_lt_dec (eTerm e') (eTerm e)); intuition).
find_eapply_lem_hyp removeAfterIndex_le_In; eauto.
repeat find_rewrite.
do_in_app.
intuition.
find_apply_hyp_hyp.
Admitted.

Lemma Prefix_maxIndex_eq : forall l l', Prefix l l' -> l <> nil -> maxIndex l = maxIndex l'.
Proof using.
intros.
induction l; simpl in *; intuition.
break_match; intuition.
subst.
simpl.
Admitted.

Lemma sorted_gt_maxIndex : forall e l1 l2, sorted (e :: l1 ++ l2) -> l2 <> nil -> maxIndex l2 < eIndex e.
Proof using.
intros; induction l1; simpl in *; intuition.
-
destruct l2; simpl in *; intuition.
Admitted.

Lemma appendEntries_haveNewEntries_false : forall net p t n pli plt es ci h e, refined_raft_intermediate_reachable net -> In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> haveNewEntries (snd (nwState net h)) es = false -> In e es -> In e (log (snd (nwState net h))).
Proof using rlmli.
intros.
unfold haveNewEntries in *.
do_bool.
intuition; [unfold not_empty in *; break_match; subst; simpl in *; intuition; congruence|].
break_match; try congruence.
do_bool.
find_apply_lem_hyp findAtIndex_elim.
intuition.
assert (es <> nil) by (destruct es; subst; simpl in *; intuition; congruence).
find_eapply_lem_hyp maxIndex_non_empty.
break_exists.
intuition.
find_copy_eapply_lem_hyp entries_sorted_nw_invariant; eauto.
match goal with | H : In e es |- _ => copy_eapply maxIndex_is_max H; eauto end.
repeat find_rewrite.
find_eapply_lem_hyp entries_match_nw_host_invariant; eauto.
