Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.RefinementCommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeaderLogsVotesWithLogInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.VotesVotesWithLogCorrespondInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Section OneLeaderLogPerTerm.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {llvwli : leaderLogs_votesWithLog_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Context {vvci : votes_votesWithLog_correspond_interface}.
Context {lltsi : leaderLogs_term_sanity_interface}.
Ltac start := red; unfold one_leaderLog_per_term; simpl; intros.
Ltac start_update := start; repeat find_higher_order_rewrite; repeat (update_destruct; subst; rewrite_update); [| | |eauto].
Ltac start_unchanged := red; intros; eapply one_leaderLog_per_term_unchanged; eauto; subst.
Ltac unchanged lem := start_unchanged; apply lem.
Instance ollpti : one_leaderLog_per_term_interface.
Proof.
split; intros; intro_refined_invariant one_leaderLog_per_term_invariant; red; eapply_prop one_leaderLog_per_term.
End OneLeaderLogPerTerm.

Lemma contradiction_case : forall (net : network ) t ll ll' (h h' : name) (p : packet (params := refined_multi_params (multi_params := multi_params))) t0 v xs ys, refined_raft_intermediate_reachable net -> pBody p = RequestVoteReply (raft_params := raft_params) t0 v -> nwPackets net = xs ++ p :: ys -> In (t, ll) (leaderLogs (fst (nwState net h))) -> In (t, ll') (leaderLogs (update_elections_data_requestVoteReply (pDst p) (pSrc p) t0 v (nwState net (pDst p)))) -> pDst p = h' -> pDst p <> h -> False.
Proof using vvci cci vci llvwli.
intros.
unfold not in *.
find_false.
simpl in *.
find_apply_lem_hyp update_elections_data_requestVoteReply_leaderLogs'.
intro_refined_invariant leaderLogs_votesWithLog_invariant.
break_or_hyp; repeat (apply_prop_hyp leaderLogs_votesWithLog In; break_exists).
-
assert (exists h, In h x /\ In h x0) by (apply pigeon_nodes; intuition).
break_exists; break_and.
do 2 (find_apply_hyp_hyp; break_exists; break_and).
intro_refined_invariant votes_votesWithLog_correspond_invariant.
do 2 (apply_prop_hyp votes_votesWithLog In).
intro_refined_invariant votes_correct_invariant.
eauto.
-
assert (exists h, In h x /\ In h (dedup name_eq_dec (pSrc p :: votesReceived (snd (nwState net (pDst p)))))).
{
eapply pigeon_nodes.
-
intuition.
-
apply NoDup_dedup.
-
intuition.
-
apply wonElection_length; intuition.
}
break_exists.
break_and.
find_apply_hyp_hyp; break_exists; break_and.
intro_refined_invariant votes_votesWithLog_correspond_invariant.
apply_prop_hyp votes_votesWithLog In.
find_apply_lem_hyp in_dedup_was_in.
simpl in *.
intro_refined_invariant cronies_correct_invariant.
intro_refined_invariant votes_correct_invariant.
break_or_hyp; eauto.
