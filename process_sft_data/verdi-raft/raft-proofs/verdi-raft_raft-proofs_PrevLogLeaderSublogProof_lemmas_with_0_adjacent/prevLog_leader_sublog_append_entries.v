Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.RefinementCommonDefinitions.
Require Import VerdiRaft.PrevLogCandidateEntriesTermInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.PrevLogLeaderSublogInterface.
Hint Extern 4 (@BaseParams) => apply base_params : typeclass_instances.
Hint Extern 4 (@MultiParams _) => apply multi_params : typeclass_instances.
Hint Extern 4 (@FailureParams _ _) => apply failure_params : typeclass_instances.
Section PrevLogLeaderSublogProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Context {lsi : leader_sublog_interface}.
Context {plceti : prevLog_candidateEntriesTerm_interface}.
Definition candidateEntriesTerm_lowered (net : network) t p : Prop := In p (nwPackets net) -> pBody p = RequestVoteReply t true -> currentTerm (nwState net (pDst p)) = t -> wonElection (dedup name_eq_dec (pSrc p :: votesReceived (nwState net (pDst p)))) = true -> type (nwState net (pDst p)) <> Candidate.
Instance pllsi : prevLog_leader_sublog_interface.
Proof.
constructor.
apply prevLog_leader_sublog_invariant.
End PrevLogLeaderSublogProof.

Lemma prevLog_leader_sublog_append_entries : raft_net_invariant_append_entries prevLog_leader_sublog.
Proof using.
unfold raft_net_invariant_append_entries, prevLog_leader_sublog.
intros.
simpl in *.
repeat find_higher_order_rewrite.
find_apply_hyp_hyp.
break_or_hyp.
-
find_eapply_lem_hyp app_cons_in_rest; [|solve[eauto]].
find_rewrite.
break_if; eauto.
find_copy_apply_lem_hyp handleAppendEntries_type_log.
intuition.
+
congruence.
+
repeat find_rewrite.
eapply_prop_hyp In In; eauto.
-
find_apply_lem_hyp handleAppendEntries_not_append_entries.
simpl in *.
subst.
exfalso.
eauto 10.
