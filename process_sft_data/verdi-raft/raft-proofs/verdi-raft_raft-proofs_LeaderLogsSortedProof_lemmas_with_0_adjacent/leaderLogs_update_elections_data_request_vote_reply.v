Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.SortedInterface.
Section LeaderLogsSorted.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {si : sorted_interface}.
Instance llsi : leaderLogs_sorted_interface.
Proof.
split.
eauto using leaderLogs_sorted_invariant.
Defined.
End LeaderLogsSorted.

Lemma leaderLogs_update_elections_data_request_vote_reply : forall {h st h' t r st'}, handleRequestVoteReply h (snd st) h' t r = st' -> forall (P : list (term * list entry) -> Prop), (forall t, P ((t, log (snd st)) :: leaderLogs (fst st))) -> (P (leaderLogs (fst st))) -> (P (leaderLogs (update_elections_data_requestVoteReply h h' t r st))).
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
repeat break_match; simpl in *; eauto.
repeat find_rewrite.
match goal with | H : handleRequestVoteReply _ _ _ _ _ = _ |- _ => symmetry in H end.
find_apply_lem_hyp handleRequestVoteReply_spec.
intuition; repeat find_rewrite; auto.
