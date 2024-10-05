Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.AppendEntriesRequestsCameFromLeadersInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.OneLeaderPerTermInterface.
Require Import VerdiRaft.AppendEntriesLeaderInterface.
Section AppendEntriesLeader.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {aecfli : append_entries_came_from_leaders_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {lltsi : leaderLogs_term_sanity_interface}.
Context {olpti : one_leader_per_term_interface}.
Definition type_term_log_monotonic st st' := type st' = Leader -> type st = Leader /\ currentTerm st' = currentTerm st /\ (forall e, In e (log st) -> In e (log st')).
Notation appendEntries_leader_predicate ps st := (forall p t lid pli plt es lci e, In p ps -> pBody p = AppendEntries t lid pli plt es lci -> In e es -> currentTerm st = t -> type st = Leader -> In e (log st)).
Instance appendeli : append_entries_leader_interface.
Proof.
split.
exact appendEntries_leader_invariant.
End AppendEntriesLeader.

Lemma handleClientRequest_TTLM : forall h st client id c out st' l, handleClientRequest h st client id c = (out, st', l) -> type_term_log_monotonic st st'.
Proof using.
unfold type_term_log_monotonic.
intros.
find_copy_apply_lem_hyp handleClientRequest_type.
find_copy_apply_lem_hyp handleClientRequest_log.
intuition; try congruence.
break_exists.
intuition.
subst.
repeat find_rewrite.
auto with *.
