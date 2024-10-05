Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.AppendEntriesReplySublogInterface.
Require Import VerdiRaft.MatchIndexSanityInterface.
Require Import VerdiRaft.SortedInterface.
Section MatchIndexSanity.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {aersi : append_entries_reply_sublog_interface}.
Context {si : sorted_interface}.
Instance matchisi : match_index_sanity_interface.
Proof.
split.
exact match_index_sanity_invariant.
End MatchIndexSanity.

Lemma handleRequestVoteReply_matchIndex : forall n st src t v, type (handleRequestVoteReply n st src t v) = Leader -> type st = Leader /\ matchIndex (handleRequestVoteReply n st src t v) = matchIndex st \/ matchIndex (handleRequestVoteReply n st src t v) = (assoc_set name_eq_dec nil n (maxIndex (log st))).
Proof using.
unfold handleRequestVoteReply, advanceCurrentTerm.
intros.
repeat break_match; repeat find_inversion; auto; simpl in *; try congruence.
