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

Lemma handleAppendEntriesReply_matchIndex : forall h st st' m t es res h', handleAppendEntriesReply h st h' t es res = (st', m) -> type st' = Leader -> type st = Leader /\ (matchIndex st' = matchIndex st \/ res = true /\ currentTerm st = t /\ matchIndex st' = (assoc_set name_eq_dec (matchIndex st) h' (Nat.max (assoc_default name_eq_dec (matchIndex st) h' 0) (maxIndex es)))).
Proof using.
unfold handleAppendEntriesReply, advanceCurrentTerm.
intros.
repeat break_match; repeat find_inversion; simpl in *; do_bool; auto; congruence.
