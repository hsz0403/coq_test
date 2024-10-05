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

Lemma match_index_sanity_preserved : forall st st', matchIndex_preserved st st' -> (forall h, type st = Leader -> assoc_default name_eq_dec (matchIndex st) h 0 <= maxIndex (log st)) -> (forall h, type st' = Leader -> assoc_default name_eq_dec (matchIndex st') h 0 <= maxIndex (log st')).
Proof using.
unfold matchIndex_preserved.
intros.
intuition.
repeat find_rewrite.
auto.
