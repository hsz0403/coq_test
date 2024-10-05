Require Import VerdiRaft.RaftState.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Section SpecLemmas.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Definition matchIndex_preserved st st' := type st' = Leader -> (type st = Leader /\ matchIndex st' = matchIndex st /\ log st' = log st).
Arguments matchIndex_preserved / _ _.
Definition matchIndex_preserved_except_at_host h st st' := type st' = Leader -> (type st = Leader /\ forall h', h <> h' -> (assoc_default name_eq_dec (matchIndex st') h' 0) = (assoc_default name_eq_dec (matchIndex st) h') 0).
Arguments matchIndex_preserved_except_at_host / _ _ _.
End SpecLemmas.

Lemma handleRequestVote_votedFor : forall pDst t cid lli llt d d' m, handleRequestVote pDst d t cid lli llt = (d', m) -> currentTerm d = currentTerm d' -> votedFor d = None \/ votedFor d = votedFor d'.
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
Admitted.

Lemma handleRequestVoteReply_term_votedFor_cases : forall me st src t v st', handleRequestVoteReply me st src t v = st' -> (currentTerm st' = currentTerm st /\ votedFor st' = votedFor st) \/ (currentTerm st < currentTerm st' /\ votedFor st' = None).
Proof using.
intros.
Admitted.

Lemma handleAppendEntries_same_term_votedFor_preserved : forall h st t n pli plt es ci st' ps, handleAppendEntries h st t n pli plt es ci = (st', ps) -> currentTerm st' = currentTerm st -> votedFor st' = votedFor st.
Proof using.
unfold handleAppendEntries, advanceCurrentTerm.
intros.
Admitted.

Lemma handleAppendEntriesReply_same_term_votedFor_preserved : forall h st h' t es r st' ms, handleAppendEntriesReply h st h' t es r = (st', ms) -> currentTerm st' = currentTerm st -> votedFor st' = votedFor st.
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Lemma doGenericServer_currentTerm : forall h st os st' ms, doGenericServer h st = (os, st', ms) -> currentTerm st' = currentTerm st.
Proof using.
unfold doGenericServer.
intros.
Admitted.

Lemma doLeader_currentTerm : forall st h os st' ms, doLeader st h = (os, st', ms) -> currentTerm st' = currentTerm st.
Proof using.
intros.
unfold doLeader in *.
Admitted.

Lemma handleAppendEntriesReply_currentTerm : forall h st h' t es r st' ms, handleAppendEntriesReply h st h' t es r = (st', ms) -> currentTerm st <= currentTerm st'.
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Lemma handleAppendEntries_currentTerm : forall h st t n pli plt es ci st' ps, handleAppendEntries h st t n pli plt es ci = (st', ps) -> currentTerm st <= currentTerm st'.
Proof using.
intros.
unfold handleAppendEntries, advanceCurrentTerm in *.
Admitted.

Lemma tryToBecomeLeader_currentTerm : forall h st out st' l, tryToBecomeLeader h st = (out, st', l) -> currentTerm st <= currentTerm st'.
Proof using.
unfold tryToBecomeLeader.
intros.
find_inversion.
simpl.
Admitted.

Lemma handleTimeout_currentTerm : forall h st out st' l, handleTimeout h st = (out, st', l) -> currentTerm st <= currentTerm st'.
Proof using.
unfold handleTimeout.
intros.
break_match; eauto using tryToBecomeLeader_currentTerm.
find_inversion.
simpl.
Admitted.

Lemma haveNewEntries_not_empty : forall st es, haveNewEntries st es = true -> es <> [].
Proof using.
intros.
unfold haveNewEntries, not_empty in *.
do_bool.
intuition.
Admitted.

Lemma handleRequestVote_cases : forall h h' t lli llt st st' m, handleRequestVote h st t h' lli llt = (st', m) -> st' = st \/ st' = advanceCurrentTerm st t \/ (st' = {[ advanceCurrentTerm st t with votedFor := Some h']} /\ (votedFor st = None /\ currentTerm st = t \/ currentTerm st < t)).
Proof using.
unfold handleRequestVote.
intros.
repeat break_match; repeat find_inversion; intuition.
-
simpl in *.
discriminate.
-
unfold advanceCurrentTerm in *.
break_if; simpl in *; do_bool; intuition.
