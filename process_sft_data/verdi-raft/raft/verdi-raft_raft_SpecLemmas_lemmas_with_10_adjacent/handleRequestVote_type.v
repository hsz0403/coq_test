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

Lemma handleRequestVote_log : forall h st t candidate lli llt st' m, handleRequestVote h st t candidate lli llt = (st', m) -> log st' = log st.
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
Admitted.

Lemma handleTimeout_log_same : forall h d out d' l, handleTimeout h d = (out, d', l) -> log d' = log d.
Proof using.
unfold handleTimeout, tryToBecomeLeader.
intros.
Admitted.

Lemma doGenericServer_log : forall h st os st' ps, doGenericServer h st = (os, st', ps) -> log st' = log st.
Proof using.
intros.
unfold doGenericServer in *.
Admitted.

Lemma handleRequestVoteReply_spec : forall h st h' t r st', st' = handleRequestVoteReply h st h' t r -> log st' = log st /\ (forall v, In v (votesReceived st) -> In v (votesReceived st')) /\ ((currentTerm st' = currentTerm st /\ type st' = type st) \/ type st' <> Candidate) /\ (type st <> Leader /\ type st' = Leader -> (type st = Candidate /\ wonElection (dedup name_eq_dec (votesReceived st')) = true)).
Proof using.
intros.
unfold handleRequestVoteReply, advanceCurrentTerm in *.
Admitted.

Lemma handleRequestVoteReply_spec' : forall h st h' t r st', st' = handleRequestVoteReply h st h' t r -> log st' = log st /\ (forall v, In v (votesReceived st) -> In v (votesReceived st')) /\ (type st <> Leader /\ type st' = Leader -> (type st = Candidate /\ wonElection (dedup name_eq_dec (votesReceived st')) = true) /\ r = true /\ currentTerm st' = currentTerm st /\ currentTerm st = t /\ votesReceived st' = (h' :: (votesReceived st))).
Proof using.
intros.
unfold handleRequestVoteReply, advanceCurrentTerm in *.
Admitted.

Theorem handleTimeout_not_is_append_entries : forall h st st' ms m, handleTimeout h st = (st', ms) -> In m ms -> ~ is_append_entries (snd m).
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Lemma handleAppendEntries_type : forall h st t n pli plt es ci st' ps, handleAppendEntries h st t n pli plt es ci = (st', ps) -> (type st' = type st /\ currentTerm st' = currentTerm st) \/ type st' = Follower.
Proof using.
intros.
unfold handleAppendEntries, advanceCurrentTerm in *.
Admitted.

Lemma handleAppendEntries_type_term : forall h st t n pli plt es ci st' ps, handleAppendEntries h st t n pli plt es ci = (st', ps) -> (type st' = type st /\ currentTerm st' = currentTerm st) \/ (type st' = Follower /\ currentTerm st' >= currentTerm st).
Proof using.
intros.
unfold handleAppendEntries, advanceCurrentTerm in *.
Admitted.

Lemma handleAppendEntriesReply_type : forall h st h' t es r st' ms, handleAppendEntriesReply h st h' t es r = (st', ms) -> (type st' = type st /\ currentTerm st' = currentTerm st) \/ type st' = Follower.
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Lemma handleAppendEntriesReply_type_term : forall h st h' t es r st' ms, handleAppendEntriesReply h st h' t es r = (st', ms) -> (type st' = type st /\ currentTerm st' = currentTerm st) \/ (type st' = Follower /\ currentTerm st' >= currentTerm st).
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Lemma handleRequestVote_type_term : forall st h h' t lli llt st' m, handleRequestVote h st t h' lli llt = (st', m) -> (type st' = type st /\ currentTerm st' = currentTerm st) \/ (type st' = Follower /\ currentTerm st' >= currentTerm st).
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
Admitted.

Lemma handleRequestVoteReply_type : forall h st h' t r st', handleRequestVoteReply h st h' t r = st' -> (type st' = type st /\ currentTerm st' = currentTerm st) \/ (type st' = Follower /\ currentTerm st' > currentTerm st) \/ (type st = Candidate /\ type st' = Leader /\ currentTerm st' = currentTerm st).
Proof using.
intros.
unfold handleRequestVoteReply, advanceCurrentTerm in *.
Admitted.

Lemma handleClientRequest_type : forall h st client id c out st' l, handleClientRequest h st client id c = (out, st', l) -> type st' = type st /\ currentTerm st' = currentTerm st.
Proof using.
intros.
unfold handleClientRequest in *.
Admitted.

Lemma handleClientRequest_currentTerm : forall h st client id c out st' l, handleClientRequest h st client id c = (out, st', l) -> currentTerm st' = currentTerm st.
Proof using.
intros.
find_apply_lem_hyp handleClientRequest_type.
Admitted.

Lemma handleTimeout_type : forall h st out st' l, handleTimeout h st = (out, st', l) -> (type st' = type st /\ currentTerm st' = currentTerm st) \/ type st' = Candidate.
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Lemma handleTimeout_type_strong : forall h st out st' l, handleTimeout h st = (out, st', l) -> (type st' = type st /\ currentTerm st' = currentTerm st) \/ (type st' = Candidate /\ currentTerm st' = S (currentTerm st)).
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Lemma doGenericServer_type : forall h st os st' ms, doGenericServer h st = (os, st', ms) -> type st' = type st /\ currentTerm st' = currentTerm st.
Proof using.
unfold doGenericServer.
intros.
Admitted.

Lemma doLeader_type : forall st h os st' ms, doLeader st h = (os, st', ms) -> type st' = type st /\ currentTerm st' = currentTerm st.
Proof using.
intros.
unfold doLeader in *.
Admitted.

Lemma doLeader_log : forall st h os st' ms, doLeader st h = (os, st', ms) -> log st' = log st.
Proof using.
unfold doLeader.
intros.
Admitted.

Lemma handleAppendEntriesReply_log : forall h st h' t es r st' ms, handleAppendEntriesReply h st h' t es r = (st', ms) -> log st' = log st.
Proof using.
unfold handleAppendEntriesReply, advanceCurrentTerm.
intros.
Admitted.

Lemma handleRequestVote_type : forall st h h' t lli llt st' m, handleRequestVote h st t h' lli llt = (st', m) -> (type st' = type st /\ currentTerm st' = currentTerm st) \/ type st' = Follower.
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
repeat break_match; find_inversion; auto.
