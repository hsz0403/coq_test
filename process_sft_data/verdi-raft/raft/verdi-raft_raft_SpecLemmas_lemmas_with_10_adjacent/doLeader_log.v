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

Lemma handleAppendEntriesReply_type_term : forall h st h' t es r st' ms, handleAppendEntriesReply h st h' t es r = (st', ms) -> (type st' = type st /\ currentTerm st' = currentTerm st) \/ (type st' = Follower /\ currentTerm st' >= currentTerm st).
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Lemma handleRequestVote_type : forall st h h' t lli llt st' m, handleRequestVote h st t h' lli llt = (st', m) -> (type st' = type st /\ currentTerm st' = currentTerm st) \/ type st' = Follower.
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
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

Lemma handleAppendEntriesReply_log : forall h st h' t es r st' ms, handleAppendEntriesReply h st h' t es r = (st', ms) -> log st' = log st.
Proof using.
unfold handleAppendEntriesReply, advanceCurrentTerm.
intros.
Admitted.

Lemma handleRequestVoteReply_log : forall h st h' t r st', handleRequestVoteReply h st h' t r = st' -> log st' = log st.
Proof using.
intros.
Admitted.

Lemma handleRequestVoteReply_log_rewrite : forall h st h' t r, log (handleRequestVoteReply h st h' t r) = log st.
Proof using.
intros.
Admitted.

Lemma handleAppendEntriesReply_packets : forall h st from t es s st' ps, handleAppendEntriesReply h st from t es s = (st', ps) -> ps = [].
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Lemma doGenericServer_packets : forall h st os st' ps, doGenericServer h st = (os, st', ps) -> ps = [].
Proof using.
intros.
unfold doGenericServer in *.
Admitted.

Theorem handleAppendEntries_not_append_entries : forall h st t n pli plt es ci st' m, handleAppendEntries h st t n pli plt es ci = (st', m) -> ~ is_append_entries m.
Proof using.
intros.
unfold handleAppendEntries in *.
Admitted.

Lemma handleAppendEntries_clientCache: forall h st (d : raft_data) (m : msg) (t : term) (n : name) (pli : logIndex) (plt : term) (es : list entry) (ci : logIndex), handleAppendEntries h st t n pli plt es ci = (d, m) -> clientCache d = clientCache st.
Proof using.
intros.
unfold handleAppendEntries, advanceCurrentTerm in *.
Admitted.

Lemma handleAppendEntriesReply_clientCache: forall h st (d : raft_data) (m : list (name * msg)) (t : nat) (es : list entry) (res : bool) h', handleAppendEntriesReply h st h' t es res = (d, m) -> clientCache d = clientCache st.
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Lemma advanceCurrentTerm_clientCache : forall st t, clientCache (advanceCurrentTerm st t) = clientCache st.
Proof using.
unfold advanceCurrentTerm.
intros.
Admitted.

Theorem handleTimeout_clientCache : forall h st out st' ps, handleTimeout h st = (out, st', ps) -> clientCache st' = clientCache st.
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Lemma doLeader_log : forall st h os st' ms, doLeader st h = (os, st', ms) -> log st' = log st.
Proof using.
unfold doLeader.
intros.
repeat break_match; find_inversion; simpl in *; auto.
