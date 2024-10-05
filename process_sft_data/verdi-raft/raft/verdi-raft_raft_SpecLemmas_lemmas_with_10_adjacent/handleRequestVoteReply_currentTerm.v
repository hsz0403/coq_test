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

Lemma handleClientRequest_candidate : forall h st client id c os st' m, handleClientRequest h st client id c = (os, st', m) -> type st' = Candidate -> st' = st.
Proof using.
intros.
unfold handleClientRequest in *.
Admitted.

Lemma doLeader_candidate : forall st h os st' ms, doLeader st h = (os, st', ms) -> type st' = Candidate -> st' = st.
Proof using.
unfold doLeader, advanceCommitIndex in *.
intros.
Admitted.

Lemma doLeader_term_votedFor : forall st h os st' ms, doLeader st h = (os, st', ms) -> currentTerm st' = currentTerm st /\ votedFor st' = votedFor st.
Proof using.
unfold doLeader, advanceCommitIndex in *.
intros.
Admitted.

Lemma doGenericServer_log_type_term_votesReceived : forall h st os st' ps, doGenericServer h st = (os, st', ps) -> log st' = log st /\ type st' = type st /\ currentTerm st' = currentTerm st /\ votesReceived st' = votesReceived st /\ votedFor st' = votedFor st.
Proof using.
intros.
unfold doGenericServer in *.
Admitted.

Lemma handleClientRequest_term_votedFor : forall h st client id c os st' m, handleClientRequest h st client id c = (os, st', m) -> type st' = type st /\ currentTerm st' = currentTerm st /\ votedFor st' = votedFor st.
Proof using.
intros.
unfold handleClientRequest in *.
Admitted.

Theorem handleAppendEntries_term_votedFor : forall h st t n pli plt es ci st' ps h', handleAppendEntries h st t n pli plt es ci = (st', ps) -> votedFor st' = Some h' -> currentTerm st' = currentTerm st /\ votedFor st' = votedFor st.
Proof using.
intros.
unfold handleAppendEntries, advanceCurrentTerm in *.
Admitted.

Theorem handleAppendEntriesReply_term_votedFor : forall h st n t es r st' ps h', handleAppendEntriesReply h st n t es r = (st', ps) -> votedFor st' = Some h' -> currentTerm st' = currentTerm st /\ votedFor st' = votedFor st.
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Theorem handleRequestVoteReply_term_votedFor : forall h st t h' h'' r st', handleRequestVoteReply h st h' t r = st' -> votedFor st' = Some h'' -> currentTerm st' = currentTerm st /\ votedFor st' = votedFor st.
Proof using.
intros.
unfold handleRequestVoteReply, advanceCurrentTerm in *.
Admitted.

Lemma handleRequestVote_reply_true: forall h h' st t lli llt st' t', handleRequestVote h st t h' lli llt = (st', RequestVoteReply t' true) -> votedFor st' = Some h' /\ currentTerm st' = t'.
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
Admitted.

Lemma handleTimeout_messages: forall (out : list raft_output) (st : raft_data) (l : list (name * msg)) h (mi : logIndex) (mt : term) m st' t n, handleTimeout h st = (out, st', l) -> In m l -> snd m = RequestVote t n mi mt -> maxIndex (log st') = mi /\ maxTerm (log st') = mt /\ t = currentTerm st'.
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Lemma handleRequestVote_reply_true': forall (h : name) (h' : fin N) (st : RaftState.raft_data term name entry logIndex serverType data clientId output) (t lli llt : nat) (st' : raft_data) (t' : term), handleRequestVote h st t h' lli llt = (st', RequestVoteReply t' true) -> t' = t /\ currentTerm st' = t.
Proof using.
unfold handleRequestVote, advanceCurrentTerm in *.
intros.
Admitted.

Lemma handleRequestVoteReply_currentTerm : forall h st h' t r x, x <= currentTerm st -> x <= currentTerm (handleRequestVoteReply h st h' t r).
Proof using.
intros.
unfold handleRequestVoteReply, advanceCurrentTerm.
repeat break_match; subst; simpl in *; auto; try omega.
do_bool.
omega.
