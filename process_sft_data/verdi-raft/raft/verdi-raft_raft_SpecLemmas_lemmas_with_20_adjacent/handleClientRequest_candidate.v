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

Lemma handleRequestVote_matchIndex_preserved : forall n st t c li lt st' ms, handleRequestVote n st t c li lt = (st', ms) -> matchIndex_preserved st st'.
Proof using.
unfold handleRequestVote, advanceCurrentTerm.
intros.
Admitted.

Lemma doGenericServer_matchIndex_preserved : forall h st os st' ps, doGenericServer h st = (os, st', ps) -> matchIndex_preserved st st'.
Proof using.
intros.
unfold doGenericServer in *.
Admitted.

Lemma handleRequestVoteReply_matchIndex : forall n st src t v, type (handleRequestVoteReply n st src t v) = Leader -> (type st = Leader /\ matchIndex (handleRequestVoteReply n st src t v) = matchIndex st) \/ (assoc_default name_eq_dec (matchIndex (handleRequestVoteReply n st src t v)) n 0 = maxIndex (log (handleRequestVoteReply n st src t v))).
Proof using.
unfold handleRequestVoteReply.
intros.
repeat break_match; simpl; auto using advanceCurrentTerm_matchIndex_preserved; simpl in *; try congruence.
unfold assoc_default.
simpl.
Admitted.

Lemma doLeader_matchIndex_preserved : forall st h os st' ms, doLeader st h = (os, st', ms) -> matchIndex_preserved st st'.
Proof using.
intros.
unfold doLeader in *.
simpl; intros.
Admitted.

Lemma doLeader_lastApplied : forall st h os st' ms, doLeader st h = (os, st', ms) -> lastApplied st' = lastApplied st.
Proof using.
intros.
unfold doLeader in *.
Admitted.

Lemma handleRequestVote_no_append_entries : forall st h h' t lli llt st' m, handleRequestVote h st t h' lli llt = (st', m) -> ~ is_append_entries m.
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
Admitted.

Theorem handleClientRequest_no_append_entries : forall h st client id c out st' ps m, handleClientRequest h st client id c = (out, st', ps) -> In m ps -> ~ is_append_entries (snd m).
Proof using.
intros.
unfold handleClientRequest in *.
Admitted.

Theorem handleClientRequest_packets : forall h st client id c out st' ps, handleClientRequest h st client id c = (out, st', ps) -> ps = [].
Proof using.
intros.
unfold handleClientRequest in *.
Admitted.

Lemma handleTimeout_packets : forall h d out d' ps m, handleTimeout h d = (out, d', ps) -> In m ps -> ~ is_append_entries (snd m).
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Lemma doLeader_messages : forall st h os st' ms m t n pli plt es ci, doLeader st h = (os, st', ms) -> In m ms -> snd m = AppendEntries t n pli plt es ci -> t = currentTerm st /\ log st' = log st /\ type st = Leader /\ ((plt = 0) \/ ((exists e, findAtIndex (log st) pli = Some e /\ eTerm e = plt))).
Proof using.
intros.
unfold doLeader, advanceCommitIndex in *.
break_match; try solve [find_inversion; simpl in *; intuition].
break_if; try solve [find_inversion; simpl in *; intuition].
find_inversion.
simpl.
do_in_map.
subst.
simpl in *.
find_inversion.
intuition.
match goal with | |- context [pred ?x] => remember (pred x) as index end.
break_match; simpl in *.
-
right.
eauto.
-
Admitted.

Lemma doLeader_message_entries : forall st h os st' ms m t n pli plt es ci e, doLeader st h = (os, st', ms) -> In m ms -> snd m = AppendEntries t n pli plt es ci -> In e es -> In e (log st).
Proof using.
intros.
unfold doLeader, advanceCommitIndex in *.
break_match; try solve [find_inversion; simpl in *; intuition].
break_if; try solve [find_inversion; simpl in *; intuition].
find_inversion.
simpl.
do_in_map.
subst.
simpl in *.
find_inversion.
Admitted.

Theorem handleAppendEntries_log_term_type : forall h st t n pli plt es ci st' ps, handleAppendEntries h st t n pli plt es ci = (st', ps) -> (log st' = log st /\ currentTerm st' = currentTerm st /\ type st' = type st) \/ type st' = Follower.
Proof using.
intros.
unfold handleAppendEntries, advanceCurrentTerm in *.
Admitted.

Theorem handleAppendEntries_votesReceived : forall h st t n pli plt es ci st' ps, handleAppendEntries h st t n pli plt es ci = (st', ps) -> votesReceived st' = votesReceived st.
Proof using.
intros.
unfold handleAppendEntries, advanceCurrentTerm in *.
Admitted.

Theorem handleAppendEntriesReply_log_term_type : forall h st n t es r st' ps, handleAppendEntriesReply h st n t es r = (st', ps) -> (log st' = log st /\ currentTerm st' = currentTerm st /\ type st' = type st) \/ type st' = Follower.
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Theorem handleAppendEntriesReply_votesReceived : forall h st n t es r st' ps, handleAppendEntriesReply h st n t es r = (st', ps) -> votesReceived st' = votesReceived st.
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Theorem handleRequestVote_log_term_type : forall h st t c li lt st' m, handleRequestVote h st t c li lt = (st', m) -> (log st' = log st /\ currentTerm st' = currentTerm st /\ type st' = type st) \/ type st' = Follower.
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
Admitted.

Theorem handleRequestVote_votesReceived : forall h st t c li lt st' m, handleRequestVote h st t c li lt = (st', m) -> votesReceived st' = votesReceived st.
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
Admitted.

Theorem handleRequestVoteReply_log_term_type : forall h st t h' r st', type st' = Candidate -> handleRequestVoteReply h st h' t r = st' -> (log st' = log st /\ currentTerm st' = currentTerm st /\ type st' = type st).
Proof using.
intros.
unfold handleRequestVoteReply, advanceCurrentTerm in *.
Admitted.

Theorem handleRequestVoteReply_votesReceived : forall h st t h' r v, In v (votesReceived (handleRequestVoteReply h st h' t r)) -> In v (votesReceived st) \/ (r = true /\ v = h' /\ currentTerm (handleRequestVoteReply h st h' t r) = t).
Proof using.
intros.
unfold handleRequestVoteReply, advanceCurrentTerm in *.
Admitted.

Theorem handleTimeout_log_term_type : forall h st out st' ps, handleTimeout h st = (out, st', ps) -> (log st' = log st /\ currentTerm st' = currentTerm st /\ type st' = type st) \/ currentTerm st' = S (currentTerm st).
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
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

Lemma handleRequestVoteReply_currentTerm : forall h st h' t r x, x <= currentTerm st -> x <= currentTerm (handleRequestVoteReply h st h' t r).
Proof using.
intros.
unfold handleRequestVoteReply, advanceCurrentTerm.
repeat break_match; subst; simpl in *; auto; try omega.
do_bool.
Admitted.

Lemma handleRequestVote_reply_true': forall (h : name) (h' : fin N) (st : RaftState.raft_data term name entry logIndex serverType data clientId output) (t lli llt : nat) (st' : raft_data) (t' : term), handleRequestVote h st t h' lli llt = (st', RequestVoteReply t' true) -> t' = t /\ currentTerm st' = t.
Proof using.
unfold handleRequestVote, advanceCurrentTerm in *.
intros.
Admitted.

Lemma handleClientRequest_candidate : forall h st client id c os st' m, handleClientRequest h st client id c = (os, st', m) -> type st' = Candidate -> st' = st.
Proof using.
intros.
unfold handleClientRequest in *.
repeat break_match; find_inversion; simpl in *; congruence.
