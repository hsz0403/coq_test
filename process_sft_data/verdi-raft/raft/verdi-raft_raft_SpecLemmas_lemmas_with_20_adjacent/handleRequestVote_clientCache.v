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

Theorem handleClientRequest_clientCache: forall h st client id c out st' ps, handleClientRequest h st client id c = (out, st', ps) -> clientCache st' = clientCache st.
Proof using.
intros.
unfold handleClientRequest in *.
Admitted.

Lemma tryToBecomeLeader_clientCache : forall n st out st' ms, tryToBecomeLeader n st = (out, st', ms) -> clientCache st' = clientCache st.
Proof using.
unfold tryToBecomeLeader.
intros.
find_inversion.
Admitted.

Lemma handleRequestVoteReply_clientCache : forall n st src t v, clientCache (handleRequestVoteReply n st src t v) = clientCache st.
Proof using.
unfold handleRequestVoteReply.
intros.
Admitted.

Lemma doLeader_clientCache : forall st h os st' ms, doLeader st h = (os, st', ms) -> clientCache st' = clientCache st.
Proof using.
intros.
unfold doLeader in *.
Admitted.

Lemma handleAppendEntries_stateMachine: forall h st (d : raft_data) (m : msg) (t : term) (n : name) (pli : logIndex) (plt : term) (es : list entry) (ci : logIndex), handleAppendEntries h st t n pli plt es ci = (d, m) -> stateMachine d = stateMachine st.
Proof using.
intros.
unfold handleAppendEntries, advanceCurrentTerm in *.
Admitted.

Lemma handleAppendEntriesReply_stateMachine: forall h st (d : raft_data) (m : list (name * msg)) (t : nat) (es : list entry) (res : bool) h', handleAppendEntriesReply h st h' t es res = (d, m) -> stateMachine d = stateMachine st.
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Lemma advanceCurrentTerm_stateMachine : forall st t, stateMachine (advanceCurrentTerm st t) = stateMachine st.
Proof using.
unfold advanceCurrentTerm.
intros.
Admitted.

Theorem handleTimeout_stateMachine : forall h st out st' ps, handleTimeout h st = (out, st', ps) -> stateMachine st' = stateMachine st.
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Theorem handleClientRequest_stateMachine: forall h st client id c out st' ps, handleClientRequest h st client id c = (out, st', ps) -> stateMachine st' = stateMachine st.
Proof using.
intros.
unfold handleClientRequest in *.
Admitted.

Lemma tryToBecomeLeader_stateMachine : forall n st out st' ms, tryToBecomeLeader n st = (out, st', ms) -> stateMachine st' = stateMachine st.
Proof using.
unfold tryToBecomeLeader.
intros.
find_inversion.
Admitted.

Lemma handleRequestVote_stateMachine : forall n st t c li lt st' ms, handleRequestVote n st t c li lt = (st', ms) -> stateMachine st' = stateMachine st.
Proof using.
unfold handleRequestVote.
intros.
Admitted.

Lemma handleRequestVoteReply_stateMachine : forall n st src t v, stateMachine (handleRequestVoteReply n st src t v) = stateMachine st.
Proof using.
unfold handleRequestVoteReply.
intros.
Admitted.

Lemma doLeader_stateMachine : forall st h os st' ms, doLeader st h = (os, st', ms) -> stateMachine st' = stateMachine st.
Proof using.
intros.
unfold doLeader in *.
Admitted.

Lemma handleAppendEntries_matchIndex_preserved: forall h st (d : raft_data) (m : msg) (t : term) (n : name) (pli : logIndex) (plt : term) (es : list entry) (ci : logIndex), handleAppendEntries h st t n pli plt es ci = (d, m) -> matchIndex_preserved st d.
Proof using.
intros.
unfold handleAppendEntries, advanceCurrentTerm in *.
Admitted.

Lemma handleAppendEntriesReply_matchIndex_leader_preserved: forall h st (d : raft_data) (m : list (name * msg)) (t : nat) (es : list entry) (res : bool) h', handleAppendEntriesReply h st h' t es res = (d, m) -> matchIndex_preserved_except_at_host h' st d.
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
repeat (break_match; try find_inversion; simpl in *; auto); [|intros; congruence].
intros.
intuition.
unfold assoc_default.
Admitted.

Lemma advanceCurrentTerm_matchIndex_preserved : forall st t, matchIndex_preserved st (advanceCurrentTerm st t).
Proof using.
unfold advanceCurrentTerm.
intros.
Admitted.

Theorem handleTimeout_matchIndex_preserved : forall h st out st' ps, handleTimeout h st = (out, st', ps) -> matchIndex_preserved st st'.
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Theorem handleClientRequest_matchIndex_maxIndex: forall h st client id c out st' ps, handleClientRequest h st client id c = (out, st', ps) -> (maxIndex (log st') = maxIndex (log st) /\ matchIndex st' = matchIndex st) \/ (assoc_default name_eq_dec (matchIndex st') h 0) = maxIndex (log st').
Proof using.
intros.
unfold handleClientRequest in *.
break_match; find_inversion; subst; simpl in *; auto.
unfold assoc_default.
Admitted.

Theorem handleClientRequest_matchIndex : forall h st client id c out st' ps, handleClientRequest h st client id c = (out, st', ps) -> (maxIndex (log st') = maxIndex (log st) /\ matchIndex st' = matchIndex st) \/ matchIndex st' = assoc_set name_eq_dec (matchIndex st) h (maxIndex (log st')) /\ maxIndex (log st') = S (maxIndex (log st)).
Proof using.
unfold handleClientRequest.
intros.
Admitted.

Lemma tryToBecomeLeader_matchIndex_preserved : forall n st out st' ms, tryToBecomeLeader n st = (out, st', ms) -> matchIndex_preserved st st'.
Proof using.
unfold tryToBecomeLeader.
intros.
find_inversion.
Admitted.

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

Lemma handleRequestVote_clientCache : forall n st t c li lt st' ms, handleRequestVote n st t c li lt = (st', ms) -> clientCache st' = clientCache st.
Proof using.
unfold handleRequestVote.
intros.
repeat (break_match; try discriminate; repeat (find_inversion; simpl in *)); auto using advanceCurrentTerm_clientCache.
