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

Lemma handleRequestVote_clientCache : forall n st t c li lt st' ms, handleRequestVote n st t c li lt = (st', ms) -> clientCache st' = clientCache st.
Proof using.
unfold handleRequestVote.
intros.
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

Theorem handleTimeout_clientCache : forall h st out st' ps, handleTimeout h st = (out, st', ps) -> clientCache st' = clientCache st.
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
break_match; find_inversion; subst; auto.
