Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Section SpecLemmas.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
End SpecLemmas.

Lemma update_elections_data_timeout_votes_intro_new : forall h st out st' ps t' h', handleTimeout h (snd st) = (out, st', ps) -> (forall t h, t = currentTerm (snd st) -> votedFor (snd st) = Some h -> In (t, h) (votes (fst st))) -> t' = currentTerm st' -> votedFor st' = Some h' -> In (t', h') (votes (update_elections_data_timeout h st)).
Proof using.
unfold update_elections_data_timeout, handleTimeout, tryToBecomeLeader.
intros.
Admitted.

Lemma votes_update_elections_data_timeout : forall h st out st' ps t' h', handleTimeout h (snd st) = (out, st', ps) -> In (t', h') (votes (update_elections_data_timeout h st)) -> In (t', h') (votes (fst st)) \/ t' = currentTerm st'.
Proof using.
unfold update_elections_data_timeout.
intros.
Admitted.

Lemma votes_update_elections_data_client_request : forall h st client id c, votes (update_elections_data_client_request h st client id c) = votes (fst st).
Proof using.
intros.
unfold update_elections_data_client_request.
Admitted.

Lemma votesWithLog_same_client_request : forall h st client id c, votesWithLog (update_elections_data_client_request h st client id c) = votesWithLog (fst st).
Proof using.
intros.
unfold update_elections_data_client_request.
Admitted.

Lemma votesWithLog_update_elections_data_client_request : forall h st client id c out st' ps t' h' l', handleClientRequest h (snd st) client id c = (out, st', ps) -> In (t', h', l') (votesWithLog (update_elections_data_client_request h st client id c)) -> In (t', h', l') (votesWithLog (fst st)).
Proof using.
unfold update_elections_data_client_request.
intros.
Admitted.

Lemma votesWithLog_update_elections_data_timeout : forall h st out st' ps t' h' l', handleTimeout h (snd st) = (out, st', ps) -> In (t', h', l') (votesWithLog (update_elections_data_timeout h st)) -> In (t', h', l') (votesWithLog (fst st)) \/ (t' = currentTerm st' /\ l' = log st').
Proof using.
unfold update_elections_data_timeout.
intros.
Admitted.

Lemma votesWithLog_same_append_entries : forall h st t n pli plt es ci, votesWithLog (update_elections_data_appendEntries h st t n pli plt es ci) = votesWithLog (fst st).
Proof using.
intros.
unfold update_elections_data_appendEntries.
Admitted.

Lemma votesWithLog_update_elections_data_append_entries : forall h st t n pli plt es ci st' ps t' h' l', handleAppendEntries h (snd st) t n pli plt es ci = (st', ps) -> In (t', h', l') (votesWithLog (update_elections_data_appendEntries h st t n pli plt es ci)) -> In (t', h', l') (votesWithLog (fst st)).
Proof using.
unfold update_elections_data_appendEntries.
intros.
Admitted.

Lemma votesWithLog_update_elections_data_request_vote : forall h st t src lli llt st' m t' h' l', handleRequestVote h (snd st) t src lli llt = (st', m) -> In (t', h', l') (votesWithLog (update_elections_data_requestVote h src t src lli llt st)) -> In (t', h', l') (votesWithLog (fst st)) \/ (t' = currentTerm st' /\ l' = log st').
Proof using.
unfold update_elections_data_requestVote.
intros.
Admitted.

Lemma votesWithLog_update_elections_data_request_vote_reply : forall h st src t r st' t' h' l', handleRequestVoteReply h (snd st) src t r = st' -> In (t', h', l') (votesWithLog (update_elections_data_requestVoteReply h src t r st)) -> In (t', h', l') (votesWithLog (fst st)).
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
Admitted.

Lemma update_elections_data_client_request_leaderLogs : forall h st client id c, leaderLogs (update_elections_data_client_request h st client id c) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_client_request in *.
intros.
Admitted.

Lemma update_elections_data_timeout_leaderLogs : forall h st, leaderLogs (update_elections_data_timeout h st) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_timeout.
intros.
Admitted.

Lemma update_elections_data_appendEntries_leaderLogs : forall h st t src pli plt es ci, leaderLogs (update_elections_data_appendEntries h st t src pli plt es ci) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_appendEntries.
intros.
Admitted.

Lemma leaderLogs_update_elections_data_requestVote : forall h src t ci lli llt st, leaderLogs (update_elections_data_requestVote h src t ci lli llt st) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_requestVote.
intros.
Admitted.

Lemma leaderLogs_update_elections_data_RVR : forall h src t1 v st t2 ll st', handleRequestVoteReply h (snd st) src t1 v = st' -> In (t2, ll) (leaderLogs (update_elections_data_requestVoteReply h src t1 v st)) -> In (t2, ll) (leaderLogs (fst st)) \/ (type st' = Leader /\ type (snd st) = Candidate /\ t2 = currentTerm st' /\ ll = log st').
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
repeat break_match; repeat find_inversion; intuition.
simpl in *.
intuition.
find_inversion.
Admitted.

Lemma update_elections_data_requestVoteReply_old : forall h src t1 v st t2 ll, In (t2, ll) (leaderLogs (fst st)) -> In (t2, ll) (leaderLogs (update_elections_data_requestVoteReply h src t1 v st)).
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
repeat break_match; repeat find_inversion; intuition.
simpl in *.
Admitted.

Lemma update_elections_data_client_request_allEntries : forall h st client id c out st' ms, handleClientRequest h (snd st) client id c = (out, st', ms) -> allEntries (update_elections_data_client_request h st client id c) = allEntries (fst st) \/ (exists e : entry, eIndex e = S (maxIndex (log (snd st))) /\ eTerm e = currentTerm (snd st) /\ eClient e = client /\ eInput e = c /\ eId e = id /\ type (snd st) = Leader /\ allEntries (update_elections_data_client_request h st client id c) = (currentTerm st', e) :: allEntries (fst st)).
Proof using.
intros.
unfold update_elections_data_client_request.
repeat break_match; repeat find_inversion; auto.
simpl.
find_copy_apply_lem_hyp handleClientRequest_log.
intuition.
-
repeat find_rewrite.
do_bool.
omega.
-
right.
break_exists_exists.
intuition.
Admitted.

Lemma update_elections_data_client_request_log_allEntries : forall h st client id c out st' ms, handleClientRequest h (snd st) client id c = (out, st', ms) -> (allEntries (update_elections_data_client_request h st client id c) = allEntries (fst st) /\ log st' = log (snd st)) \/ (type (snd st) = Leader /\ exists e : entry, eIndex e = S (maxIndex (log (snd st))) /\ eTerm e = currentTerm (snd st) /\ eClient e = client /\ eInput e = c /\ eId e = id /\ type (snd st) = Leader /\ allEntries (update_elections_data_client_request h st client id c) = (currentTerm st', e) :: allEntries (fst st) /\ log st' = e :: log (snd st)).
Proof using.
intros.
unfold update_elections_data_client_request.
unfold handleClientRequest in *.
repeat break_match; repeat tuple_inversion; auto.
-
discriminate.
-
do_bool.
find_rewrite.
omega.
-
do_bool.
find_rewrite.
omega.
-
simpl in *.
right.
intuition.
exists e.
find_inversion.
simpl.
intuition.
-
simpl in *.
do_bool.
Admitted.

Lemma update_elections_data_requestVoteReply_allEntries : forall h h' t st r, allEntries (update_elections_data_requestVoteReply h h' t r st) = allEntries (fst st).
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
Admitted.

Lemma handleAppendEntriesReply_entries : forall h st t h' pli plt es ci st' t' es', handleAppendEntries h st t h' pli plt es ci = (st', AppendEntriesReply t' es' true) -> t' = t /\ es' = es /\ (forall e, In e es -> In e (log st') \/ haveNewEntries st es = false /\ log st' = log st).
Proof using.
intros.
unfold handleAppendEntries in *.
Admitted.

Lemma update_elections_data_request_vote_reply_votesWithLog : forall (h : name) (st : electionsData * RaftState.raft_data term name entry logIndex serverType data clientId output) (src : name) (t : nat) (r : bool), votesWithLog (update_elections_data_requestVoteReply h src t r st) = votesWithLog (fst st).
Proof using.
intros.
unfold update_elections_data_requestVoteReply.
break_match; simpl in *; auto.
