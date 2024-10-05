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

Lemma votes_update_elections_data_request_vote_reply : forall h st src t r st' t' h', handleRequestVoteReply h (snd st) src t r = st' -> In (t', h') (votes (update_elections_data_requestVoteReply h src t r st)) -> In (t', h') (votes (fst st)).
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
Admitted.

Lemma votes_same_append_entries : forall h st t n pli plt es ci, votes (update_elections_data_appendEntries h st t n pli plt es ci) = votes (fst st).
Proof using.
intros.
unfold update_elections_data_appendEntries.
Admitted.

Lemma votes_update_elections_data_timeout_votedFor : forall h st out st' ps t' h', handleTimeout h (snd st) = (out, st', ps) -> In (t', h') (votes (update_elections_data_timeout h st)) -> In (t', h') (votes (fst st)) \/ t' = currentTerm st' /\ t' = S (currentTerm (snd st)) /\ votedFor st' = Some h'.
Proof using.
unfold update_elections_data_timeout, handleTimeout, tryToBecomeLeader.
intros.
Admitted.

Lemma handleTimeout_same_term_votedFor_preserved : forall h st out st' ps, handleTimeout h st = (out, st', ps) -> currentTerm st' = currentTerm st -> votedFor st' = votedFor st.
Proof using.
unfold handleTimeout, tryToBecomeLeader.
intros.
Admitted.

Lemma votes_update_elections_data_request_vote_reply_eq : forall h st src t r st', handleRequestVoteReply h (snd st) src t r = st' -> votes (update_elections_data_requestVoteReply h src t r st) = votes (fst st).
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
Admitted.

Lemma votes_update_elections_data_request_vote_intro : forall h st t src lli llt st' m h', handleRequestVote h (snd st) t src lli llt = (st', m) -> votedFor st' = Some h' -> currentTerm (snd st) < currentTerm st' \/ votedFor (snd st) = None -> In (currentTerm st', h') (votes (update_elections_data_requestVote h src t src lli llt st)).
Proof using.
unfold update_elections_data_requestVote.
intros.
repeat break_match; repeat tuple_inversion; do_bool; intuition; simpl in *; intuition; do_bool; try discriminate; intuition try congruence.
Admitted.

Lemma votes_update_elections_data_request_vote_intro_old : forall h st t src lli llt st' m t' h', handleRequestVote h (snd st) t src lli llt = (st', m) -> In (t', h') (votes (fst st)) -> In (t', h') (votes (update_elections_data_requestVote h src t src lli llt st)).
Proof using.
unfold update_elections_data_requestVote.
intros.
Admitted.

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

Lemma update_elections_data_request_vote_reply_votesWithLog : forall (h : name) (st : electionsData * RaftState.raft_data term name entry logIndex serverType data clientId output) (src : name) (t : nat) (r : bool), votesWithLog (update_elections_data_requestVoteReply h src t r st) = votesWithLog (fst st).
Proof using.
intros.
unfold update_elections_data_requestVoteReply.
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

Lemma votesWithLog_same_client_request : forall h st client id c, votesWithLog (update_elections_data_client_request h st client id c) = votesWithLog (fst st).
Proof using.
intros.
unfold update_elections_data_client_request.
repeat break_match; auto.
