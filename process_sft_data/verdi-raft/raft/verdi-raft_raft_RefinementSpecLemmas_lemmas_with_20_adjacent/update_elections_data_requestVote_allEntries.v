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

Lemma update_elections_data_appendEntries_allEntries : forall h st t h' pli plt es ci e, In e (map snd (allEntries (update_elections_data_appendEntries h st t h' pli plt es ci))) -> In e (map snd (allEntries (fst st))) \/ In e es.
Proof using.
intros.
unfold update_elections_data_appendEntries in *.
repeat break_match; subst; simpl in *; auto.
find_apply_lem_hyp handleAppendEntriesReply_entries.
subst.
do_in_map.
do_in_app.
subst.
intuition.
-
do_in_map.
subst.
simpl in *.
auto.
-
left.
apply in_map_iff.
Admitted.

Lemma update_elections_data_appendEntries_allEntries_term : forall h st t h' pli plt es ci te e, In (te, e) (allEntries (update_elections_data_appendEntries h st t h' pli plt es ci)) -> In (te, e) (allEntries (fst st)) \/ (In e es /\ te = t).
Proof using.
intros.
unfold update_elections_data_appendEntries in *.
repeat break_match; subst; simpl in *; auto.
find_apply_lem_hyp handleAppendEntriesReply_entries.
intuition.
subst.
do_in_app.
intuition.
do_in_map.
repeat find_inversion.
subst.
simpl in *.
Admitted.

Lemma update_elections_data_appendEntries_allEntries_term' : forall h st t h' pli plt es ci te e d m, In (te, e) (allEntries (update_elections_data_appendEntries h st t h' pli plt es ci)) -> handleAppendEntries h (snd st) t h' pli plt es ci = (d, m) -> In (te, e) (allEntries (fst st)) \/ (In e es /\ te = currentTerm d).
Proof using.
intros.
unfold update_elections_data_appendEntries in *.
repeat break_match; subst; simpl in *; auto.
unfold handleAppendEntries, advanceCurrentTerm in *.
Admitted.

Lemma update_elections_data_appendEntries_log_allEntries : forall h st t n pli plt es ci st' h' ps, handleAppendEntries h (snd st) t n pli plt es ci = (st', ps) -> (log st' = log (snd st) /\ allEntries (update_elections_data_appendEntries h st t h' pli plt es ci) = allEntries (fst st)) \/ (allEntries (update_elections_data_appendEntries h st t h' pli plt es ci) = (map (fun e => (t, e)) es) ++ allEntries (fst st) /\ ((currentTerm st' = t /\ log st' = log (snd st) /\ haveNewEntries (snd st) es = false) \/ (currentTerm st' = t /\ currentTerm (snd st) <= t /\ es <> [] /\ pli = 0 /\ log st' = es) \/ (currentTerm st' = t /\ currentTerm (snd st) <= t /\ es <> [] /\ pli <> 0 /\ exists e, In e (log (snd st)) /\ eIndex e = pli /\ eTerm e = plt) /\ log st' = es ++ (removeAfterIndex (log (snd st)) pli))).
Proof using.
intros.
unfold update_elections_data_appendEntries, handleAppendEntries in *.
repeat break_match; repeat find_inversion; auto; simpl in *.
-
right.
intuition.
right.
left.
do_bool.
intuition; eauto using advanceCurrentTerm_term.
find_apply_lem_hyp haveNewEntries_not_empty.
congruence.
-
rewrite advanceCurrentTerm_log.
right.
intuition.
left.
intuition.
do_bool.
eauto using advanceCurrentTerm_term.
-
right.
intuition.
right.
right.
do_bool.
intuition.
+
eauto using advanceCurrentTerm_term.
+
find_apply_lem_hyp haveNewEntries_not_empty.
congruence.
+
find_apply_lem_hyp findAtIndex_elim.
intuition; do_bool; eauto.
-
rewrite advanceCurrentTerm_log.
do_bool.
rewrite advanceCurrentTerm_term; auto.
Admitted.

Lemma update_elections_data_appendEntries_allEntries_detailed : forall h st t h' pli plt es ci st' m te e, handleAppendEntries h (snd st) t h' pli plt es ci = (st', m) -> In (te, e) (allEntries (update_elections_data_appendEntries h st t h' pli plt es ci)) -> In (te, e) (allEntries (fst st)) \/ In e (log st') \/ (In e es /\ haveNewEntries (snd st) es = false /\ log st' = log (snd st)).
Proof using.
intros.
unfold update_elections_data_appendEntries in *.
repeat break_match; subst; simpl in *; auto.
find_apply_lem_hyp handleAppendEntriesReply_entries.
intuition.
find_inversion.
do_in_app.
intuition.
do_in_map.
find_inversion.
find_copy_apply_hyp_hyp.
Admitted.

Lemma update_elections_data_clientRequest_allEntries_new : forall h st client id c e, In e (map snd (allEntries (update_elections_data_client_request h st client id c))) -> In e (map snd (allEntries (fst st))) \/ (eIndex e = S (maxIndex (log (snd st))) /\ eTerm e = currentTerm (snd st) /\ type (snd st) = Leader).
Proof using.
intros.
unfold update_elections_data_client_request in *.
repeat break_match; subst; simpl in *; auto.
intuition.
subst.
do_bool.
find_apply_lem_hyp handleClientRequest_log.
intuition.
-
match goal with | H : log _ = log (snd _) |- _ => symmetry in H end.
repeat find_rewrite.
simpl in *.
omega.
-
break_exists.
intuition.
repeat find_rewrite.
find_inversion.
Admitted.

Lemma update_elections_data_clientRequest_allEntries_old : forall h st client id c e, In e (map snd (allEntries (fst st))) -> In e (map snd (allEntries (update_elections_data_client_request h st client id c))).
Proof using.
intros.
unfold update_elections_data_client_request in *.
Admitted.

Lemma update_elections_data_clientRequest_allEntries_old' : forall h st client id c x, In x (allEntries (fst st)) -> In x (allEntries (update_elections_data_client_request h st client id c)).
Proof using.
intros.
unfold update_elections_data_client_request in *.
Admitted.

Lemma update_elections_data_timeout_allEntries : forall h st, allEntries (update_elections_data_timeout h st) = allEntries (fst st).
Proof using.
intros.
unfold update_elections_data_timeout.
Admitted.

Lemma update_elections_data_client_request_cronies : forall h st client id c out st' ms, handleClientRequest h (snd st) client id c = (out, st', ms) -> cronies (update_elections_data_client_request h st client id c) = cronies (fst st).
Proof using.
intros.
unfold update_elections_data_client_request.
Admitted.

Lemma update_elections_data_appendEntries_cronies : forall h st t h' pli plt es ci, cronies (update_elections_data_appendEntries h st t h' pli plt es ci) = cronies (fst st).
Proof using.
intros.
unfold update_elections_data_appendEntries in *.
Admitted.

Lemma update_elections_data_clientRequest_cronies_new : forall h st client id c, cronies (update_elections_data_client_request h st client id c) = cronies (fst st).
Proof using.
intros.
unfold update_elections_data_client_request in *.
Admitted.

Lemma update_elections_data_timeout_cronies : forall h st t, cronies (update_elections_data_timeout h st) t = cronies (fst st) t \/ (cronies (update_elections_data_timeout h st) t = [h] /\ t = S (currentTerm (snd st))).
Proof using.
intros.
unfold update_elections_data_timeout.
repeat break_match; simpl; auto.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Lemma update_elections_data_requestVote_cronies : forall h h' t lli llt st, cronies (update_elections_data_requestVote h h' t h' lli llt st) = cronies (fst st).
Proof using.
unfold update_elections_data_requestVote.
intros.
Admitted.

Lemma update_elections_data_appendEntries_preserves_allEntries : forall net h t n pli plt es ci x, In x (allEntries (fst (nwState net h))) -> In x (allEntries (update_elections_data_appendEntries h (nwState net h) t n pli plt es ci)).
Proof using.
unfold update_elections_data_appendEntries.
intros.
break_let.
break_match; auto.
break_if; auto.
simpl.
Admitted.

Lemma update_elections_data_request_vote_votesWithLog_old : forall (h : name) (st : electionsData * RaftState.raft_data term name entry logIndex serverType data clientId output) (t : nat) (src : fin N) (lli llt : nat) (t' : term) (h' : name) (l' : list entry), In (t', h', l') (votesWithLog (fst st)) -> In (t', h', l') (votesWithLog (update_elections_data_requestVote h src t src lli llt st)).
Proof using.
intros.
unfold update_elections_data_requestVote in *.
Admitted.

Lemma update_elections_data_timeout_votesWithLog_old : forall h st t h' l, In (t, h', l) (votesWithLog (fst st)) -> In (t, h', l) (votesWithLog (update_elections_data_timeout h st)).
Proof using.
intros.
unfold update_elections_data_timeout.
Admitted.

Lemma update_elections_data_timeout_votesWithLog_votesReceived : forall h st out st' ps, handleTimeout h (snd st) = (out, st', ps) -> (votesReceived st' = votesReceived (snd st) /\ votesWithLog (update_elections_data_timeout h st) = votesWithLog (fst st) /\ type st' = Leader) \/ (votesReceived st' = [h] /\ votesWithLog (update_elections_data_timeout h st) = (currentTerm st', h, (log st')) :: votesWithLog (fst st) /\ currentTerm st' = S (currentTerm (snd st))).
Proof using.
unfold update_elections_data_timeout, handleTimeout, tryToBecomeLeader in *.
intros.
Admitted.

Lemma update_elections_data_timeout_votedFor : forall h cid st out st' m, handleTimeout h (snd st) = (out, st', m) -> votedFor st' = Some cid -> (votedFor (snd st) = Some cid /\ currentTerm st' = currentTerm (snd st) /\ type st' = type (snd st) /\ votesWithLog (update_elections_data_timeout h st) = votesWithLog (fst st)) \/ (cid = h /\ currentTerm st' = S (currentTerm (snd st)) /\ votesWithLog (update_elections_data_timeout h st) = (currentTerm st', cid, (log st')) :: votesWithLog (fst st)).
Proof using.
intros.
unfold update_elections_data_timeout.
repeat find_rewrite.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Lemma update_elections_data_request_vote_votedFor : forall h h' cid t lli llt st st' m, handleRequestVote h (snd st) t h' lli llt = (st', m) -> votedFor st' = Some cid -> (votedFor (snd st) = Some cid /\ currentTerm st' = currentTerm (snd st)) \/ (cid = h' /\ currentTerm st' = t /\ votesWithLog (update_elections_data_requestVote h h' t h' lli llt st) = (currentTerm st', cid, (log st')) :: votesWithLog (fst st) /\ moreUpToDate llt lli (maxTerm (log st')) (maxIndex (log st')) = true).
Proof using.
intros.
unfold update_elections_data_requestVote.
repeat find_rewrite.
unfold handleRequestVote, advanceCurrentTerm in *.
repeat break_match; repeat find_inversion; simpl in *; auto; try congruence; find_inversion; auto; do_bool; intuition; try congruence.
do_bool.
subst.
Admitted.

Lemma update_elections_data_requestVote_allEntries : forall h h' t lli llt st, allEntries (update_elections_data_requestVote h h' t h' lli llt st) = allEntries (fst st).
Proof using.
unfold update_elections_data_requestVote.
intros.
repeat break_match; auto.
