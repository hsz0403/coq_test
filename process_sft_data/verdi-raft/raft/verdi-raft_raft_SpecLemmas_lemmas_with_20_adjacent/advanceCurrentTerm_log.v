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

Theorem handleAppendEntries_log : forall h st t n pli plt es ci st' ps, handleAppendEntries h st t n pli plt es ci = (st', ps) -> log st' = log st \/ (currentTerm st <= t /\ es <> [] /\ pli = 0 /\ log st' = es) \/ (currentTerm st <= t /\ es <> [] /\ pli <> 0 /\ exists e, In e (log st) /\ eIndex e = pli /\ eTerm e = plt) /\ log st' = es ++ (removeAfterIndex (log st) pli).
Proof using.
intros.
unfold handleAppendEntries in *.
break_if; [find_inversion; subst; eauto|].
break_if; [do_bool; break_if; find_inversion; subst; try find_apply_lem_hyp haveNewEntries_not_empty; intuition; simpl in *; eauto using advanceCurrentTerm_log|].
break_if.
-
break_match; [|find_inversion; subst; eauto].
break_if; [find_inversion; subst; eauto|].
find_inversion; subst; simpl in *.
right.
right.
find_apply_lem_hyp findAtIndex_elim.
intuition; do_bool; eauto.
find_apply_lem_hyp haveNewEntries_not_empty.
congruence.
-
repeat break_match; find_inversion; subst; eauto.
simpl in *.
Admitted.

Theorem handleAppendEntries_log_ind : forall {h st t n pli plt es ci st' ps}, handleAppendEntries h st t n pli plt es ci = (st', ps) -> forall (P : list entry -> Prop), P (log st) -> (pli = 0 -> P es) -> (forall e, pli <> 0 -> In e (log st) -> eIndex e = pli -> eTerm e = plt -> P (es ++ (removeAfterIndex (log st) pli))) -> P (log st').
Proof using.
intros.
find_apply_lem_hyp handleAppendEntries_log.
intuition; subst; try find_rewrite; auto.
break_exists.
Admitted.

Lemma haveNewEntries_true : forall st es, haveNewEntries st es = true -> (es <> nil /\ (findAtIndex (log st) (maxIndex es) = None \/ exists e, findAtIndex (log st) (maxIndex es) = Some e /\ eTerm e <> maxTerm es)).
Proof using.
intros.
unfold haveNewEntries, not_empty in *.
repeat break_match; do_bool; intuition eauto; try congruence.
do_bool.
Admitted.

Lemma advanceCurrentTerm_commitIndex : forall st t, commitIndex (advanceCurrentTerm st t) = commitIndex st.
Proof using.
intros.
unfold advanceCurrentTerm.
Admitted.

Lemma some_none : forall A (x : A), Some x = None -> False.
Proof using.
Admitted.

Lemma advanceCurrentTerm_term : forall st t, currentTerm st <= t -> currentTerm (advanceCurrentTerm st t) = t.
Proof using.
intros.
unfold advanceCurrentTerm in *.
Admitted.

Theorem handleAppendEntries_log_detailed : forall h st t n pli plt es ci st' ps, handleAppendEntries h st t n pli plt es ci = (st', ps) -> (commitIndex st' = commitIndex st /\ log st' = log st) \/ (leaderId st' <> None /\ currentTerm st' = t /\ commitIndex st' = max (commitIndex st) (min ci (maxIndex es)) /\ es <> nil /\ pli = 0 /\ t >= currentTerm st /\ log st' = es /\ (findAtIndex (log st) (maxIndex es) = None \/ exists e, findAtIndex (log st) (maxIndex es) = Some e /\ eTerm e <> maxTerm es)) \/ (leaderId st' <> None /\ currentTerm st' = t /\ commitIndex st' = max (commitIndex st) (min ci (maxIndex (es ++ (removeAfterIndex (log st) pli)))) /\ es <> nil /\ exists e, In e (log st) /\ eIndex e = pli /\ eTerm e = plt) /\ t >= currentTerm st /\ log st' = es ++ (removeAfterIndex (log st) pli) /\ (findAtIndex (log st) (maxIndex es) = None \/ exists e, findAtIndex (log st) (maxIndex es) = Some e /\ eTerm e <> maxTerm es).
Proof using.
intros.
unfold handleAppendEntries in *.
break_if; [find_inversion; subst; eauto|].
break_if; [do_bool; break_if; find_inversion; subst; try find_apply_lem_hyp haveNewEntries_true; simpl in *; intuition eauto using advanceCurrentTerm_log, advanceCurrentTerm_commitIndex, some_none, advanceCurrentTerm_term|].
simpl in *.
intuition eauto using advanceCurrentTerm_log, advanceCurrentTerm_commitIndex.
break_match; [|find_inversion; subst; eauto].
break_if; [find_inversion; subst; eauto|].
break_if; [|find_inversion; subst; eauto using advanceCurrentTerm_log, advanceCurrentTerm_commitIndex].
find_inversion; subst; simpl in *.
right.
right.
find_apply_lem_hyp findAtIndex_elim.
Admitted.

Lemma advanceCurrentTerm_currentTerm_leaderId : forall st t, currentTerm st < currentTerm (advanceCurrentTerm st t) \/ leaderId (advanceCurrentTerm st t) = leaderId st.
Proof using.
intros.
unfold advanceCurrentTerm in *.
Admitted.

Lemma advanceCurrentTerm_currentTerm : forall st t, currentTerm st <= currentTerm (advanceCurrentTerm st t).
Proof using.
intros.
unfold advanceCurrentTerm in *.
Admitted.

Lemma handleRequestVote_currentTerm_monotonic : forall pDst t cid lli llt d d' m, handleRequestVote pDst d t cid lli llt = (d', m) -> currentTerm d <= currentTerm d'.
Proof using.
intros.
unfold handleRequestVote in *.
Admitted.

Lemma handleRequestVote_currentTerm_votedFor : forall pDst t cid lli llt d d' m, handleRequestVote pDst d t cid lli llt = (d', m) -> (currentTerm d < currentTerm d' \/ (currentTerm d = currentTerm d' /\ votedFor d = None) \/ (currentTerm d = currentTerm d' /\ votedFor d = votedFor d')).
Proof using.
intros.
find_copy_apply_lem_hyp handleRequestVote_currentTerm_monotonic.
find_apply_lem_hyp le_lt_or_eq.
intuition.
right.
Admitted.

Lemma handleRequestVoteReply_currentTerm' : forall h st h' t r st', handleRequestVoteReply h st h' t r = st' -> currentTerm st <= currentTerm st'.
Proof using.
intros.
unfold handleRequestVoteReply in *.
repeat break_match; subst; do_bool; intuition.
Admitted.

Lemma handleRequestVote_currentTerm : forall st h h' t lli llt st' m, handleRequestVote h st t h' lli llt = (st', m) -> currentTerm st <= currentTerm st'.
Proof using.
intros.
unfold handleRequestVote in *.
Admitted.

Theorem handleAppendEntries_currentTerm_leaderId : forall h st t n pli plt es ci st' ps, handleAppendEntries h st t n pli plt es ci = (st', ps) -> currentTerm st < currentTerm st' \/ (currentTerm st <= currentTerm st' /\ (leaderId st' = leaderId st \/ leaderId st' <> None)).
Proof using.
intros.
unfold handleAppendEntries in *.
Admitted.

Lemma handleRequestVote_currentTerm_leaderId : forall h st t c li lt st' m, handleRequestVote h st t c li lt = (st', m) -> currentTerm st < currentTerm st' \/ (currentTerm st = currentTerm st' /\ leaderId st' = leaderId st).
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
Admitted.

Lemma handleRequestVoteReply_currentTerm_leaderId : forall h st h' t r st', handleRequestVoteReply h st h' t r = st' -> currentTerm st < currentTerm st' \/ currentTerm st' = currentTerm st /\ leaderId st' = leaderId st.
Proof using.
intros.
unfold handleRequestVoteReply, advanceCurrentTerm in *.
subst.
Admitted.

Theorem handleClientRequest_log : forall h st client id c out st' ps, handleClientRequest h st client id c = (out, st', ps) -> ps = [] /\ (log st' = log st \/ exists e, log st' = e :: log st /\ eIndex e = S (maxIndex (log st)) /\ eTerm e = currentTerm st /\ eClient e = client /\ eInput e = c /\ eId e = id /\ type st = Leader).
Proof using.
intros.
unfold handleClientRequest in *.
break_match; find_inversion; subst; intuition.
simpl in *.
Admitted.

Lemma handleClientRequest_log_ind : forall {h st client id c out st' ps}, handleClientRequest h st client id c = (out, st', ps) -> forall (P : list entry -> Prop), P (log st) -> (forall e, eIndex e = S (maxIndex (log st)) -> eTerm e = currentTerm st -> eClient e = client -> eInput e = c -> eId e = id -> type st = Leader -> P (e :: log st)) -> P (log st').
Proof using.
intros.
find_apply_lem_hyp handleClientRequest_log.
intuition; repeat find_rewrite; auto.
break_exists.
intuition.
repeat find_rewrite.
Admitted.

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

Lemma advanceCurrentTerm_log : forall st t, log (advanceCurrentTerm st t) = log st.
Proof using.
intros.
unfold advanceCurrentTerm.
break_if; simpl in *; auto.
