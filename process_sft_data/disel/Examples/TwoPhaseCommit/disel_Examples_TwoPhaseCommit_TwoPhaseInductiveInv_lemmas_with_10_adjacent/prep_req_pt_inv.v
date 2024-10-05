From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX DepMaps Protocols Worlds NetworkSem Rely.
From DiSeL Require Import Actions Injection Process Always HoareTriples InferenceRules.
From DiSeL Require Import InductiveInv While StatePredicates.
From DiSeL Require Import TwoPhaseProtocol.
Require Import Omega.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Section TwoPhaseInductiveInv.
Variable l : Label.
Variables (cn : nid) (pts : seq nid) (others : seq nid).
Hypothesis Hnin : cn \notin pts.
Hypothesis PtsNonEmpty : pts != [::].
Definition tpc := TwoPhaseCommitProtocol others Hnin l.
Notation sts := (snd_trans tpc).
Notation rts := (rcv_trans tpc).
Notation loc z d := (getLocal z d).
Definition cn_state (d : dstatelet) (c : CStateT) (l : Log) : Prop := loc cn d = st :-> c \+ log :-> l.
Definition pt_state (d : dstatelet) (p : PStateT) (l : Log) (pt : nid) : Prop := loc pt d = st :-> p \+ log :-> l.
Definition EverythingInit (d : dstatelet) (round : nat) (l : Log) : Prop := [/\ cn_state d (round, CInit) l & forall pt, pt \in pts -> [/\ pt_state d (round, PInit) l pt, no_msg_from_to pt cn (dsoup d) & no_msg_from_to cn pt (dsoup d)]].
Definition pt_PhaseOne (d : dstatelet) (round : nat) (next_data : data) (l : Log) (pt : nid) : Prop := [\/ [/\ pt_state d (round, PInit) l pt, no_msg_from_to pt cn (dsoup d) & msg_spec cn pt prep_req (round :: next_data) (dsoup d)] , [/\ pt_state d (round, PGotRequest next_data) l pt, no_msg_from_to pt cn (dsoup d) & no_msg_from_to cn pt (dsoup d)] , [/\ pt_state d (round, PRespondedYes next_data) l pt, no_msg_from_to cn pt (dsoup d) & msg_spec pt cn prep_yes [::round] (dsoup d)] | [/\ pt_state d (round, PRespondedNo next_data) l pt, no_msg_from_to cn pt (dsoup d) & msg_spec pt cn prep_no [::round] (dsoup d)]].
Definition pt_PhaseOneResponded (d : dstatelet) (round : nat) (next_data : data) (l : Log) (committed : bool) (pt : nid) : Prop := [/\ no_msg_from_to cn pt (dsoup d), no_msg_from_to pt cn (dsoup d) & if committed then pt_state d (round, PRespondedYes next_data) l pt else pt_state d (round, PRespondedNo next_data) l pt].
Definition pt_Init d round l pt := [/\ pt_state d (round, PInit) l pt, no_msg_from_to pt cn (dsoup d) & no_msg_from_to cn pt (dsoup d)].
Definition cn_PhaseOneSend d round next_data l sent := [/\ cn_state d (round, CSentPrep next_data sent) l, uniq sent, {subset sent <= pts} & forall pt, pt \in pts -> if pt \in sent then pt_PhaseOne d round next_data l pt else pt_Init d round l pt].
Definition cn_PhaseOneReceive d round next_data l recvd := let rps := map fst recvd in [/\ cn_state d (round, CWaitPrepResponse next_data recvd) l, uniq rps, {subset rps <= pts} , forall pt b, pt \in pts -> (pt, b) \in recvd -> pt_PhaseOneResponded d round next_data l b pt & forall pt, pt \in pts -> pt \notin rps -> pt_PhaseOne d round next_data l pt].
Definition PhaseOne (d : dstatelet) (round : nat) (next_data : data) (l : Log) := (exists sent, cn_PhaseOneSend d round next_data l sent) \/ (exists recvd, cn_PhaseOneReceive d round next_data l recvd).
Definition pt_PhaseTwoCommit d round next_data l pt := [\/ [/\ pt_state d (round, PRespondedYes next_data) l pt, msg_spec cn pt commit_req [::round] (dsoup d) & no_msg_from_to pt cn (dsoup d)] , [/\ pt_state d (round, PCommitted next_data) (rcons l (true, next_data)) pt, no_msg_from_to cn pt (dsoup d) & no_msg_from_to pt cn (dsoup d)] | [/\ pt_state d (round.+1, PInit) (rcons l (true, next_data)) pt, no_msg_from_to cn pt (dsoup d) & msg_spec pt cn commit_ack [::round] (dsoup d) ]].
Definition pt_PhaseTwoAbort d round next_data l pt := [\/ [/\ (pt_state d (round, PRespondedYes next_data) l pt \/ pt_state d (round, PRespondedNo next_data) l pt), msg_spec cn pt abort_req [::round] (dsoup d) & no_msg_from_to pt cn (dsoup d)] , [/\ pt_state d (round, PAborted next_data) (rcons l (false, next_data)) pt, no_msg_from_to cn pt (dsoup d) & no_msg_from_to pt cn (dsoup d)] | [/\ pt_state d (round.+1, PInit) (rcons l (false, next_data)) pt, no_msg_from_to cn pt (dsoup d) & msg_spec pt cn abort_ack [::round] (dsoup d) ]].
Definition pt_PhaseTwoResponded d round next_data l b pt := [/\ pt_state d (round.+1, PInit) (rcons l (b, next_data)) pt, no_msg_from_to cn pt (dsoup d) & no_msg_from_to pt cn (dsoup d)].
Definition cn_PhaseTwoSendCommits d round next_data l sent := [/\ cn_state d (round, CSentCommit next_data sent) l, uniq sent, {subset sent <= pts} & forall pt, pt \in pts -> if pt \in sent then pt_PhaseTwoCommit d round next_data l pt else pt_PhaseOneResponded d round next_data l true pt].
Definition cn_PhaseTwoSendAborts d round next_data l sent := [/\ cn_state d (round, CSentAbort next_data sent) l, uniq sent, {subset sent <= pts} & forall pt, pt \in pts -> if pt \in sent then pt_PhaseTwoAbort d round next_data l pt else exists b, pt_PhaseOneResponded d round next_data l b pt].
Definition cn_PhaseTwoReceiveCommits d round next_data l recvd := [/\ cn_state d (round, CWaitAckCommit next_data recvd) l, uniq recvd, {subset recvd <= pts} & forall pt, pt \in pts -> if pt \in recvd then pt_PhaseTwoResponded d round next_data l true pt else pt_PhaseTwoCommit d round next_data l pt].
Definition cn_PhaseTwoReceiveAborts d round next_data l recvd := [/\ cn_state d (round, CWaitAckAbort next_data recvd) l, uniq recvd, {subset recvd <= pts} & forall pt, pt \in pts -> if pt \in recvd then pt_PhaseTwoResponded d round next_data l false pt else pt_PhaseTwoAbort d round next_data l pt].
Definition PhaseTwoCommit d round next_data lg := [\/ exists sent : seq nid, cn_PhaseTwoSendCommits d round next_data lg sent | exists recvd : seq nid, cn_PhaseTwoReceiveCommits d round next_data lg recvd ].
Definition PhaseTwoAbort d round next_data lg := [\/ exists sent : seq nid, cn_PhaseTwoSendAborts d round next_data lg sent | exists recvd : seq nid, cn_PhaseTwoReceiveAborts d round next_data lg recvd ].
Definition PhaseTwo (d : dstatelet) (round : nat) (next_data : data) (l : Log) := [\/ exists sent, cn_PhaseTwoSendCommits d round next_data l sent, exists sent, cn_PhaseTwoSendAborts d round next_data l sent, exists recvd, cn_PhaseTwoReceiveCommits d round next_data l recvd | exists recvd, cn_PhaseTwoReceiveAborts d round next_data l recvd].
Definition Inv (d : dstatelet) := exists round l, [\/ EverythingInit d round l , exists next_data, PhaseOne d round next_data l | exists next_data, PhaseTwo d round next_data l].
Notation coh d := (coh tpc d).
Notation PI := pf_irr.
Export TPCProtocol.
Definition coord_msg tag (from to : nid) : bool := [&& from == cn, to \in pts & tagFromCoordinator tag].
Definition participant_msg tag (from to : nid) : bool := [&& from \in pts, to == cn & tagFromParticipant tag].
Definition internal_msg (tag : nat) (from to : nid) : bool := coord_msg tag from to || participant_msg tag from to.
Definition E_consume_external d i this tag m from P := let: d' := {| dstate := upd this (loc this d) (dstate d); dsoup := consume_msg (dsoup d) i |} in coh d -> find i (dsoup d) = Some {| content := {| tag := tag; tms_cont := m |}; from := from; to := this; active := true |} -> ~~ internal_msg tag from this -> P d -> P d'.
End TwoPhaseInductiveInv.

Lemma inv_waitprep d r (C : coh d) next_data recvd: Inv d -> getStC C = (r, CWaitPrepResponse next_data recvd) -> exists lg, cn_PhaseOneReceive d r next_data lg recvd.
Proof.
case=>r'[lg][]=>[|[nd]|[nd]].
by case=> CS; rewrite (getStC_K C CS).
case; case => x[]CS; rewrite (getStC_K C CS)//.
by move=>H1 H2 H3 H4; case=><-<-<-; eexists; split; eauto.
Admitted.

Lemma inv_sentcommit d r (C : coh d) next_data sent: Inv d -> getStC C = (r, CSentCommit next_data sent) -> exists lg, cn_PhaseTwoSendCommits d r next_data lg sent.
Proof.
case=>r'[lg][]=>[|[nd]|[nd]].
by case=> CS; rewrite (getStC_K C CS).
by case; case => x[]CS; rewrite (getStC_K C CS).
case; case => x[]CS; rewrite (getStC_K C CS)//.
move=>H1 H2 H3.
case.
intros.
subst.
Admitted.

Lemma inv_sentabort d r (C : coh d) next_data sent: Inv d -> getStC C = (r, CSentAbort next_data sent) -> exists lg, cn_PhaseTwoSendAborts d r next_data lg sent.
Proof.
case=>r'[lg][]=>[|[nd]|[nd]].
by case=> CS; rewrite (getStC_K C CS).
by case; case => x[]CS; rewrite (getStC_K C CS).
case; case => x[]CS; rewrite (getStC_K C CS)//.
move=>H1 H2 H3.
case.
intros.
subst.
Admitted.

Lemma inv_waitcommit d r (C : coh d) next_data sent: Inv d -> getStC C = (r, CWaitAckCommit next_data sent) -> exists lg, cn_PhaseTwoReceiveCommits d r next_data lg sent.
Proof.
case=>r'[lg][]=>[|[nd]|[nd]].
by case=> CS; rewrite (getStC_K C CS).
by case; case => x[]CS; rewrite (getStC_K C CS).
case; case => x[]CS; rewrite (getStC_K C CS)//.
move=>H1 H2 H3.
case.
intros.
subst.
Admitted.

Lemma inv_waitabort d r (C : coh d) next_data sent: Inv d -> getStC C = (r, CWaitAckAbort next_data sent) -> exists lg, cn_PhaseTwoReceiveAborts d r next_data lg sent.
Proof.
case=>r'[lg][]=>[|[nd]|[nd]].
by case=> CS; rewrite (getStC_K C CS).
by case; case => x[]CS; rewrite (getStC_K C CS).
case; case => x[]CS; rewrite (getStC_K C CS)//.
move=>H1 H2 H3.
case.
intros.
subst.
Admitted.

Lemma prep_no_pt_inv d i m pt round next_data lg : tag m = prep_no -> find i (dsoup d) = Some {| content := m; from := pt; to := cn; active := true |} -> pt_PhaseOne d round next_data lg pt -> [/\ pt_state d (round, PRespondedNo next_data) lg pt, no_msg_from_to cn pt (dsoup d) & msg_spec pt cn prep_no [::round] (dsoup d)].
Proof.
Admitted.

Lemma prep_yes_pt_inv d i m pt round next_data lg : tag m = prep_yes -> find i (dsoup d) = Some {| content := m; from := pt; to := cn; active := true |} -> pt_PhaseOne d round next_data lg pt -> [/\ pt_state d (round, PRespondedYes next_data) lg pt, no_msg_from_to cn pt (dsoup d) & msg_spec pt cn prep_yes [::round] (dsoup d)].
Proof.
Admitted.

Lemma commit_ack_pt_inv d i m pt round next_data lg : tag m = commit_ack -> find i (dsoup d) = Some {| content := m; from := pt; to := cn; active := true |} -> pt_PhaseTwoCommit d round next_data lg pt -> [/\ pt_state d (round.+1, PInit) (rcons lg (true, next_data)) pt, no_msg_from_to cn pt (dsoup d) & msg_spec pt cn Exports.commit_ack [:: round] (dsoup d)].
Proof.
Admitted.

Lemma abort_ack_pt_inv d i m pt round next_data lg : tag m = abort_ack -> find i (dsoup d) = Some {| content := m; from := pt; to := cn; active := true |} -> pt_PhaseTwoAbort d round next_data lg pt -> [/\ pt_state d (round.+1, PInit) (rcons lg (false, next_data)) pt, no_msg_from_to cn pt (dsoup d) & msg_spec pt cn Exports.abort_ack [:: round] (dsoup d)].
Proof.
Admitted.

Lemma prep_req_cn_inv d i m pt : tag m = prep_req -> pt \in pts -> find i (dsoup d) = Some {| content := m; from := cn; to := pt; active := true |} -> Inv d -> exists round lg next_data, PhaseOne d round next_data lg.
Proof.
case: m=>t m /=T.
subst t.
move=>Hpt F [r][lg][].
-
by move=>[] _ /(_ _ Hpt)[] _ _ /(_ _ _ _ F).
-
move=>[nd].
by eauto.
-
Admitted.

Lemma commit_req_pt_inv d i m pt round next_data lg : find i (dsoup d) = Some {| content := m; from := cn; to := pt; active := true |} -> pt_PhaseTwoCommit d round next_data lg pt -> [/\ pt_state d (round, PRespondedYes next_data) lg pt, msg_spec cn pt Exports.commit_req [:: round] (dsoup d) & no_msg_from_to pt cn (dsoup d)].
Proof.
Admitted.

Lemma abort_req_pt_inv d i m pt round next_data lg : find i (dsoup d) = Some {| content := m; from := cn; to := pt; active := true |} -> pt_PhaseTwoAbort d round next_data lg pt -> [/\ pt_state d (round, PRespondedYes next_data) lg pt \/ pt_state d (round, PRespondedNo next_data) lg pt, msg_spec cn pt Exports.abort_req [:: round] (dsoup d) & no_msg_from_to pt cn (dsoup d)].
Proof.
Admitted.

Lemma in_map_exists (x : nid) xs : (exists b : bool, (x, b) \in xs) \/ x \notin map fst xs.
Proof.
case H: (x \in map fst xs); last by right.
left.
case/mapP: H =>[][y b] H/=->.
Admitted.

Lemma commit_req_cn_inv d i m pt : tag m = commit_req -> pt \in pts -> find i (dsoup d) = Some {| content := m; from := cn; to := pt; active := true |} -> Inv d -> exists round lg next_data, PhaseTwoCommit d round next_data lg.
Proof.
case: m=>t m /=T.
subst t.
move=>Hpt F [r][lg][].
-
by move=>[] _ /(_ _ Hpt)[] _ _ /(_ _ _ _ F).
-
move=>[nd] [][l1][] _ _ _.
+
move/(_ _ Hpt).
case: ifP=>_ [][]; do?[by move=>_ _ /(_ _ _ _ F)]; do?[by move=>_ /(_ _ _ _ F)]; do?[by move=>/(_ _ _ _ F)]; by move=>_ _ []_ /(_ _ _ _ F)/=.
+
case: (in_map_exists pt l1).
*
move=>[b] H /(_ _ _ Hpt H) [].
by move=>/(_ _ _ _ F).
*
move=>H _ /(_ _ Hpt H) [][]; do?[by move=>_ _ /(_ _ _ _ F)]; do?[by move=>_ /(_ _ _ _ F)]; do?[by move=>/(_ _ _ _ F)]; by move=>_ _ []_ /(_ _ _ _ F)/=.
-
unfold PhaseTwoCommit.
Admitted.

Lemma abort_req_cn_inv d i m pt : tag m = abort_req -> pt \in pts -> find i (dsoup d) = Some {| content := m; from := cn; to := pt; active := true |} -> Inv d -> exists round lg next_data, PhaseTwoAbort d round next_data lg.
Proof.
case: m=>t m /=T.
subst t.
move=>Hpt F [r][lg][].
-
by move=>[] _ /(_ _ Hpt)[] _ _ /(_ _ _ _ F).
-
move=>[nd] [][l1][] _ _ _.
+
move/(_ _ Hpt).
case: ifP=>_ [][]; do?[by move=>_ _ /(_ _ _ _ F)]; do?[by move=>_ /(_ _ _ _ F)]; do?[by move=>/(_ _ _ _ F)]; by move=>_ _ []_ /(_ _ _ _ F)/=.
+
case: (in_map_exists pt l1).
*
move=>[b] H /(_ _ _ Hpt H) [].
by move=>/(_ _ _ _ F).
*
move=>H _ /(_ _ Hpt H) [][]; do?[by move=>_ _ /(_ _ _ _ F)]; do?[by move=>_ /(_ _ _ _ F)]; do?[by move=>/(_ _ _ _ F)]; by move=>_ _ []_ /(_ _ _ _ F)/=.
-
unfold PhaseTwoAbort.
Admitted.

Lemma PhaseTwoCommit_req_round d i m pt round lg next_data : tag m = commit_req -> pt \in pts -> find i (dsoup d) = Some {| content := m; from := cn; to := pt; active := true |} -> PhaseTwoCommit d round next_data lg -> exists ps, pt_state d (round, ps) lg pt.
Proof.
Admitted.

Lemma PhaseTwoAbort_req_round d i m pt round lg next_data : tag m = abort_req -> pt \in pts -> find i (dsoup d) = Some {| content := m; from := cn; to := pt; active := true |} -> PhaseTwoAbort d round next_data lg -> exists ps, pt_state d (round, ps) lg pt.
Proof.
Admitted.

Lemma PhaseTwoAbort_round_cn d round lg next_data : PhaseTwoAbort d round next_data lg -> exists cs, cn_state d (round, cs) lg.
Proof.
Admitted.

Lemma PhaseTwoCommit_round_cn d round lg next_data : PhaseTwoCommit d round next_data lg -> exists cs, cn_state d (round, cs) lg.
Proof.
Admitted.

Lemma PhaseOne_round_cn d round lg next_data : PhaseOne d round next_data lg -> exists cs, cn_state d (round, cs) lg.
Proof.
Admitted.

Lemma prep_req_pt_inv d i m pt round next_data lg : find i (dsoup d) = Some {| content := m; from := cn; to := pt; active := true |} -> pt_PhaseOne d round next_data lg pt -> [/\ pt_state d (round, PInit) lg pt, no_msg_from_to pt cn (dsoup d) & msg_spec cn pt Exports.prep_req (round :: next_data) (dsoup d)].
Proof.
by move=>F[][]H1 H2 H3; do?[by move: (H2 _ _ _ F)]; do?[by move: (H3 _ _ _ F)]; split=>//.
