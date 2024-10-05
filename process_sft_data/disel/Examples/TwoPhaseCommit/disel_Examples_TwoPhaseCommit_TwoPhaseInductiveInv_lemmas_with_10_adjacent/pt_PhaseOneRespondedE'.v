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

Lemma pt_PhaseOneE_consume d e dt lg pt ds i from to m: let d' := {| dstate := upd to ds (dstate d); dsoup := consume_msg (dsoup d) i |} in coh d -> pt \in pts -> pt != from -> pt != to -> find i (dsoup d) = Some {| content := m; from := from; to := to; active := true |} -> pt_PhaseOne d e dt lg pt -> pt_PhaseOne d' e dt lg pt.
Proof.
move => d' C Hpt.
subst d'.
have Npt: pt != cn by apply pt_not_cn.
have Vst: valid (dsoup d) by apply /(cohVs C).
move => N1 N2 F [][] PS NM1.
-
move => M.
constructor 1.
split.
+
by apply /pt_state_consume.
+
by apply /no_msg_from_to_consume.
+
by apply /(@msg_specE_consume2 (dsoup d) _ from pt to _ _ i m) => //.
-
move => NM2.
constructor 2.
split.
+
by apply /pt_state_consume.
+
by apply /no_msg_from_to_consume.
+
by apply /no_msg_from_to_consume.
-
move => M.
constructor 3.
split.
+
by apply /pt_state_consume.
+
by apply /no_msg_from_to_consume=>//.
+
by apply /(@msg_specE_consume1 (dsoup d) _ from _ to _ _ i m).
-
move => M.
constructor 4.
split.
+
by apply /pt_state_consume.
+
by apply /no_msg_from_to_consume.
+
Admitted.

Lemma pt_PhaseOneRespondedE_consume d e dt lg b pt ds i from: let: d' := {| dstate := upd from ds (dstate d); dsoup := consume_msg (dsoup d) i |} in coh d -> pt \in pts -> pt != from -> pt_PhaseOneResponded d e dt lg b pt -> pt_PhaseOneResponded d' e dt lg b pt.
Proof.
move=>C Hpt N [] NM1 NM2 PS.
have Vs: (valid (dsoup d)) by exact: (cohVs C).
split.
-
exact: no_msg_from_to_consume.
-
exact: no_msg_from_to_consume.
-
Admitted.

Lemma cn_PhaseOneReceive_consume d round next_data lg recvd i m from : cn_PhaseOneReceive d round next_data lg recvd -> find i (dsoup d) = Some {| content := m; from := from; to := cn; active := true |} -> from \in pts -> from \in map fst recvd -> coh d -> let: d' := {| dstate := upd cn (mkLocal (round, CWaitPrepResponse next_data recvd, lg)) (dstate d); dsoup := consume_msg (dsoup d) i |} in cn_PhaseOneReceive d' round next_data lg recvd.
Proof.
move=>[] CS U Hsub Hrecvd1 Hrecvd2 F Hfrom Hold C.
split=>//.
-
by rewrite /cn_state locE'// (cohVl C).
-
move=>pt b Hpt Hr.
apply /(pt_PhaseOneRespondedE_consume _ i)=>//.
by apply: pt_not_cn.
exact : Hrecvd1.
-
move=>pt Hpt Hr.
case H: (pt == from).
+
move/eqP in H.
subst from.
move: (Hrecvd2 _ Hpt Hr).
move /negbTE in Hr.
by rewrite Hr in Hold.
+
apply /(@pt_PhaseOneE_consume _ _ _ _ _ _ _ from cn m) =>//.
by apply /negbT/H.
by apply /pt_not_cn.
Admitted.

Lemma pt_PhaseTwoRespondedE_consume d e dt lg b pt ds i this: let: d' := {| dstate := upd this ds (dstate d); dsoup := consume_msg (dsoup d) i |} in coh d -> pt \in pts -> pt != this -> pt_PhaseTwoResponded d e dt lg b pt -> pt_PhaseTwoResponded d' e dt lg b pt.
Proof.
move=>C Hpt N [] NM1 NM2 PS.
have Vs: (valid (dsoup d)) by exact: (cohVs C).
have N2: (pt != cn) by exact: pt_not_cn.
split.
-
exact: pt_state_consume.
-
exact: no_msg_from_to_consume.
-
Admitted.

Lemma pt_PhaseTwoCommitE_consume d e dt lg pt ds from to i m: let: d' := {| dstate := upd to ds (dstate d); dsoup := consume_msg (dsoup d) i |} in coh d -> pt != from -> pt != to -> find i (dsoup d) = Some {| content := m; from := from; to := to; active := true |} -> pt_PhaseTwoCommit d e dt lg pt -> pt_PhaseTwoCommit d' e dt lg pt.
Proof.
move=>C N1 N2 F I.
have Vs: (valid (dsoup d)) by exact: (cohVs C).
move: I => [][] PS H1 H2; [constructor 1|constructor 2|constructor 3]; split; do?[by apply: no_msg_from_to_consume]; do?[by apply: pt_state_consume].
-
by apply /(msg_specE_consume2 _ F)=>//.
-
Admitted.

Lemma pt_PhaseTwoAbortE_consume d e dt lg pt ds from to i m: let: d' := {| dstate := upd to ds (dstate d); dsoup := consume_msg (dsoup d) i |} in coh d -> pt != from -> pt != to -> find i (dsoup d) = Some {| content := m; from := from; to := to; active := true |} -> pt_PhaseTwoAbort d e dt lg pt -> pt_PhaseTwoAbort d' e dt lg pt.
Proof.
move=>C N1 N2 F I.
have Vs: (valid (dsoup d)) by exact: (cohVs C).
move: I => [][] PS H1 H2; [constructor 1|constructor 2|constructor 3]; split; do?[by apply: no_msg_from_to_consume]; do?[by apply: pt_state_consume].
-
case: PS=>PS; [left|right]; by apply: pt_state_consume.
-
by apply /(msg_specE_consume2 _ F)=>//.
-
Admitted.

Lemma cn_state_soupE d ds this h cs lg : let: d' := {| dstate := upd this h (dstate d); dsoup := ds |} in coh d -> this != cn -> cn_state d cs lg -> cn_state d' cs lg.
Proof.
move=>C N.
have Vl := (cohVl C).
rewrite /cn_state locU//.
Admitted.

Lemma pt_state_soupE d ds h ps lg pt n : let: d' := {| dstate := upd n h (dstate d); dsoup := ds |} in coh d -> pt != n -> pt_state d ps lg pt -> pt_state d' ps lg pt .
Proof.
move => C N H.
Admitted.

Lemma pt_PhaseOneE' d r nd lg pt from h to m : let: d' := {| dstate := upd from h (dstate d); dsoup := (post_msg (dsoup d) {| content := m; from := from; to := to; active := true |}).1 |} in coh d -> from != pt -> from != cn -> pt_PhaseOne d r nd lg pt -> pt_PhaseOne d' r nd lg pt.
Proof.
move=>C N1 N2.
have Vl := cohVl C.
have Vs := cohVs C.
move=>[][] H1 H2 H3; [constructor 1|constructor 2|constructor 3|constructor 4].
-
split.
+
apply /pt_state_soupE=>//.
by apply /eqP/nesym/eqP.
+
apply no_msg_from_toE'=>//.
by apply /negbTE.
+
apply msg_specE''=>//.
by apply /eqP/nesym/eqP.
-
split.
+
apply /pt_state_soupE=>//.
by apply /eqP/nesym/eqP.
+
apply no_msg_from_toE'=>//.
by apply /negbTE.
+
apply no_msg_from_toE'=>//.
by apply /negbTE.
-
split.
+
apply /pt_state_soupE=>//.
by apply /eqP/nesym/eqP.
+
apply no_msg_from_toE'=>//.
by apply /negbTE.
+
apply msg_specE''=>//.
by apply /eqP/nesym/eqP.
-
split.
+
apply /pt_state_soupE=>//.
by apply /eqP/nesym/eqP.
+
apply no_msg_from_toE'=>//.
by apply /negbTE.
+
apply msg_specE''=>//.
Admitted.

Lemma pt_InitE d r lg pt from h to m : let: d' := {| dstate := upd from h (dstate d); dsoup := (post_msg (dsoup d) {| content := m; from := from; to := to; active := true |}).1 |} in coh d -> from != pt -> from != cn -> pt_Init d r lg pt -> pt_Init d' r lg pt.
Proof.
move=>C N1 N2.
have Vl := cohVl C.
have Vs := cohVs C.
move=>[] H1 H2 H3.
split.
-
apply pt_state_soupE=>//.
by apply /eqP/nesym/eqP.
-
apply /no_msg_from_toE'=>//.
by apply /negbTE.
-
apply /no_msg_from_toE'=>//.
Admitted.

Lemma PhaseTwo_PCommitted_pt d pt round lg next_data r nd (C : coh d) (Hpt : pt \in nodes _ _ _) : pt \in pts -> getStP Hnin C Hpt = (r, PCommitted nd) -> PhaseTwo d round next_data lg -> [/\ pt_state d (round, PCommitted next_data) (rcons lg (true, next_data)) pt, no_msg_from_to cn pt (dsoup d) & no_msg_from_to pt cn (dsoup d)].
Proof.
move=>HptP PS[][l1][] CS U S /(_ pt HptP); case: ifP=> _[]; (try case); (try case); intros => //.
Admitted.

Lemma pt_PhaseTwoCommitE' d r nd lg pt from h to m : let: d' := {| dstate := upd from h (dstate d); dsoup := (post_msg (dsoup d) {| content := m; from := from; to := to; active := true |}).1 |} in coh d -> from != pt -> from != cn -> pt_PhaseTwoCommit d r nd lg pt -> pt_PhaseTwoCommit d' r nd lg pt.
Proof.
move=>C /eqP/nesym/eqP N1 /eqP/nesym/eqP N2.
have Vs := cohVs C.
Admitted.

Lemma pt_PhaseTwoAbortE' d r nd lg pt from h to m : let: d' := {| dstate := upd from h (dstate d); dsoup := (post_msg (dsoup d) {| content := m; from := from; to := to; active := true |}).1 |} in coh d -> from != pt -> from != cn -> pt_PhaseTwoAbort d r nd lg pt -> pt_PhaseTwoAbort d' r nd lg pt.
Proof.
move=>C /eqP/nesym/eqP N1 /eqP/nesym/eqP N2.
have Vs := cohVs C.
case=>[][] H1 H2 H3; [constructor 1|constructor 2|constructor 3]; split; do?[by apply /pt_state_soupE]; do?[by apply /msg_specE''=>//; apply /negbTE]; do?[by apply/no_msg_from_toE'=>//; apply/eqP/nesym/eqP].
Admitted.

Lemma pt_PhaseTwoRespondedE' d r nd lg pt from h to m b : let: d' := {| dstate := upd from h (dstate d); dsoup := (post_msg (dsoup d) {| content := m; from := from; to := to; active := true |}).1 |} in coh d -> from != pt -> from != cn -> pt_PhaseTwoResponded d r nd lg b pt -> pt_PhaseTwoResponded d' r nd lg b pt.
Proof.
move=>C N1 N2 [] PS NM1 NM2.
have Vs := cohVs C.
split.
-
apply /pt_state_soupE=>//.
by apply /eqP/nesym/eqP.
-
apply /no_msg_from_toE'=>//.
by apply /negbTE.
-
apply /no_msg_from_toE'=>//.
Admitted.

Lemma PhaseTwo_PAborted_pt d pt round lg next_data r nd (C : coh d) (Hpt : pt \in nodes _ _ _) : pt \in pts -> getStP Hnin C Hpt = (r, PAborted nd) -> PhaseTwo d round next_data lg -> [/\ pt_state d (round, PAborted next_data) (rcons lg (false, next_data)) pt, no_msg_from_to cn pt (dsoup d) & no_msg_from_to pt cn (dsoup d)].
Proof.
move=>HptP PS[][l1][] CS U S /(_ pt HptP); case: ifP=> _[]; (try case); (try case); intros => //.
Admitted.

Lemma internal_msg_tagFromParticipant_to_cn tag from to : internal_msg tag from to -> tagFromParticipant tag -> to == cn.
Proof.
case/orP; move=>/and3P[]//.
move=> _ _.
rewrite /tagFromCoordinator/tagFromParticipant !inE.
Admitted.

Lemma internal_msg_tagFromParticipant_from_pts tag from to : internal_msg tag from to -> tagFromParticipant tag -> from \in pts.
Proof.
case/orP; move=>/and3P[]//.
move=> _ _.
rewrite /tagFromCoordinator/tagFromParticipant !inE.
Admitted.

Lemma internal_msg_tagFromCoordinator_to_pts tag from to : internal_msg tag from to -> tagFromCoordinator tag -> to \in pts.
Proof.
case/orP; move=>/and3P[]//.
move=> _ _.
rewrite /tagFromCoordinator/tagFromCoordinator !inE.
Admitted.

Lemma internal_msg_tagFromCoordinator_from_cn tag from to : internal_msg tag from to -> tagFromCoordinator tag -> from == cn.
Proof.
case/orP; move=>/and3P[]//.
move=> _ _.
rewrite /tagFromCoordinator/tagFromCoordinator !inE.
Admitted.

Lemma internal_msg_to_cn tag from : internal_msg tag from cn -> participant_msg tag from cn.
Proof.
move=>/orP[]// /and3P[] _ H.
move: Hnin.
Admitted.

Lemma pt_PhaseOneRespondedE' d r nd lg pt from h to m b : let: d' := {| dstate := upd from h (dstate d); dsoup := (post_msg (dsoup d) {| content := m; from := from; to := to; active := true |}).1 |} in coh d -> from != pt -> from != cn -> pt_PhaseOneResponded d r nd lg b pt -> pt_PhaseOneResponded d' r nd lg b pt.
Proof.
move=>C N1 N2 [] NM1 NM2 H.
have Vl := cohVl C.
have Vs := cohVs C.
split.
-
apply /no_msg_from_toE'=>//.
by apply /negbTE.
-
apply /no_msg_from_toE'=>//.
by apply /negbTE.
-
case: b H.
+
apply: pt_state_soupE=>//.
by apply /eqP/nesym/eqP.
+
apply: pt_state_soupE=>//.
by apply /eqP/nesym/eqP.
