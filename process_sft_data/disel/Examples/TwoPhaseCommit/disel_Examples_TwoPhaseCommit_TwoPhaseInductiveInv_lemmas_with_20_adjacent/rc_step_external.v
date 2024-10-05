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

Lemma inv_msg_round d (C : coh d) i tag m from to round cs : find i (dsoup d) = Some {| content := {| tag := tag; tms_cont := m |}; from := from; to := to; active := true |} -> internal_msg tag from to -> Inv d -> getStC C = (round, cs) -> head 0 m == round.
Proof.
move=>F Hinternal I St.
case/orP: Hinternal.
-
move=>/and3P[]/eqP ? Hto T.
subst from.
move: I=>[rd][lg][].
+
by move=>[]CS /(_ _ Hto) [] PS NM1 /(_ _ _ _ F).
+
move=>[next_data][].
*
move=>[sent][] CS U Sub /(_ _ Hto).
case: ifP.
--
move=>Hsent [][] PS.
++
move=>_[] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
rewrite (getStC_K _ CS) in St.
case: St=>->.
by rewrite eqxx.
++
by move=>_ /(_ _ _ _ F).
++
by move=>/(_ _ _ _ F).
++
by move=>/(_ _ _ _ F).
--
by move=>Hsent[] PS _ /(_ _ _ _ F).
*
move=>[recvd][] CS U Sub Hrecvd1 Hrecvd2.
case: (in_map_exists to recvd).
--
move=>[b] Hr.
by move: (Hrecvd1 _ _ Hto Hr)=>[] /(_ _ _ _ F).
--
move=>Hr.
move: (Hrecvd2 _ Hto Hr)=>[][] PS.
++
move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
rewrite (getStC_K _ CS) in St.
case: St=>->.
by rewrite eqxx.
++
by move=>_ /(_ _ _ _ F).
++
by move=>/(_ _ _ _ F).
++
by move=>/(_ _ _ _ F).
+
move=>[next_data][].
*
move=>[sent][] CS U Sub /(_ _ Hto).
case: ifP.
--
move=>Hsent [][] PS.
++
move=>[] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
rewrite (getStC_K _ CS) in St.
case: St=>->.
by rewrite eqxx.
++
by move=>/(_ _ _ _ F).
++
by move=>/(_ _ _ _ F).
--
by move=>_ [] /(_ _ _ _ F).
*
move=>[sent][] CS U Sub /(_ _ Hto).
case: ifP.
--
move=>Hsent [][] PS.
++
move=>[] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
rewrite (getStC_K _ CS) in St.
case: St=>->.
by rewrite eqxx.
++
by move=>/(_ _ _ _ F).
++
by move=>/(_ _ _ _ F).
--
by move=> _[b][] /(_ _ _ _ F).
*
move=>[recvd][] CS U Sub /(_ _ Hto).
case: ifP.
--
by move=>Hrecvd [] PS /(_ _ _ _ F).
--
move=>Hrecvd[][] PS.
++
move=>[] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
rewrite (getStC_K _ CS) in St.
case: St=>->.
by rewrite eqxx.
++
by move=>/(_ _ _ _ F).
++
by move=>/(_ _ _ _ F).
*
move=>[recvd][] CS U Sub /(_ _ Hto).
case: ifP.
--
by move=>Hrecvd [] PS /(_ _ _ _ F).
--
move=>Hrecvd[][] PS.
++
move=>[] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
rewrite (getStC_K _ CS) in St.
case: St=>->.
by rewrite eqxx.
++
by move=>/(_ _ _ _ F).
++
by move=>/(_ _ _ _ F).
-
move=>/and3P[]Hfrom/eqP ? T.
subst to.
move: I=>[rd][lg][].
+
by move=>[]CS /(_ _ Hfrom) [] PS /(_ _ _ _ F).
+
move=>[next_data][].
*
move=>[sent][] CS U Sub /(_ _ Hfrom).
case: ifP.
--
move=>Hsent [][] PS.
++
by move=>/(_ _ _ _ F).
++
by move=>/(_ _ _ _ F).
++
move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
rewrite (getStC_K _ CS) in St.
case: St=>->.
by rewrite eqxx.
++
move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
rewrite (getStC_K _ CS) in St.
case: St=>->.
by rewrite eqxx.
--
by move=>Hsent[] PS /(_ _ _ _ F).
*
move=>[recvd][] CS U Sub Hrecvd1 Hrecvd2.
case: (in_map_exists from recvd).
--
move=>[b] Hr.
by move: (Hrecvd1 _ _ Hfrom Hr)=>[] _/(_ _ _ _ F).
--
move=>Hr.
move: (Hrecvd2 _ Hfrom Hr)=>[][] PS.
++
by move=>/(_ _ _ _ F).
++
by move=>/(_ _ _ _ F).
++
move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
rewrite (getStC_K _ CS) in St.
case: St=>->.
by rewrite eqxx.
++
move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
rewrite (getStC_K _ CS) in St.
case: St=>->.
by rewrite eqxx.
+
move=>[next_data][].
*
move=>[sent][] CS U Sub /(_ _ Hfrom).
case: ifP.
--
move=>Hsent [][] PS.
++
by move=>_ /(_ _ _ _ F).
++
by move=>_ /(_ _ _ _ F).
++
move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
rewrite (getStC_K _ CS) in St.
case: St=>->.
by rewrite eqxx.
--
by move=>Hsent [] _ /(_ _ _ _ F).
*
move=>[sent][] CS U Sub /(_ _ Hfrom).
case: ifP.
--
move=>Hsent [][] PS.
++
by move=>_ /(_ _ _ _ F).
++
by move=>_ /(_ _ _ _ F).
++
move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
rewrite (getStC_K _ CS) in St.
case: St=>->.
by rewrite eqxx.
--
by move=>Hsent [b][] _ /(_ _ _ _ F).
*
move=>[recvd][] CS U Sub /(_ _ Hfrom).
case: ifP.
--
by move=>Hrecvd [] PS _ /(_ _ _ _ F).
--
move=>Hrecvd[][] PS.
++
by move=>_ /(_ _ _ _ F).
++
by move=>_ /(_ _ _ _ F).
++
move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
rewrite (getStC_K _ CS) in St.
case: St=>->.
by rewrite eqxx.
*
move=>[recvd][] CS U Sub /(_ _ Hfrom).
case: ifP.
--
by move=>Hrecvd [] PS _ /(_ _ _ _ F).
--
move=>Hrecvd[][] PS.
++
by move=>_ /(_ _ _ _ F).
++
by move=>_ /(_ _ _ _ F).
++
move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
rewrite (getStC_K _ CS) in St.
case: St=>->.
Admitted.

Lemma cn_stateE_consume_external d i this tag m from cs log : E_consume_external d i this tag m from (fun d => cn_state d cs log).
Proof.
move=>C F Hext.
have Vl := (cohVl C).
rewrite /cn_state.
case H: (this == cn).
-
move/eqP in H.
subst this.
by rewrite locE'.
rewrite locU//.
Admitted.

Lemma pt_stateE_consume_external d i this tag m from ps lg pt : E_consume_external d i this tag m from (fun d => pt_state d ps lg pt).
Proof.
move=>C F Hext.
have Vl := (cohVl C).
rewrite /pt_state.
case H: (this == pt).
-
move/eqP in H.
subst this.
by rewrite locE'.
rewrite locU//.
Admitted.

Lemma msg_specE_consume_external d i this tag m from from' to' tag' m' : internal_msg tag' from' to' -> E_consume_external d i this tag m from (fun d => msg_spec from' to' tag' m' (dsoup d)).
Proof.
move=>Hint C F Hext [] [j] [][t][c] F' U H.
have Vs := cohVs C.
split.
-
exists j.
split.
+
exists t, c.
rewrite mark_other//.
case E: (j == i)=>//.
move/eqP in E.
subst j.
move: F.
rewrite F'.
case=> ? ? ? ?.
subst.
move: (F')=>/H/andP[]/eqP ? _.
subst.
by rewrite Hint in Hext.
+
move=>k[t'][c'] F''.
case H2: (k == i).
*
move/eqP in H2.
subst k.
move: F''=> /(find_mark Vs)[msg'][F''].
discriminate.
*
rewrite mark_other// in F''.
apply /U.
by eauto.
-
move=> k t' c' F''.
case H2: (k == i).
+
move/eqP in H2.
subst k.
move: F''=> /(find_mark Vs)[msg'][F''].
discriminate.
+
rewrite mark_other// in F''.
apply /H.
Admitted.

Lemma pt_PhaseOneE_consume_external d i this tag m from round next_data lg pt : pt \in pts -> E_consume_external d i this tag m from (fun d => pt_PhaseOne d round next_data lg pt).
Proof.
move=>Hpt C F Hext.
have Vs := (cohVs C).
case=>[][]PS NM1 H; [constructor 1|constructor 2| constructor 3 | constructor 4].
-
split=>//.
+
by apply: (pt_stateE_consume_external _ F).
+
by apply: no_msg_from_to_consume.
+
apply: (msg_specE_consume_external _ _ F)=>//.
apply/orP.
left.
by apply/and3P.
-
split=>//.
+
by apply: (pt_stateE_consume_external _ F).
+
by apply: no_msg_from_to_consume.
+
by apply: no_msg_from_to_consume.
-
split=>//.
+
by apply: (pt_stateE_consume_external _ F).
+
by apply: no_msg_from_to_consume.
+
apply: (msg_specE_consume_external _ _ F)=>//.
apply/orP.
right.
by apply/and3P.
-
split=>//.
+
by apply: (pt_stateE_consume_external _ F).
+
by apply: no_msg_from_to_consume.
+
apply: (msg_specE_consume_external _ _ F)=>//.
apply/orP.
right.
Admitted.

Lemma pt_InitE_consume_external d i this tag m from round lg pt : E_consume_external d i this tag m from (fun d => pt_Init d round lg pt).
Proof.
move=>C F Hext [] PS NM1 NM2.
have Vs := (cohVs C).
split.
-
by apply: (pt_stateE_consume_external _ F).
-
by apply: no_msg_from_to_consume.
-
Admitted.

Lemma pt_PhaseOneRespondedE_consume_external d i this tag m from round next_data lg b pt : E_consume_external d i this tag m from (fun d => pt_PhaseOneResponded d round next_data lg b pt).
Proof.
move=>C F Hext [] NM1 NM2 H.
have Vs := (cohVs C).
split.
-
by apply: no_msg_from_to_consume.
-
by apply: no_msg_from_to_consume.
-
Admitted.

Lemma pt_PhaseTwoRespondedE_consume_external d i this tag m from round next_data lg b pt : E_consume_external d i this tag m from (fun d => pt_PhaseTwoResponded d round next_data lg b pt).
Proof.
move=>C F Hext [] PS NM1 NM2.
have Vs := (cohVs C).
split.
-
by apply: (pt_stateE_consume_external _ F).
-
by apply: no_msg_from_to_consume.
-
Admitted.

Lemma pt_PhaseTwoCommitE_consume_external d i this tag m from round next_data lg pt : pt \in pts -> E_consume_external d i this tag m from (fun d => pt_PhaseTwoCommit d round next_data lg pt).
Proof.
move=>Hpt C F Hext [][] PS H1 H2; have Vs := (cohVs C); [constructor 1|constructor 2|constructor 3]; split; do?[by apply: (pt_stateE_consume_external _ F)]; do?[by apply: no_msg_from_to_consume].
-
apply: (msg_specE_consume_external _ _ F)=>//.
apply/orP.
left.
by apply/and3P.
-
apply: (msg_specE_consume_external _ _ F)=>//.
apply/orP.
right.
Admitted.

Lemma pt_PhaseTwoAbortE_consume_external d i this tag m from round next_data lg pt : pt \in pts -> E_consume_external d i this tag m from (fun d => pt_PhaseTwoAbort d round next_data lg pt).
Proof.
move=>Hpt C F Hext [][] PS H1 H2; have Vs := (cohVs C); [constructor 1|constructor 2|constructor 3]; split; do?[by apply: (pt_stateE_consume_external _ F)]; do?[by apply: no_msg_from_to_consume].
-
case: PS=>PS; [left|right]; by apply: (pt_stateE_consume_external _ F).
-
apply: (msg_specE_consume_external _ _ F)=>//.
apply/orP.
left.
by apply/and3P.
-
apply: (msg_specE_consume_external _ _ F)=>//.
apply/orP.
right.
Admitted.

Lemma invE_consume_external d i this tag m from : E_consume_external d i this tag m from Inv.
Proof.
move=>C F Hext [round][lg] I.
have Vs := cohVs C.
have Vl := cohVl C.
exists round, lg.
case: I=>I; [constructor 1|constructor 2|constructor 3].
-
move: I=>[] CS Pts.
split.
+
by apply: (cn_stateE_consume_external _ F).
+
move=>pt Hpt.
move: (Pts pt Hpt)=>[] PS NM2.
split.
*
by apply: (pt_stateE_consume_external _ F).
*
by apply: (no_msg_from_to_consume).
*
by apply: (no_msg_from_to_consume).
-
move: I=>[next_data][[sent]|[recvd]] I; exists next_data; [constructor 1; exists sent|constructor 2; exists recvd].
+
move: I=>[] CS U Sub Pts.
split=>//.
*
by apply: (cn_stateE_consume_external _ F).
*
move=>pt Hpt.
case: ifP.
--
move=>Hsent.
move: (Pts _ Hpt).
rewrite Hsent.
by apply: (pt_PhaseOneE_consume_external _ _ F).
--
move=>Hsent.
move: (Pts _ Hpt).
rewrite Hsent.
by apply: (pt_InitE_consume_external _ F).
+
move: I=>[] CS U Sub Hrecvd1 Hrecvd2.
split=>//.
*
by apply: (cn_stateE_consume_external _ F).
*
move=>pt b Hpt Hr.
move: (Hrecvd1 _ _ Hpt Hr).
by apply: (pt_PhaseOneRespondedE_consume_external _ F).
*
move=>pt Hpt Hr.
move: (Hrecvd2 _ Hpt Hr).
by apply: (pt_PhaseOneE_consume_external _ _ F).
-
move: I=>[next_data][[sent]|[sent]|[recvd]|[recvd]] I; exists next_data; [constructor 1; exists sent|constructor 2; exists sent| constructor 3; exists recvd|constructor 4; exists recvd].
+
move: I=>[] CS U Sub Pts.
split=>//.
*
by apply: (cn_stateE_consume_external _ F).
*
move=>pt Hpt.
case: ifP.
--
move=>Hsent.
move: (Pts _ Hpt).
rewrite Hsent.
by apply: (pt_PhaseTwoCommitE_consume_external _ _ F).
--
move=>Hsent.
move: (Pts _ Hpt).
rewrite Hsent.
by apply: (pt_PhaseOneRespondedE_consume_external _ F).
+
move: I=>[] CS U Sub Pts.
split=>//.
*
by apply: (cn_stateE_consume_external _ F).
*
move=>pt Hpt.
case: ifP.
--
move=>Hsent.
move: (Pts _ Hpt).
rewrite Hsent.
by apply: (pt_PhaseTwoAbortE_consume_external _ _ F).
--
move=>Hsent.
move: (Pts _ Hpt).
rewrite Hsent=>[][b] I.
exists b.
by apply: (pt_PhaseOneRespondedE_consume_external _ F).
+
move: I=>[] CS U Sub Pts.
split=>//.
*
by apply: (cn_stateE_consume_external _ F).
*
move=>pt Hpt.
case: ifP.
--
move=>Hsent.
move: (Pts _ Hpt).
rewrite Hsent.
by apply: (pt_PhaseTwoRespondedE_consume_external _ F).
--
move=>Hsent.
move: (Pts _ Hpt).
rewrite Hsent.
by apply: (pt_PhaseTwoCommitE_consume_external _ _ F).
+
move: I=>[] CS U Sub Pts.
split=>//.
*
by apply: (cn_stateE_consume_external _ F).
*
move=>pt Hpt.
case: ifP.
--
move=>Hsent.
move: (Pts _ Hpt).
rewrite Hsent.
by apply: (pt_PhaseTwoRespondedE_consume_external _ F).
--
move=>Hsent.
move: (Pts _ Hpt).
rewrite Hsent.
Admitted.

Lemma rp_step_external d (C : coh d) this (Hthis : this \in nodes cn pts others) tag from m i : ~~ internal_msg tag from this -> find i (dsoup d) = Some {| content := {| tag := tag; tms_cont := m |}; from := from; to := this; active := true |} -> rp_step Hnin tag from m C Hthis = loc this d.
Proof.
move/norP=>[] H1 H2 F.
rewrite /rp_step.
case: ifP=>//Hpts.
pose proof C as C'.
case: C'=>Hs _ _ /(_ this (pts_in _ _ Hpts)) [] _.
rewrite (this_not_pts Hnin Hpts) Hpts =>[][ps][lg] L.
rewrite (getStP_K _ _ _ _ L)// (getStL_Kp _ _ L).
rewrite /pstep_recv.
case: ifP=>//.
move=>/norP[]/norP[] /negbNE H3 /negbNE H4 /negbNE H5.
destruct ps as[round ps].
move: H3 H1.
rewrite /coord_msg H4 Hpts/=/tagFromCoordinator/p_matches_tag.
destruct ps=>//.
-
move=>/eqP ?.
subst tag.
done.
-
case/orP=>/eqP ?; subst; done.
-
move=>/eqP ?.
subst tag.
Admitted.

Lemma internal_msg_from_cn tag to : internal_msg tag cn to -> coord_msg tag cn to.
Proof.
move=>/orP[]// /and3P[] H.
move: Hnin.
Admitted.

Lemma p_matches_tag_internal_inv d i t m pt r ps lg : coh d -> pt \in pts -> find i (dsoup d) = Some {| content := {| tag := t; tms_cont := m |}; from := cn; to := pt; active := true |} -> internal_msg t cn pt -> pt_state d (r, ps) lg pt -> Inv d -> p_matches_tag ps t.
Proof.
move=>C Hpt F /internal_msg_from_cn /and3P[] _ _ T PS.
move=>[r'][lg'][].
-
by move=>[] _ /(_ pt Hpt) [] _ _ /(_ _ _ _ F).
-
move=>[nd][][l1][] _ _ _.
+
move=>/(_ _ Hpt).
case: ifP=>_ [][] PS'; do?[by move=>_ /(_ _ _ _ F)]; do?[by move=>/(_ _ _ _ F)].
move=>_[] _ /(_ _ _ _ F) /andP[] /eqP ? /eqP ?.
subst.
move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _.
move: (pt_state_functional V PS PS')=>[][] ? ? ?.
subst.
done.
+
case: (in_map_exists pt l1).
*
by move=>[b] H /(_ _ _ Hpt H)[] /(_ _ _ _ F).
*
move=>H _ /(_ _ Hpt H)[][] PS'; do?[by move=>_ /(_ _ _ _ F)]; do?[by move=>/(_ _ _ _ F)].
move=>_[] _ /(_ _ _ _ F) /andP[] /eqP ? /eqP ?.
subst.
move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _.
move: (pt_state_functional V PS PS')=>[][] ? ? ?.
subst.
done.
-
Admitted.

Lemma PhaseOne_msg_next_data d (C : coh d) i m pt round next_data lg : find i (dsoup d) = Some {| content := {| tag := prep_req; tms_cont := m |}; from := cn; to := pt; active := true |} -> internal_msg prep_req cn pt -> PhaseOne d round next_data lg -> behead m == next_data.
Proof.
move=>F /internal_msg_from_cn /and3P[] _ Hpt _ [].
-
move=>[sent][] CS U S /(_ pt Hpt).
case: ifP=>_ [][] PS; do?[by move=>_ /(_ _ _ _ F)]; do?[by move=>/(_ _ _ _ F)].
by move=>_ [] _ /(_ _ _ _ F)/andP [] _ /eqP ->.
-
move=>[recvd][] CS U S.
case: (in_map_exists pt recvd).
+
by move=>[b] H /(_ _ _ Hpt H) [] /(_ _ _ _ F).
+
move=>H _ /(_ _ Hpt H) [][] _; do?[by move=>/(_ _ _ _ F)]; do?[by move=>_ /(_ _ _ _ F)].
Admitted.

Lemma cn_state_functional d cs1 lg1 cs2 lg2 : valid (loc cn d) -> cn_state d cs1 lg1 -> cn_state d cs2 lg2 -> cs1 = cs2 /\ lg1 = lg2.
Proof.
move=>V.
rewrite/cn_state=> H.
move: V.
rewrite H => V.
move /(hcancelV V) => [] ?.
subst.
move=> V1.
Admitted.

Lemma pt_log_agreement d r lg pt : coh d -> pt \in pts -> pt_state d (r, PInit) lg pt -> Inv d -> forall pt' ps' r' lg', pt' \in pts -> pt_state d (r', ps') lg' pt' -> r' = r -> lg' = lg.
Proof.
move=>C Hpt PS [r0][lg0].
move: (C)=>[] _ _ _ /(_ _ (pts_in _ _ Hpt)) [] V _.
case.
-
move=>[] CS.
move=>Pts pt' ps' r' lg' Hpt' PS'.
move: (Pts pt Hpt)=>[].
move /(pt_state_functional V PS)=>[][] ? ? _ _.
subst.
move: (Pts pt' Hpt')=>[].
move: (C)=>[] _ _ _ /(_ _ (pts_in _ _ Hpt')) [] V' _.
move /(pt_state_functional V' PS') =>[][] ? ? ? _.
by subst.
-
move=>[nd][[sent]|[recvd]][] _ _ _.
+
move=>Pts pt' ps' r' lg' Hpt' PS'.
move: (Pts pt Hpt); case: ifP=>_[][]; move /(pt_state_functional V PS)=>[]; try discriminate; move=>[] ? ? _ _; subst; move: (Pts pt' Hpt'); case: ifP=>_ [][]=>//; move: (C)=>[] _ _ _ /(_ _ (pts_in _ _ Hpt')) [] V' _; move /(pt_state_functional V' PS') =>[][] ? ? ? _; by subst.
+
move=>Hrecvd1 Hrecvd2.
case: (in_map_exists pt recvd).
*
move=>[b] H.
case: (Hrecvd1 _ _ Hpt H) => _ _.
case: ifP=>_; move /(pt_state_functional V PS)=>[]; discriminate.
*
move=>H.
case: (Hrecvd2 _ Hpt H)=>[][]; move /(pt_state_functional V PS)=>[]; try discriminate.
case=> ? ?.
subst.
move=> _ _ pt' ps' r' lg' Hpt' PS'.
case: (in_map_exists pt' recvd).
--
move=>[b] H'.
move: (Hrecvd1 _ _ Hpt' H')=>[]; case: ifP=> _ _ _; move: (C)=>[] _ _ _ /(_ _ (pts_in _ _ Hpt')) [] V' _; move /(pt_state_functional V' PS') =>[][] ? ? ? _; by subst.
--
move=>H'.
case: (Hrecvd2 _ Hpt' H')=>[][]; move: (C)=>[] _ _ _ /(_ _ (pts_in _ _ Hpt')) [] V' _; move /(pt_state_functional V' PS') =>[][] ? ? ? _; by subst.
-
Admitted.

Lemma cn_log_agreement d r lg pt : coh d -> cn_state d (r, CInit) lg -> Inv d -> pt \in pts -> pt_state d (r, PInit) lg pt.
Proof.
move=>C CS [r'][lg'].
move: C=>[] _ _ _ /(_ _ (cn_in _ _ _)) [] V _.
case.
-
move=>[].
move /(cn_state_functional V CS)=>[][] ? ?.
subst.
move=>H Hpt.
by move: (H pt Hpt)=>[].
-
move=>[nd][[sent]|[recvd]][]; move /(cn_state_functional V CS)=>[]; discriminate.
-
Admitted.

Lemma rc_step_external d (C : coh d) this (Hthis : this \in nodes cn pts others) tag from m i : ~~ internal_msg tag from this -> find i (dsoup d) = Some {| content := {| tag := tag; tms_cont := m |}; from := from; to := this; active := true |} -> rc_step tag from m C Hthis = loc this d.
Proof.
move/norP=>[]/and3P H1 /and3P H2 F.
rewrite /rc_step.
case: ifP=>// /eqP ?.
subst this.
pose proof C as C'.
case: C'=>Hs _ _ /(_ cn Hthis)[] _.
rewrite eqxx=>[][cs][lg] L.
rewrite (getStC_K _ L) (getStL_Kc _ _ L).
rewrite /cstep_recv.
case: ifP=>// /negbFE Hfrom.
case: cs L=>round cs L.
case: ifP=>//.
move: Hs=>[] _ /(_ _ _ F)[r].
rewrite /cohMsg/=.
case: ifP.
-
move=> _ [].
by rewrite (negbTE Hnin).
-
move=>_.
rewrite Hfrom.
move=>[] _ /andP[] T.
exfalso.
apply/H2.
by split.
