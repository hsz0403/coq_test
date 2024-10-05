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
by rewrite eqxx.
