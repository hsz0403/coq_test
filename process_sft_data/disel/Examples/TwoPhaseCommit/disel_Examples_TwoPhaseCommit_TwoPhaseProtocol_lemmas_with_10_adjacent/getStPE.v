From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX DepMaps Protocols Worlds NetworkSem Rely.
From DiSeL Require Import Actions Injection Process Always HoareTriples InferenceRules.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Module TPCProtocol.
Module States.
Definition data := seq nid.
Inductive CState := (* Waiting at a current stage *) | CInit (* Sent prepare message to some nodes at a current stage *) | CSentPrep of data & seq nid (* Received results from some nodes, bool for commit/abort *) | CWaitPrepResponse of data & seq (nid * bool) (* Send commit/abort requests *) | CSentCommit of data & seq nid | CSentAbort of data & seq nid (* Waiting for acks on Commit with some already collected *) | CWaitAckCommit of data & seq nid (* Waiting for acks on Abort with some already collected *) | CWaitAckAbort of data & seq nid.
Inductive PState := | PInit | PGotRequest of data | PRespondedYes of data | PRespondedNo of data | PCommitted of data | PAborted of data.
Definition st := ptr_nat 1.
Definition log := ptr_nat 2.
Definition Log := seq (bool * (seq nat)).
Definition CStateT := (nat * CState)%type.
Definition PStateT := (nat * PState)%type.
End States.
Import States.
Section TPCProtocol.
Variable cn : nid.
Variable pts : seq nid.
Variable others : seq nid.
Hypothesis Hnin : cn \notin pts.
Hypothesis Puniq : uniq pts.
Definition localCoh (n : nid) : Pred heap := [Pred h | valid h /\ if n == cn then exists (s : CStateT) (l : Log), h = st :-> s \+ log :-> l else if n \in pts then exists (s : PStateT) (l : Log), h = st :-> s \+ log :-> l else log \notin dom h].
Definition nodes := [:: cn] ++ pts ++ others.
Definition prep_req : nat := 0.
Definition prep_yes : nat := 1.
Definition prep_no : nat := 2.
Definition commit_req : nat := 3.
Definition abort_req : nat := 4.
Definition commit_ack : nat := 5.
Definition abort_ack : nat := 6.
Definition eval_req : nat := 7.
Definition eval_resp : nat := 8.
Definition ttag := nat.
Definition payload := seq nat.
Definition tags : seq ttag := [:: prep_req; prep_yes; prep_no; commit_req; abort_req; commit_ack; abort_ack; eval_req; eval_resp].
Definition tagFromParticipant (t : nat) : bool := (t \in [:: prep_yes; prep_no; commit_ack; abort_ack]).
Definition msgFromParticipant (tms : TaggedMessage) (y : nat) : bool := tagFromParticipant (tag tms) && (tms_cont tms == [:: y]).
Definition tagFromCoordinator (t : nat) : bool := (t \in [:: prep_req; commit_req; abort_req]).
Definition msgFromCoordinator (tms : TaggedMessage) (y : nat) : Prop := let: body := tms_cont tms in if tag tms == prep_req then exists data, body = y :: data else if tag tms == commit_req then body = [:: y] else if tag tms == abort_req then body = [:: y] else False.
Definition cohMsg (ms: msg TaggedMessage) (y : nat) : Prop := if from ms == cn then to ms \in pts /\ msgFromCoordinator (content ms) y else if from ms \in pts then to ms == cn /\ msgFromParticipant (content ms) y else True.
Definition soupCoh : Pred soup := [Pred s | valid s /\ forall m ms, find m s = Some ms -> exists y, cohMsg ms y].
Definition tpc_coh d : Prop := let: dl := dstate d in let: ds := dsoup d in [/\ soupCoh ds, dom dl =i nodes, valid dl & forall n, n \in nodes -> localCoh n (getLocal n d)].
Definition TPCCoh := CohPred (CohPredMixin l1 l2 l3).
Section TransitionLemmas.
End TransitionLemmas.
Definition getStC d (C : TPCCoh d) : CStateT := match find st (getLocal cn d) as f return _ = f -> _ with Some v => fun epf => icast (sym_eq (cohStC C epf)) (dyn_val v) | _ => fun epf => (0, CInit) end (erefl _).
Program Definition getStP n d (C : TPCCoh d) (pf : n \in nodes) : PStateT.
Proof.
case X: (n \in pts); last by exact: (0, PInit).
exact: (match find st (getLocal n d) as f return _ = f -> _ with Some v => fun epf => icast (sym_eq (cohStP C X epf)) (dyn_val v) | _ => fun epf => (0, PInit) end (erefl _)).
Defined.
Definition getStL n d (C : TPCCoh d) (pf : n \in nodes) : Log := match find log (getLocal n d) as f return _ = f -> _ with Some v => fun epf => icast (sym_eq (cohStL C pf epf)) (dyn_val v) | _ => fun epf => [::] end (erefl _).
Definition cstep_send (cs: CStateT) (to : nid) (d : data) (l : Log) : CStateT * Log := (* Only accept good destinations *) if to \in pts then let: (e, s) := cs in match s with | CInit => if pts == [:: to] then (e, CWaitPrepResponse d [::], l) else (e, CSentPrep d [:: to], l) (* Sending pre-messages *) | CSentPrep d' tos => (* Do not duplicate prepare-requests *) if perm_eq (to :: tos) pts (* If all sent, switch to the receiving state *) then (e, CWaitPrepResponse d' [::], l) else (e, CSentPrep d' (to :: tos), l) | CWaitPrepResponse d' res => (* Switch into sending commit or abort-messages mode *) if (perm_eq (map fst res) pts) then if all (fun r => r) (map snd res) then if pts == [:: to] then (e, CWaitAckCommit d' [::], l) else (e, CSentCommit d' [:: to], l) else if pts == [:: to] then (e, CWaitAckAbort d' [::], l) else (e, CSentAbort d' [:: to], l) else (cs, l) | CSentCommit d' tos => (* Sending commit messages *) if perm_eq (to :: tos) pts then (e, CWaitAckCommit d' [::], l) else (e, CSentCommit d' (to :: tos), l) | CSentAbort d' tos => if perm_eq (to :: tos) pts then (e, CWaitAckAbort d' [::], l) else (e, CSentAbort d' (to :: tos), l) | _ => (cs, l) end else (cs, l).
Definition c_matches_tag s mtag : bool := match s with | CWaitPrepResponse _ _ => (mtag == prep_yes) || (mtag == prep_no) | CWaitAckCommit _ _ => mtag == commit_ack | CWaitAckAbort _ _ => mtag == abort_ack | _ => false end.
Definition cstep_recv' (cs : CStateT) (from : nid) (mtag : ttag) (mbody : payload) (l : Log) : CStateT * Log := let: (e, s) := cs in match s with | CWaitPrepResponse d' res => (* All responses already collected or already received from this participant *) if (from \in (map fst res)) then (cs, l) (* Save result *) else (e, CWaitPrepResponse d' ((from, mtag == prep_yes) :: res), l) | CWaitAckCommit d' res => if from \in res then (cs, l) else if (perm_eq (from :: res) pts) then ((e.+1, CInit), rcons l (true, d')) else (e, CWaitAckCommit d' (from :: res), l) | CWaitAckAbort d' res => if from \in res then (cs, l) else if (perm_eq (from :: res) pts) then ((e.+1, CInit), rcons l (false, d')) else (e, CWaitAckAbort d' (from :: res), l) | _ => (cs, l) end.
Definition cstep_recv (cs: CStateT) (from : nid) (mtag : ttag) (mbody : payload) (l : Log) : CStateT * Log := if (from \notin pts) then (cs, l) else let: (e, s) := cs in (* Ignore messages from irrelevant rounds *) if (head 0 mbody != e) then (cs, l) else cstep_recv' cs from mtag mbody l .
Section CoordinatorGenericSendTransitions.
Notation coh := TPCCoh.
Definition HCn this to := (this == cn /\ to \in pts).
Definition mkLocal {T} (sl : T * Log) := st :-> sl.1 \+ log :-> sl.2.
Variable stag : ttag.
Variable prec : CStateT -> nid -> payload -> Prop.
Hypothesis cn_prec_safe : forall this to s m, HCn this to -> prec s to m -> cohMsg (Msg (TMsg stag m) this to true) s.1.
Definition cn_safe (this n : nid) (d : dstatelet) (msg : data) := HCn this n /\ exists (C : coh d), prec (getStC C) n msg.
Definition cn_step (this to : nid) (d : dstatelet) (msg : seq nat) (pf : cn_safe this to d msg) := let C := cn_safe_coh pf in let s := getStC C in let l := getStL C (cn_this_in (proj1 pf)) in Some (mkLocal (cstep_send s to (behead msg) l)).
Definition cn_send_trans := SendTrans cn_safe_coh cn_safe_in cn_safe_def cn_step_coh.
End CoordinatorGenericSendTransitions.
Section CoordinatorSendTransitions.
Definition send_prep_prec (p : CStateT) to (m : payload) := (exists n, p = (n, CInit) /\ exists d, m = n :: d) \/ exists n d ps, [/\ p = (n, CSentPrep d ps), m = n :: d & to \notin ps].
Program Definition cn_send_prep_trans : send_trans TPCCoh := @cn_send_trans prep_req send_prep_prec _.
Next Obligation.
case: H=>/eqP->H; rewrite /cohMsg eqxx; split=>//=.
case: H0; first by case=>n[->{s}][d->{m}]/=; eexists _.
by case=>n[d][ps][->{s}]->; eexists _.
Definition send_commit_prec (p : CStateT) to (m : payload) := (exists n d res, [/\ p = (n, CWaitPrepResponse d res), m = [::n], perm_eq (map fst res) pts & all (fun r => r) (map snd res)]) \/ exists n d ps, [/\ p = (n, CSentCommit d ps), m = [::n] & to \notin ps].
Program Definition cn_send_commit_trans : send_trans TPCCoh := @cn_send_trans commit_req send_commit_prec _.
Next Obligation.
case: H=>/eqP->H; rewrite /cohMsg eqxx; split=>//=.
case: H0; by case=>n[d][res][->{s}]/=->.
Definition send_abort_prec (p : CStateT) to (m : payload) := (exists n d res, [/\ p = (n, CWaitPrepResponse d res), m = [::n], perm_eq (map fst res) pts & has (fun r => negb r) (map snd res)]) \/ exists n d ps, [/\ p = (n, CSentAbort d ps), m = [::n] & to \notin ps].
Program Definition cn_send_abort_trans : send_trans TPCCoh := @cn_send_trans abort_req send_abort_prec _.
Next Obligation.
case: H=>/eqP->H; rewrite /cohMsg eqxx; split=>//=.
by case:H0;move=>[n][d][res][->{s}]/=->.
End CoordinatorSendTransitions.
Section CoordinatorGenericReceiveTransitions.
Notation coh := TPCCoh.
Variable rc_tag : ttag.
Variable rc_wf : forall d, coh d -> nid -> nid -> TaggedMessage -> bool.
Definition rc_step : receive_step_t coh := fun this (from : nid) (m : seq nat) d (pf : coh d) (pt : this \in nodes) => if (this == cn) then let s := getStC pf in let l := @getStL this d pf pt in mkLocal (cstep_recv s from rc_tag m l) else getLocal this d.
Definition rc_recv_trans := ReceiveTrans rc_step_coh.
End CoordinatorGenericReceiveTransitions.
Section CoordinatorReceiveTransitions.
Definition cn_msg_wf d (C : TPCCoh d) (this from : nid) := [pred m : TaggedMessage | c_matches_tag (getStC C).2 (tag m)].
Definition cn_receive_prep_yes_trans := rc_recv_trans prep_yes cn_msg_wf.
Definition cn_receive_prep_no_trans := rc_recv_trans prep_no cn_msg_wf.
Definition cn_receive_commit_ack_trans := rc_recv_trans commit_ack cn_msg_wf.
Definition cn_receive_abort_ack_trans := rc_recv_trans abort_ack cn_msg_wf.
End CoordinatorReceiveTransitions.
Definition pstep_send (cs: PStateT) (l : Log) (commit : bool) : PStateT * Log := let: (e, s) := cs in match s with | PGotRequest d => if commit then (e, PRespondedYes d, l) else (e, PRespondedNo d, l) | PCommitted d => (e.+1, PInit, l) | PAborted d => (e.+1, PInit, l) | _ => (cs, l) end.
Definition p_matches_tag s mtag : bool := match s with | PInit => mtag == prep_req (* Just because I responded Yes, doesn't mean everyone else did. So the transaction might have been aborted. *) | PRespondedYes _ => (mtag == commit_req) || (mtag == abort_req) | PRespondedNo _ => mtag == abort_req | _ => false end.
Definition pstep_recv (ps: PStateT) (from : nid) (mtag : ttag) (mbody : payload) (l : Log) : PStateT * Log := if (negb (p_matches_tag ps.2 mtag)) || (from != cn) || (head 0 mbody != ps.1) then (ps, l) else let: (e, s) := ps in match s with | PInit => (e, PGotRequest (behead mbody), l) | PRespondedYes d => if mtag == commit_req then (e, PCommitted d, rcons l (true, d)) else (* Even though I said Yes, the coordinator decided to abort. *) (e, PAborted d, rcons l (false, d)) | PRespondedNo d => (e, PAborted d, rcons l (false, d)) | _ => (ps, l) end.
Section ParticipantGenericSendTransitions.
Notation coh := TPCCoh.
Definition HPn this to := (this \in pts /\ to == cn).
Variable ptag : ttag.
Variable prec : PStateT -> payload -> Prop.
Hypothesis pn_prec_safe : forall this to s m, HPn this to -> prec s m -> cohMsg (Msg (TMsg ptag m) this to true) s.1.
Definition pn_safe (this n : nid) (d : dstatelet) (msg : data) := HPn this n /\ exists (Hp : HPn this n) (C : coh d), prec (getStP C (pn_this_in Hp)) msg.
Variable commit : bool.
Definition pn_step (this to : nid) (d : dstatelet) (msg : seq nat) (pf : pn_safe this to d msg) := let C := pn_safe_coh pf in let s := getStP C (pn_this_in (proj1 pf)) in let l := getStL C (pn_this_in (proj1 pf)) in Some (mkLocal (pstep_send s l commit)).
Definition pn_send_trans := SendTrans pn_safe_coh pn_safe_in pn_safe_def pn_step_coh.
End ParticipantGenericSendTransitions.
Section ParticipantSendTransitions.
Definition send_prep_resp_prec (ps : data -> PState) (p : PStateT) (m : payload) := exists n d, p = (n, ps d) /\ m = [:: n].
Program Definition pn_gen_send_trans (t : ttag) (T: t \in [:: prep_yes; prep_no; commit_ack; abort_ack]) (ps : data -> PState) c := @pn_send_trans t (send_prep_resp_prec ps) _ c.
Next Obligation.
case: H=>H/eqP->{to}.
rewrite /cohMsg (this_not_pts H) H eqxx/=; split=>//.
by apply/andP; split=>//=; case: H0=>[?][?][->]/eqP.
Program Definition pn_send_yes_trans := @pn_gen_send_trans prep_yes _ PGotRequest true.
Program Definition pn_send_no_trans := @pn_gen_send_trans prep_no _ PGotRequest false.
Program Definition pn_commit_ack_trans := @pn_gen_send_trans commit_ack _ PCommitted true.
Program Definition pn_abort_ack_trans := @pn_gen_send_trans abort_ack _ PAborted false.
End ParticipantSendTransitions.
Section ParticipantGenericReceiveTransitions.
Notation coh := TPCCoh.
Variable rp_tag : ttag.
Variable rp_wf : forall d, coh d -> nid -> nid -> pred payload.
Definition rp_step : receive_step_t coh := fun this (from : nid) (m : seq nat) d (pf : coh d) (pt : this \in nodes) => if (this \in pts) then let s := getStP pf pt in let l := @getStL this d pf pt in mkLocal (pstep_recv s from rp_tag m l) else getLocal this d.
Definition rp_recv_trans := ReceiveTrans rp_step_coh.
End ParticipantGenericReceiveTransitions.
Section ParticipantReceiveTransitions.
Definition pn_msg_wf d (_ : TPCCoh d) (this from : nid) := [pred p : payload | true].
Definition pn_receive_got_prep_trans := rp_recv_trans prep_req pn_msg_wf.
Definition pn_receive_commit_ack_trans := rp_recv_trans commit_req pn_msg_wf.
Definition pn_receive_abort_ack_trans := rp_recv_trans abort_req pn_msg_wf.
End ParticipantReceiveTransitions.
Section Protocol.
Variable l : Label.
Definition tpc_sends := [:: cn_send_prep_trans; cn_send_commit_trans; cn_send_abort_trans; pn_send_yes_trans; pn_send_no_trans; pn_commit_ack_trans; pn_abort_ack_trans ].
Definition tpc_receives := [:: cn_receive_prep_yes_trans; cn_receive_prep_no_trans; cn_receive_commit_ack_trans; cn_receive_abort_ack_trans; pn_receive_got_prep_trans; pn_receive_commit_ack_trans; pn_receive_abort_ack_trans ].
Program Definition TwoPhaseCommitProtocol : protocol := @Protocol _ l _ tpc_sends tpc_receives _ _.
End Protocol.
End TPCProtocol.
Module Exports.
Section Exports.
Definition TwoPhaseCommitProtocol := TwoPhaseCommitProtocol.
Definition cn_send_prep_trans := cn_send_prep_trans.
Definition cn_send_commit_trans := cn_send_commit_trans.
Definition cn_send_abort_trans := cn_send_abort_trans.
Definition pn_send_yes_trans := pn_send_yes_trans.
Definition pn_send_no_trans := pn_send_no_trans.
Definition pn_commit_ack_trans := pn_commit_ack_trans.
Definition pn_abort_ack_trans := pn_abort_ack_trans.
Definition cn_receive_prep_yes_trans := cn_receive_prep_yes_trans.
Definition cn_receive_prep_no_trans := cn_receive_prep_no_trans.
Definition cn_receive_commit_ack_trans := cn_receive_commit_ack_trans.
Definition cn_receive_abort_ack_trans := cn_receive_abort_ack_trans.
Definition pn_receive_got_prep_trans := pn_receive_got_prep_trans.
Definition pn_receive_commit_ack_trans := pn_receive_commit_ack_trans.
Definition pn_receive_abort_ack_trans := pn_receive_abort_ack_trans.
Definition prep_req := prep_req.
Definition prep_yes := prep_yes.
Definition prep_no := prep_no.
Definition commit_req := commit_req.
Definition abort_req := abort_req.
Definition commit_ack := commit_ack.
Definition abort_ack := abort_ack.
Definition getStC := getStC.
Definition getStP := getStP.
Definition getStL := getStL.
Definition getStCE := getStCE.
Definition getStPE := getStPE.
Definition getStCL := getStLE.
End Exports.
End Exports.
End TPCProtocol.
Export TPCProtocol.States.
Export TPCProtocol.Exports.

Lemma cohStP n d (C : TPCCoh d) (H : n \in pts) s: find st (getLocal n d) = Some s -> dyn_tp s = PStateT.
Proof.
have pf: n \in nodes by rewrite inE/=orbC mem_cat H.
move: (locCn C pf); rewrite H=>[[V]].
case E: (n == cn); last first.
-
move=>[s'][l']Z; rewrite Z in V *.
by rewrite findUnL//; rewrite domPt inE/= findPt/=; case=><-.
Admitted.

Lemma getStC_K d (C : TPCCoh d) m (l : Log): getLocal cn d = st :-> m \+ log :-> l -> getStC C = m.
Proof.
move=>E; rewrite /getStC/=.
have pf : cn \in nodes by rewrite inE eqxx.
have V: valid (getLocal cn d) by case: (locCn C pf).
move: (cohStC C); rewrite !E=>/= H.
Admitted.

Lemma getStP_K n d (C : TPCCoh d) (pf : n \in nodes) m (l : Log): n \in pts -> getLocal n d = st :-> m \+ log :-> l -> getStP C pf = m.
Proof.
move=>X E; rewrite /getStP/=.
have V: valid (getLocal n d) by case: (locCn C pf).
rewrite E in V.
move: (cohStP C); case B: (n \in pts)=>//=; last by rewrite X in B.
move=>H; move: (H (erefl true))=>{H}; rewrite E=>/=H.
Admitted.

Lemma cohStL d (C : TPCCoh d) n (H : n \in nodes) l: find log (getLocal n d) = Some l -> dyn_tp l = Log.
Proof.
move: (locCn C H)=>[V].
case B: (n == cn)=>/=.
-
move=>[s'][l']Z; rewrite Z in V *; by rewrite joinC in V *; rewrite findPtUn //; case=><-/=.
rewrite inE in H; case/orP: H; first by rewrite B.
rewrite/= mem_cat; case X: (n \in pts)=>/=_.
-
move=>[s'][l']Z; rewrite Z in V *; by rewrite joinC in V *; rewrite findPtUn //; case=><-/=.
Admitted.

Lemma getStL_Kc n d (C : TPCCoh d) (pf : n \in nodes) (m : CStateT) (l : Log): getLocal n d = st :-> m \+ log :-> l -> getStL C pf = l.
Proof.
move=>E; rewrite /getStL/=.
have V: valid (getLocal n d) by case: (locCn C pf).
Admitted.

Lemma getStL_Kp n d (C : TPCCoh d) (pf : n \in nodes) (m : PStateT) (l : Log): getLocal n d = st :-> m \+ log :-> l -> getStL C pf = l.
Proof.
move=>E; rewrite /getStL/=.
have V: valid (getLocal n d) by case: (locCn C pf).
Admitted.

Lemma cn_in : cn \in nodes.
Proof.
Admitted.

Lemma pts_in n: n \in pts -> n \in nodes.
Proof.
Admitted.

Lemma cn_pts_in this : this \in cn :: pts -> this \in nodes.
Proof.
Admitted.

Lemma getStCE l i j pf pf' : getLocal cn (getStatelet j l) = getLocal cn (getStatelet i l) -> @getStC (getStatelet j l) pf' = @getStC (getStatelet i l) pf.
Proof.
case: {-1}(pf)=>_ _ _/(_ _ cn_in)[]V; rewrite eqxx=>[[cs]][lg]E.
Admitted.

Lemma getStLE l this i j pf pf' : forall (N : this \in cn :: pts), getLocal this (getStatelet j l) = getLocal this (getStatelet i l) -> @getStL _ (getStatelet j l) pf' (cn_pts_in N) = @getStL _ (getStatelet i l) pf (cn_pts_in N).
Proof.
move=>N; case: {-1}(pf)=>_ _ _/(_ _ (cn_pts_in N))[]V.
move: (N)=>N'.
rewrite inE in N; case/orP: N.
-
move/eqP=>Z; subst this; rewrite eqxx=>[[cs]][lg]E.
rewrite (@getStL_Kc _ _ pf (cn_pts_in N') cs lg)//.
by rewrite E=>E'; rewrite (@getStL_Kc _ _ pf' (cn_pts_in N') cs lg)//.
move=>Z; rewrite (this_not_pts Z) Z=>[[cs]][lg]E.
rewrite (@getStL_Kp _ _ pf (cn_pts_in N') cs lg)//.
Admitted.

Lemma cn_safe_coh this to d m : cn_safe this to d m -> coh d.
Proof.
Admitted.

Lemma cn_this_in this to : HCn this to -> this \in nodes.
Proof.
Admitted.

Lemma cn_to_in this to : HCn this to -> to \in nodes.
Proof.
Admitted.

Lemma cn_safe_in this to d m : cn_safe this to d m -> this \in nodes /\ to \in nodes.
Proof.
Admitted.

Lemma cn_step_coh : s_step_coh_t coh stag cn_step.
Proof.
move=>this to d msg pf h[]->{h}.
have C : (coh d) by case: pf=>?[].
have E: this = cn by case: pf=>[][]/eqP.
split=>/=.
-
apply: send_soupCoh; first by case:(cn_safe_coh pf).
exists (getStC (cn_safe_coh pf)).1.
case: (pf)=>H[C']P/=; move: (conj H _)=>pf'.
by move: (cn_prec_safe H P); rewrite -(pf_irr C' (cn_safe_coh pf')).
-
by apply: trans_updDom=>//; case: (cn_safe_in pf).
-
by rewrite validU; apply: cohVl C.
move=>n Ni.
rewrite /localCoh/=.
rewrite /getLocal/=findU; case: ifP=>B; last by case: C=>_ _ _/(_ n Ni).
move/eqP: B=>Z; subst n this; rewrite eqxx (cohVl C)/=.
Admitted.

Lemma cn_safe_def this to d msg : cn_safe this to d msg <-> exists b pf, @cn_step this to d msg pf = Some b.
Proof.
split=>[pf/=|]; last by case=>?[].
set b := let C := cn_safe_coh pf in let s := getStC C in let l := getStL C (cn_this_in (proj1 pf)) in mkLocal (cstep_send s to (behead msg) l).
Admitted.

Definition send_prep_prec (p : CStateT) to (m : payload) := (exists n, p = (n, CInit) /\ exists d, m = n :: d) \/ exists n d ps, [/\ p = (n, CSentPrep d ps), m = n :: d & to \notin ps].
Program Definition cn_send_prep_trans : send_trans TPCCoh := @cn_send_trans prep_req send_prep_prec _.
Next Obligation.
case: H=>/eqP->H; rewrite /cohMsg eqxx; split=>//=.
case: H0; first by case=>n[->{s}][d->{m}]/=; eexists _.
Admitted.

Definition send_commit_prec (p : CStateT) to (m : payload) := (exists n d res, [/\ p = (n, CWaitPrepResponse d res), m = [::n], perm_eq (map fst res) pts & all (fun r => r) (map snd res)]) \/ exists n d ps, [/\ p = (n, CSentCommit d ps), m = [::n] & to \notin ps].
Program Definition cn_send_commit_trans : send_trans TPCCoh := @cn_send_trans commit_req send_commit_prec _.
Next Obligation.
case: H=>/eqP->H; rewrite /cohMsg eqxx; split=>//=.
Admitted.

Definition send_abort_prec (p : CStateT) to (m : payload) := (exists n d res, [/\ p = (n, CWaitPrepResponse d res), m = [::n], perm_eq (map fst res) pts & has (fun r => negb r) (map snd res)]) \/ exists n d ps, [/\ p = (n, CSentAbort d ps), m = [::n] & to \notin ps].
Program Definition cn_send_abort_trans : send_trans TPCCoh := @cn_send_trans abort_req send_abort_prec _.
Next Obligation.
case: H=>/eqP->H; rewrite /cohMsg eqxx; split=>//=.
Admitted.

Lemma getStPE l n i j C C' pf : n \in pts -> getLocal n (getStatelet j l) = getLocal n (getStatelet i l) -> @getStP n (getStatelet j l) C' pf = @getStP n (getStatelet i l) C pf.
Proof.
move=>I; case: {-1}(C)=>_ _ _/(_ _ pf)[]V; rewrite I.
case: ifP; first by move/eqP=>Z; subst n; move: (Hnin); rewrite I.
move=>_[ps][lg] E.
by rewrite (getStP_K _ pf I E);rewrite E=>E'; rewrite (getStP_K _ pf I E').
