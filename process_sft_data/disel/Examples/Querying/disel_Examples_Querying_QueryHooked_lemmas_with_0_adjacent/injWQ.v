From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
Require Import Eqdep.
From fcsl Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Rely Actions.
From DiSeL Require Import SeqLib QueryProtocol NewStatePredicates Actions.
From DiSeL Require Import Injection Process Always HoareTriples InferenceRules While.
Section QueryHooked.
Variables (lq : Label) (pc : protocol).
Variable Data : Type.
Variable qnodes : seq nat.
Variable serialize : Data -> seq nat.
Variable deserialize : seq nat -> Data.
Hypothesis ds_inverse : left_inverse serialize deserialize.
Definition pq := QueryProtocol qnodes serialize lq.
Variable core_state_to_data : nid -> heap -> Data -> Prop.
Hypothesis core_state_to_data_inj : forall n h d d', core_state_to_data n h d -> core_state_to_data n h d' -> d = d'.
Definition query_hook : hook_type := fun hc hq ms to => forall n rid d, ms = rid :: serialize d -> core_state_to_data n hc d.
Definition query_hookz := (1, (plab pc), (plab pq, tresp)) \\-> query_hook.
Definition W : world := ((plab pc \\-> pc) \+ (plab pq \\-> pq), query_hookz).
Hypothesis Lab_neq: lq != (plab pc).
Variable this : nid.
Hypothesis this_in_qnodes: this \in qnodes.
Notation getSc s := (getStatelet s (plab pc)).
Notation getLc s := (getLocal this (getSc s)).
Notation getLc' s n := (getLocal n (getSc s)).
Notation getSq s := (getStatelet s (plab pq)).
Notation getLq s := (getLocal this (getSq s)).
Definition holds_res_perms d n (pp : nat -> Prop) := exists (reqs resp : seq (nid * nat)), getLocal n d = qst :-> (reqs, resp) /\ forall rn, (this, rn) \in resp -> pp rn.
Definition request_msg (t: nat) (_ : seq nat) := t == treq.
Definition response_msg (t: nat) (_ : seq nat) := t == tresp.
Definition query_init_state (to : nid) s := [/\ to \in qnodes, holds_res_perms (getSq s) to (fun _ : nat => false), no_msg_from_to' this to request_msg (dsoup (getSq s)) & no_msg_from_to' to this response_msg (dsoup (getSq s))].
Definition msg_just_sent d (reqs resp : seq (nid * nat)) req_num to := [/\ getLocal this d = qst :-> (reqs, resp), no_msg_from_to' to this response_msg (dsoup d), (to, req_num) \in reqs, msg_spec' this to treq ([:: req_num]) (dsoup d) & holds_res_perms d to (fun _ => false)].
Definition msg_received d (reqs resp : seq (nid * nat)) req_num to := [/\ getLocal this d = qst :-> (reqs, resp), (to, req_num) \in reqs, no_msg_from_to' this to request_msg (dsoup d), no_msg_from_to' to this response_msg (dsoup d) & holds_res_perms d to (fun rn => rn == req_num)].
Definition msg_responded d (reqs resp : seq (nid * nat)) req_num to data := [/\ getLocal this d = qst :-> (reqs, resp), (to, req_num) \in reqs, no_msg_from_to' this to request_msg (dsoup d), msg_spec' to this tresp (req_num :: serialize data) (dsoup d) & holds_res_perms d to (fun _ => false)].
Variable local_indicator : Data -> Pred heap.
Hypothesis core_state_stable_step : forall z s data s' n, this != z -> network_step (plab pc \\-> pc, Unit) z s s' -> n \in qnodes -> local_indicator data (getLc s) -> core_state_to_data n (getLc' s n) data -> core_state_to_data n (getLc' s' n) data.
Definition msg_story s req_num to data reqs resp := [/\ to \in qnodes, core_state_to_data to (getLc' s to) data, local_indicator data (getLc s) & let: d := getSq s in [\/ msg_just_sent d reqs resp req_num to, msg_received d reqs resp req_num to | msg_responded d reqs resp req_num to data]].
Program Definition read_request_id to : {rrd : seq (nid * nat) * seq (nid * nat) * Data}, DHT [this, W] (fun i => let: (reqs, resp, data) := rrd in [/\ getLq i = qst :-> (reqs, resp), local_indicator data (getLc i), query_init_state to i & core_state_to_data to (getLc' i to) data], fun (r : nat) m => let: (reqs, resp, data) := rrd in [/\ getLq m = qst :-> (reqs, resp), local_indicator data (getLc m), query_init_state to m, core_state_to_data to (getLc' m to) data & r = fresh_id reqs]) := Do _ (act (@skip_action_wrapper W this lq pq prEqQ _ (fun s pf => fresh_id (getSt this pf).1))).
Next Obligation.
apply: ghC=>i0 [[rq rs] d][P1] P2 P3 P4 C1.
apply: act_rule=>i1 R1; split=>[|r i2 i3]; first by case: (rely_coh R1).
case=>/=H1[Cj]Z; subst i1=>->R2.
rewrite !(rely_loc' _ R2) !(rely_loc' _ R1); split=>//.
-
by apply: (query_init_rely _ _ _ _ R2); apply: (query_init_rely _ _ _ _ R1).
-
apply: (core_state_stable _ _ _ _ R2); [by case: P3|by rewrite !(rely_loc' _ R1)|].
by apply: (core_state_stable _ _ _ _ R1)=>//; case: P3.
rewrite -(rely_loc' _ R1) in P1.
suff X: getSt this (Actions.safe_local prEqQ H1) = (rq, rs) by rewrite X.
by move: (getStK (Actions.safe_local prEqQ H1) P1)=>/=.
Program Definition send_req rid to := act (@send_action_wrapper W pq this (plab pq) prEqQ (qsend_req qnodes) _ [:: rid] to).
Next Obligation.
by rewrite !InE; left.
Program Definition send_req_act (rid : nat) (to : nid) : {rrd : seq (nid * nat) * seq (nid * nat) * Data}, DHT [this, W] (fun i => let: (reqs, resp, data) := rrd in [/\ getLq i = qst :-> (reqs, resp), local_indicator data (getLc i), rid = fresh_id reqs, query_init_state to i & core_state_to_data to (getLc' i to) data], fun (r : seq nat) m => let: (reqs, resp, data) := rrd in [/\ getLq m = qst :-> ((to, rid) :: reqs, resp), local_indicator data (getLc m), r = [:: rid], msg_story m rid to data ((to, rid) :: reqs) resp & core_state_to_data to (getLc' m to) data]) := Do (send_req rid to).
Next Obligation.
apply: ghC=>s0[[reqs resp] d]/=[P1] Pi P2 Q P3 C0.
apply: act_rule=>i1 R0; split=>//=[|r i2 i3[Hs]St R2].
-
rewrite /Actions.send_act_safe/=.
move/rely_coh: (R0)=>[_ C1]; rewrite -(rely_loc' _ R0) in P1.
move: (coh_coh lq C1); rewrite prEqQ=>Cq1; split=>//; [split=>//; try by case:Q| | ].
+
by exists Cq1; rewrite /QueryProtocol.send_req_prec (getStK _ P1)/= P2.
+
by apply/andP; split=>//; rewrite -(cohD C1) W_dom !inE eqxx orbC.
move=>z lc hk; rewrite find_umfilt eqxx /query_hookz.
move => F.
apply sym_eq in F.
move: F.
by move/find_some; rewrite domPt !inE=>/eqP.
have N: network_step W this i1 i2.
-
apply: (Actions.send_act_step_sem _ _ St)=>//; first by rewrite prEqQ.
by rewrite !InE; left.
rewrite (rely_loc' _ R2).
rewrite -(rely_loc' _ R0) in P1.
move/rely_coh: (R0)=>[_]C1; move: (coh_coh lq C1);rewrite prEqQ=>Cq1.
case: St=>->[h]/=[].
rewrite/QueryProtocol.send_step/QueryProtocol.send_step_fun/=.
rewrite (pf_irr (QueryProtocol.send_safe_coh _) Cq1).
rewrite (getStK _ P1); case=>Z Z'; subst h rid.
rewrite Z' locE; last first; [by apply: cohVl Cq1| by apply: cohS C1| by rewrite -(cohD C1) W_dom !inE eqxx orbC|].
have X : getLc i3 = getLc s0.
-
rewrite (rely_loc' _ R2) -(rely_loc' _ R0) Z'.
by rewrite /getStatelet findU; move/negbTE: Lab_neq; rewrite eq_sym=>->.
split=>//; try by rewrite X//.
apply: (msg_story_rely _ _ _ _ _ i2)=>//.
have E: core_state_to_data to (getLc' i1 to) = core_state_to_data to (getLc' i2 to).
-
case B: (to == this); [move/eqP:B=>Z; subst to | ]; last first.
+
by rewrite /getLocal (step_is_local _ N)=>//; move/negbT: B.
subst i2; rewrite ![getLc' _ _]/getLocal /getStatelet/=.
by rewrite findU; move/negbTE: Lab_neq; rewrite eq_sym=>->.
move: (query_init_rely _ s0 i1 Q R0)=>{Q}Q; subst i2.
move: (Q)=>[Q1 Q2 Q3 Q4].
move: (core_state_stable _ _ _ _ R0 Q1 Pi P3); rewrite E=>{E}E.
clear N R2 Q C0 X i3 P3.
split=>//.
-
rewrite /getStatelet findU; move/negbTE: Lab_neq; rewrite eq_sym=>->//=.
by rewrite (rely_loc' _ R0).
constructor 1.
split=>//; rewrite ?inE ?eqxx=>//=.
-
rewrite locE=>//; [by rewrite -(cohD C1) W_dom !inE eqxx orbC| apply: cohS C1|by apply: cohVl Cq1].
-
move=>m t c; rewrite /getStatelet findU eqxx (cohS C1)/=.
set ds := (dsoup _); rewrite findUnR; last first.
by rewrite valid_fresh; apply: cohVs Cq1.
rewrite domPt !inE/=; case:ifP=>[/eqP<-|_]; last by apply: Q4.
by rewrite findPt; case=><-.
-
rewrite /getStatelet findU eqxx (cohS C1)/=.
set ds := (dsoup _); split=>//.
exists (fresh ds); split=>//.
+
exists [:: fresh_id reqs].
rewrite findUnR; last by rewrite valid_fresh; apply: cohVs Cq1.
by rewrite domPt inE eqxx findPt.
+
move=>x[c]; rewrite findUnR; last by rewrite valid_fresh; apply: cohVs Cq1.
case:ifP=>[|_[]]; first by rewrite domPt inE=>/eqP->.
by move/(Q3 x treq c).
move=>x c ; rewrite findUnR; last by rewrite valid_fresh; apply: cohVs Cq1.
case:ifP=>[|_[]]; last by move/(Q3 x treq c).
by rewrite domPt inE=>/eqP->; rewrite findPt;case=>->.
set ds := (dsoup _).
case: Q2=>reqs'[resp'][G1 G2].
case X: (to == this).
-
exists ((this, fresh_id reqs) :: reqs), resp; move/eqP:X=>X; subst to.
rewrite P1 in G1; have V: valid (qst :-> (reqs, resp)) by [].
case: (hcancelPtV V G1)=>Z1 Z2; subst reqs' resp'=>{G1}.
split=>//; rewrite locE//; last first; [by apply: cohVl Cq1| by apply: cohS C1| by rewrite -(cohD C1) W_dom !inE eqxx orbC].
-
exists reqs', resp'; split=>//.
rewrite /getStatelet findU eqxx (cohS C1)/=.
by rewrite /getLocal findU X.
case: (Q)=>Nq _ _ _.
move: (core_state_stable _ _ _ _ R0 Nq Pi P3)=>H1.
rewrite -(rely_loc' _ R0) in Pi.
have Pi': local_indicator d (getLc' i2 this).
-
by rewrite Z'/getStatelet findU/= eq_sym; move/negbTE:Lab_neq->.
apply: (core_state_stable _ _ _ _ R2 Nq Pi').
by rewrite Z'/getStatelet findU/= eq_sym; move/negbTE:Lab_neq->.
Program Definition tryrecv_resp (rid : nat) (to : nid) := act (@tryrecv_action_wrapper W this (fun k n t (b : seq nat) => [&& k == lq, n == to, t == tresp, head 0 b == rid & to \in qnodes]) _).
Next Obligation.
case/andP:H=>/eqP=>->_; rewrite joinC domUn inE domPt inE eqxx andbC/=.
case: validUn=>//=; rewrite ?validPt//.
move=>k; rewrite !domPt !inE=>/eqP<-/eqP Z; subst lq.
by move/negbTE: Lab_neq; rewrite eqxx.
Definition recv_resp_cond (res : option Data): bool := if res is Some v then false else true.
Definition recv_resp_inv (rid : nat) to (rrd : (seq (nid * nat) * seq (nid * nat) * Data)) : cont (option Data) := fun res i => let: (reqs, resp, data) := rrd in if res is Some d then [/\ getLq i = qst :-> (reqs, resp), local_indicator data (getLc i), query_init_state to i, core_state_to_data to (getLc' i to) data & d = data] else [/\ getLq i = qst :-> ((to, rid) :: reqs, resp), local_indicator data (getLc i) & msg_story i rid to data ((to, rid) :: reqs) resp].
Program Definition receive_resp_loop (rid : nat) to : {(rrd : (seq (nid * nat) * seq (nid * nat) * Data))}, DHT [this, W] (fun i => let: (reqs, resp, data) := rrd in [/\ getLq i = qst :-> ((to, rid) :: reqs, resp), local_indicator data (getLc i), msg_story i rid to data ((to, rid) :: reqs) resp & core_state_to_data to (getLc' i to) data], fun res m => let: (reqs, resp, data) := rrd in exists d, res = Some d /\ [/\ getLq m = qst :-> (reqs, resp), local_indicator data (getLc m), query_init_state to m, core_state_to_data to (getLc' m to) data & d = data]) := Do _ (@while this W _ _ recv_resp_cond (recv_resp_inv rid to) _ (fun _ => Do _ ( r <-- tryrecv_resp rid to; match r with | Some (from, tg, body) => ret _ _ (Some (deserialize (behead body))) | None => ret _ _ None end )) None).
Next Obligation.
by apply: with_spec x.
Defined.
Next Obligation.
case: b H=>[b|]; rewrite /recv_resp_inv !(rely_loc' _ H0); case=>H1 H2 H3.
-
move=>H4 ->; split=>//; try by apply: (query_init_rely _ _ _ H3 H0).
-
by apply: (core_state_stable _ _ _ _ H0 _ H2)=>//; case: H3.
split=>//; try apply: (msg_story_rely _ _ _ _ _ _ _ H3 H0).
Defined.
Next Obligation.
rename H into d.
apply: ghC=>i0 [[reqs resp] data][G0 H0] C0; apply: step.
apply: act_rule=>i1 R1/=; split; first by case: (rely_coh R1).
case=>[[[from tg] body] i2 i3|i2 i3]; last first.
-
case=>S/=[]C1; case; last by case=>?[?][?][?][?][?][].
case=>_ _ Z; subst i2=>R3; apply: ret_rule=>i4 R4/=.
case: d G0 H0=>//=_[H1 H2 H3].
rewrite !(rely_loc' _ R4)!(rely_loc' _ R3)!(rely_loc' _ R1); split=>//.
by apply: (msg_story_rely _ _ _ _ _ _ _ _ R4); apply: (msg_story_rely _ _ _ _ _ _ _ _ R3); apply: (msg_story_rely _ _ _ _ _ _ _ _ R1).
case=>Sf[]C1[]=>[|[l'][mid][tms][from'][rt][pf][][E]Hin E2 Hw/=]; first by case.
case/andP=>/eqP Z1/andP[/eqP Z2]/andP[/eqP Z3]/andP[/eqP Z4]Qn->{i2}[Z5] Z6 Z7 R3.
subst l' from' from tg body rid.
move: rt pf (coh_s (w:=W) lq (s:=i1) C1) Hin R3 E2 Hw Z3 E; rewrite !prEqQ.
move=>/=rt pf C1' Hin R E2 Hw G E.
have D: rt = qrecv_resp _ by move: Hin G; do![case=>/=; first by move=>->].
subst rt=>{G}; simpl in E2.
set i2 := (upd _ _ _) in R.
apply: ret_rule=>i4 R3/=; rewrite !(rely_loc' _ R3)!(rely_loc' _ R).
suff X : [/\ getLocal this (getStatelet i2 lq) = qst :-> (reqs, resp), local_indicator data (getLc' i2 this), query_init_state to i2 & deserialize (behead tms) = data].
-
case: X=>X1 X2 X3 X4; split=>//.
by apply: (query_init_rely _ _ _ _ R3); apply: (query_init_rely _ _ _ _ R).
-
case: d G0 H0=>//=_[_ H2][_] H3 _ _; case: X3=>Nq _ _ _.
move: (X2); rewrite -(rely_loc' _ R)=>X3.
apply: (core_state_stable _ _ _ _ R3 Nq X3).
apply: (core_state_stable _ _ _ _ R Nq X2).
move: (core_state_stable _ _ _ _ R1 Nq H2 H3)=>{H2 H3 X3 X4}Y.
by subst i2; rewrite /getStatelet findU eq_sym; move/negbTE:Lab_neq=>->.
clear R i4 R3.
case: d G0 H0=>//=_[Q1 Q2 Q3]; rewrite -!(rely_loc' _ R1) in Q1 Q2.
move: (msg_story_rely _ _ _ _ _ _ _ Q3 R1)=>{Q3}Q3.
have P1: valid (dstate (getSq i1)) by case: (C1')=>P1 P2 P3 P4.
have P2: valid i1 by apply: (cohS C1).
have P3: lq \in dom i1.
rewrite -(cohD C1) domUn inE !domPt !inE/= inE eqxx orbC andbC/=.
by case/andP: W_valid.
clear Hin R1 C0 i0 i3 Hw.
case: Q3=>_ Q3 Q4 [].
-
case=>_/(_ mid (tag tms) (tms_cont tms)); rewrite -E.
by case: (tms)E2=>t c/=E2=>/(_ (erefl _))/=; subst t.
-
case=>_ _ _/(_ mid (tag tms) (tms_cont tms)); rewrite -E.
by case: (tms)E2=>t c/=E2=>/(_ (erefl _))/=; subst t.
case=>X1 _ X2 X3 X4; rewrite /query_init_state.
subst i2.
rewrite /receive_step/=/QueryProtocol.receive_step !(getStK C1' X1)/=!inE!eqxx/=.
rewrite !locE ?Qn/=;[|by case: C1'|by apply: cohS C1|by case: C1'].
apply sym_eq in E.
split=>//; last 1 first.
-
case:X3; case=>m'[[c]]E'/(_ mid) H.
have Z: m' = mid by apply: H; exists (tms_cont tms); rewrite E; case: (tms) E2=>/=t c'->.
subst m'; clear H; rewrite E in E'.
case: (tms) E' E=>t c'[]Z1 Z2; subst c' t=>E.
by move/(_ _ _ E)=>/eqP->/=; apply: ds_inverse.
-
by rewrite /getStatelet findU eq_sym; move/negbTE:Lab_neq=>->.
split=>//.
-
case B: (to == this); last first.
+
rewrite /getStatelet findU eqxx/= (cohS C1)/=.
rewrite /holds_res_perms in X4.
case: X4=> rq[rs][G1 G2]; exists rq, rs; split=>//.
by rewrite /getLocal/= findU; case:ifP=>//=/eqP Z; subst to; rewrite eqxx in B.
move/eqP:B=>B; subst to; case: X4=> rq[rs][G1 G2].
rewrite G1 in X1.
have V: valid (qst :-> (rq, rs)) by apply: validPt.
case: (hcancelPtV V X1)=>Z1 Z2; subst rq rs; exists reqs, resp; split=>//.
rewrite /getStatelet/= findU eqxx (cohS C1)/=/getLocal/=findU eqxx/=.
by case: C1'=>_->.
-
rewrite /getStatelet/= findU eqxx/= (cohS C1)/=.
by apply: (no_msg_from_to_consume' _ X2); case: C1'; case.
rewrite /getStatelet/= findU eqxx/= (cohS C1)/=.
case: (tms) E2 E=>t c/=-> E;apply: (no_msg_spec_consume _ E X3).
by case: C1'; case.
Next Obligation.
apply:ghC=>i1[[reqs resp] d][L1 I1 M1 S1] C1.
apply: (gh_ex (g:=(reqs, resp, d))); apply: call_rule=>// res i2[Q1 Q2] C2.
by case: res Q1 Q2=>//=data _ [Q1 Q2 Z]; exists data.
Variable default_data : Data.
Program Definition request_data_program to : {rrd : seq (nid * nat) * seq (nid * nat) * Data}, DHT [this, W] (fun i => let: (reqs, resp, data) := rrd in [/\ getLq i = qst :-> (reqs, resp), local_indicator data (getLc i), query_init_state to i & core_state_to_data to (getLc' i to) data], fun res m => let: (reqs, resp, data) := rrd in [/\ getLq m = qst :-> (reqs, resp), local_indicator data (getLc m), query_init_state to m, core_state_to_data to (getLc' m to) data & res = data]) := Do _ ( rid <-- read_request_id to; send_req_act rid to;; r <-- receive_resp_loop rid to; ret _ _ (if r is Some d then d else default_data) ).
Next Obligation.
apply:ghC=>i1[[reqs resp] d][L1 I1 M1 S1] C1.
apply: step; apply: (gh_ex (g:=(reqs, resp, d))).
apply: call_rule=>//r i2[P1 P2 P3 P4->{r}] C2.
apply: step; apply: (gh_ex (g:=(reqs, resp, d))).
apply: call_rule=>//_ i3[Q1 Q2 _ Q3 Q4]C3.
apply: step; apply: (gh_ex (g:=(reqs, resp, d))).
apply: call_rule=>//? i4[d'][->][T1] T2 T3 T4->{d'}C4.
apply: ret_rule=>i5 R; rewrite !(rely_loc' _ R); split=>//.
-
by apply: (query_init_rely _ _ _ _ R).
by apply: (core_state_stable _ _ _ _ R _ T2 T4); case: T3.
End QueryHooked.

Lemma injWQ : inj_ext injW = (lq \\-> pq, Unit).
Proof.
move: (W_valid)=>V; move: (cohK injW).
rewrite {1}eqW/mkWorld/= -!joinA /PCM.join/= in V.
case/andP: V=>/=V V'.
rewrite {1}eqW/mkWorld/= -!joinA /PCM.join/=; case=>H K.
case: (cancel V H)=>_; rewrite !unitR=>_{H}H1.
rewrite [inj_ext _]surjective_pairing -H1{H1}; congr (_, _).
rewrite !unitL joinC/=/query_hookz/= in V' K.
rewrite -[_ \\-> _]unitR in V'.
have Z: (1, plab pc, (lq, tresp)) \\-> query_hook \+ Unit = (1, plab pc, (lq, tresp)) \\-> query_hook \+ (inj_ext injW).2 by rewrite unitR.
by case: (cancel V' Z).
