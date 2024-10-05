From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Rely.
From DiSeL Require Import Actions Injection Process Always HoareTriples InferenceRules.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Module ResourceProtocol.
Section ResourceProtocol.
Variable server : nid.
Variable clients : seq nid.
Hypothesis Hnin : server \notin clients.
Hypothesis Huniq : uniq clients.
Definition nodes := [:: server] ++ clients.
Notation epoch := nat (only parsing).
Notation client := nid (only parsing).
Definition value := nat.
Inductive request := | Update of client * epoch * value | Read of client * epoch.
Definition request_eq (r1 r2 : request) : bool := match r1, r2 with | Update x1, Update x2 => x1 == x2 | Read x1, Read x2 => x1 == x2 | _, _ => false end.
Canonical request_eqMixin := EqMixin request_eqP.
Canonical request_eqType := Eval hnf in EqType request request_eqMixin.
Record server_state := ServerState { current_epoch : epoch; current_value : value; outstanding : seq request }.
Definition update_tag := 0.
Definition update_response_tag := 1.
Definition read_tag := 2.
Definition read_response_tag := 3.
Definition msg_from_client ms := (tag ms == update_tag /\ exists e v, tms_cont ms = [:: e; v]) \/ (tag ms == read_tag /\ exists e, tms_cont ms = [:: e]).
Definition msg_from_server ms := (tag ms == update_response_tag /\ exists e v b, tms_cont ms = [:: e; v; b]) \/ (tag ms == read_response_tag /\ ((exists e v, tms_cont ms = [:: e; v] (* success *)) \/ (exists e, tms_cont ms = [:: e] (* failure *)))).
Definition coh_msg pkt := if from pkt == server then to pkt \in clients /\ msg_from_server (content pkt) else if from pkt \in clients then to pkt == server /\ msg_from_client (content pkt) else False.
Definition st := ptr_nat 1.
Definition client_local_coh := [Pred h | h = Heap.empty].
Definition server_local_coh (ss : server_state) := [Pred h | h = st :-> ss].
Definition local_coh (n : nid) := [Pred h | valid h /\ if n == server then exists ss, server_local_coh ss h else n \in clients /\ client_local_coh h].
Definition soup_coh : Pred soup := [Pred s | valid s /\ forall m ms, find m s = Some ms -> active ms -> coh_msg ms].
Definition state_coh d := forall n, n \in nodes -> local_coh n (getLocal n d).
Definition resource_coh d := let: dl := dstate d in let: ds := dsoup d in [/\ soup_coh ds , dom dl =i nodes , valid dl & state_coh d].
Definition ResourceCoh := CohPred (CohPredMixin l1 l2 l3).
Definition server_send_step (ss : server_state) (to : nid) (tag : nat) (msg : seq nat) : server_state := if to \in clients then if tag == update_response_tag then if msg is [:: e; v; b] then let: r := Update (to, e, v) in if current_epoch ss <= e then ServerState e v (seq.rem r (outstanding ss)) else ServerState (current_epoch ss) (current_value ss) (seq.rem r (outstanding ss)) else ss else if tag == read_response_tag then if msg is e :: _ then let: r := Read (to, e) in ServerState (current_epoch ss) (current_value ss) (seq.rem r (outstanding ss)) else ss else ss else ss.
Definition server_recv_step (ss : server_state) (from : nid) (mtag : nat) (mbody : seq nat) : server_state := if mtag == update_tag then if mbody is [:: e; v] then ServerState (current_epoch ss) (current_value ss) (cons (Update (from, e, v)) (outstanding ss)) else ss else (* mtag == read_tag *) if mbody is [:: e] then ServerState (current_epoch ss) (current_value ss) (cons (Read (from, e)) (outstanding ss)) else ss.
Section GetterLemmas.
Definition getSt_server d (C : ResourceCoh d) : server_state := match find st (getLocal server d) as f return _ = f -> _ with Some v => fun epf => icast (sym_eq (getLocal_server_st_tp C epf)) (dyn_val v) | _ => fun epf => ServerState 0 0 [::] end (erefl _).
End GetterLemmas.
Section ServerGenericSendTransitions.
Definition HServ this to := (this == server /\ to \in clients).
Variable the_tag : nat.
Variable prec : server_state -> nid -> seq nat -> Prop.
Hypothesis prec_safe : forall this to s m, HServ this to -> prec s to m -> coh_msg (Msg (TMsg the_tag m) this to true).
Notation coh := ResourceCoh.
Definition server_send_safe (this n : nid) (d : dstatelet) (msg : seq nat) := HServ this n /\ exists (C : coh d), prec (getSt_server C) n msg.
Definition server_step (this to : nid) (d : dstatelet) (msg : seq nat) (pf : server_send_safe this to d msg) := let C := server_send_safe_coh pf in let s := getSt_server C in Some (st :-> server_send_step s to the_tag msg).
Definition server_send_trans := SendTrans server_send_safe_coh server_send_safe_in server_step_def server_step_coh.
End ServerGenericSendTransitions.
Section ServerSendTransitions.
Definition server_send_update_response_prec (ss : server_state) to m := exists e v b e0 v0 outstanding, m = [:: e; v; b] /\ let: r := Update (to, e, v) in r \in outstanding /\ ss = ServerState e0 v0 outstanding /\ b = if e0 <= e then 1 else 0.
Program Definition server_send_update_response_trans : send_trans ResourceCoh := @server_send_trans update_response_tag server_send_update_response_prec _.
Next Obligation.
case: H=>/eqP->H; rewrite /coh_msg eqxx; split=>//=.
case: H0=>[e][v][b][e0][v0][out][]->[U][_]->.
rewrite /msg_from_server /= eqxx.
left.
split=>//.
by eexists _, _, _.
Definition server_send_read_response_prec (ss : server_state) to m := exists e e0 v0 outstanding, ss = ServerState e0 v0 outstanding /\ let: r := Read (to, e) in r \in outstanding /\ m = if e0 <= e then [:: e; v0 ] else [:: e].
Program Definition server_send_read_response_trans : send_trans ResourceCoh := @server_send_trans read_response_tag server_send_read_response_prec _.
Next Obligation.
case: H=>/eqP->H; rewrite /coh_msg eqxx; split=>//=.
case: H0=>[e][e0][v0][out][_][R]->.
rewrite /msg_from_server /= eqxx.
right.
split=>//.
by case: ifP=>_; [left; eexists _,_|right; eexists].
End ServerSendTransitions.
Section ServerGenericReceiveTransitions.
Notation coh := ResourceCoh.
Variable the_tag : nat.
Variable server_recv_wf : forall d, coh d -> nid -> nid -> TaggedMessage -> bool.
Definition rs_step : receive_step_t coh := fun this (from : nid) (m : seq nat) d (pf : coh d) (pt : this \in nodes) => if (this == server) then let s := getSt_server pf in st :-> server_recv_step s from the_tag m else getLocal this d.
Definition rs_recv_trans := ReceiveTrans rs_step_coh.
End ServerGenericReceiveTransitions.
Section ServerReceiveTransitions.
Definition s_matches_tag (ss : server_state) (from : nid) t := (t == read_tag) || (t == update_tag).
Definition server_msg_wf d (C : ResourceCoh d) (this from : nid) := [pred m : TaggedMessage | s_matches_tag (getSt_server C) from (tag m)].
Definition server_recv_update_trans := rs_recv_trans update_tag server_msg_wf.
Definition server_recv_read_trans := rs_recv_trans read_tag server_msg_wf.
End ServerReceiveTransitions.
Section ClientGenericSendTransitions.
Definition HClient this to := (this \in clients /\ to == server).
Variable the_tag : nat.
Variable prec : nid -> seq nat -> Prop.
Hypothesis prec_safe : forall this to m, HClient this to -> prec to m -> msg_from_client (TMsg the_tag m).
Notation coh := ResourceCoh.
Definition client_send_safe (this n : nid) (d : dstatelet) (msg : seq nat) := [/\ HClient this n, coh d & prec n msg].
Definition client_step (this to : nid) (d : dstatelet) (msg : seq nat) (pf : client_send_safe this to d msg) := Some Heap.empty.
Definition client_send_trans := SendTrans client_send_safe_coh client_send_safe_in client_step_def client_step_coh.
End ClientGenericSendTransitions.
Section ClientSendTransitions.
Definition client_send_update_prec (to : nid) (m : seq nat) := exists e v, m = [:: e; v].
Program Definition client_send_update_trans : send_trans ResourceCoh := @client_send_trans update_tag client_send_update_prec _.
Next Obligation.
by left.
Definition client_send_read_prec (to : nid) (m : seq nat) := exists e, m = [:: e].
Program Definition client_send_read_trans : send_trans ResourceCoh := @client_send_trans read_tag client_send_read_prec _.
Next Obligation.
by right.
End ClientSendTransitions.
Section ClientGenericReceiveTransitions.
Notation coh := ResourceCoh.
Variable the_tag : nat.
Variable client_recv_wf : forall d, coh d -> nid -> nid -> TaggedMessage -> bool.
Definition rc_step : receive_step_t coh := fun this (from : nid) (m : seq nat) d (pf : coh d) (pt : this \in nodes) => getLocal this d.
Definition rc_recv_trans := ReceiveTrans rc_step_coh.
End ClientGenericReceiveTransitions.
Section ClientReceiveTransitions.
Definition client_msg_wf d (_ : ResourceCoh d) (this from : nid) := [pred m : TaggedMessage | true].
Definition client_recv_update_response_trans := rc_recv_trans update_response_tag client_msg_wf.
Definition client_recv_read_response_trans := rc_recv_trans read_response_tag client_msg_wf.
End ClientReceiveTransitions.
Section Protocol.
Variable l : Label.
Definition resource_sends := [:: server_send_update_response_trans; server_send_read_response_trans; client_send_update_trans; client_send_read_trans ].
Definition resource_receives := [:: server_recv_update_trans; server_recv_read_trans; client_recv_update_response_trans; client_recv_read_response_trans ].
Program Definition ResourceProtocol : protocol := @Protocol _ l _ resource_sends resource_receives _ _.
End Protocol.
End ResourceProtocol.
Module Exports.
Section Exports.
Definition ResourceProtocol := ResourceProtocol.
End Exports.
End Exports.
End ResourceProtocol.
Export ResourceProtocol.Exports.

Lemma client_not_server n : n \in clients -> (n == server) = false.
Proof.
move=>H.
case E: (n == server)=>//.
move/eqP in E.
subst n.
move: (Hnin).
Admitted.

Lemma client_nodes n : n \in clients -> n \in nodes.
Proof.
Admitted.

Lemma request_eqP : Equality.axiom request_eq.
Proof.
Admitted.

Lemma l1 d: resource_coh d -> valid (dstate d).
Proof.
Admitted.

Lemma l2 d: resource_coh d -> valid (dsoup d).
Proof.
Admitted.

Lemma l3 d: resource_coh d -> dom (dstate d) =i nodes.
Proof.
Admitted.

Lemma consume_coh d m : ResourceCoh d -> soup_coh (consume_msg (dsoup d) m).
Proof.
move=>C; split=>[|m' msg]; first by apply: consume_valid; rewrite (cohVs C).
case X: (m == m');[move/eqP: X=><-{m'}|].
-
case/(find_mark (cohVs C))=>tms[E]->{msg}.
by case:(C); case=>_/(_ m tms E).
rewrite eq_sym in X.
rewrite (mark_other (cohVs C) X)=>E.
Admitted.

Lemma coh_dom_upd this d s : this \in nodes -> ResourceCoh d -> dom (upd this s (dstate d)) =i nodes.
Proof.
move=>D C z; rewrite -(cohDom C) domU inE/=.
Admitted.

Lemma getLocal_coh n d (C : ResourceCoh d): n \in nodes -> valid (getLocal n d) /\ if n == server then exists (ss : server_state), getLocal n d = st :-> ss else (n \in clients) /\ getLocal n d = Unit.
Proof.
Admitted.

Lemma getLocal_server_st_tp d (C : ResourceCoh d) s: find st (getLocal server d) = Some s -> dyn_tp s = server_state.
Proof.
have pf: server \in nodes by rewrite inE eqxx.
move: (getLocal_coh C pf); rewrite eqxx; move =>[V][s']Z; rewrite Z in V *.
Admitted.

Lemma getSt_server_K d (C : ResourceCoh d) m : getLocal server d = st :-> m -> getSt_server C = m.
Proof.
move=>E; rewrite /getSt_server/=.
have pf: server \in nodes by rewrite inE eqxx.
have V: valid (getLocal server d) by case: (getLocal_coh C pf).
move: (getLocal_server_st_tp C); rewrite !E=>/= H.
Admitted.

Lemma server_send_safe_coh this to d m : server_send_safe this to d m -> coh d.
Proof.
Admitted.

Lemma server_send_this_in this to : HServ this to -> this \in nodes.
Proof.
Admitted.

Lemma server_send_to_in this to : HServ this to -> to \in nodes.
Proof.
Admitted.

Lemma server_send_safe_in this to d m : server_send_safe this to d m -> this \in nodes /\ to \in nodes.
Proof.
Admitted.

Lemma server_step_coh : s_step_coh_t coh the_tag server_step.
Proof.
move=>this to d msg pf h[]->{h}.
have C : (coh d) by case: pf=>?[].
have E: this = server by case: pf=>[][]/eqP.
split=>/=.
-
apply: soup_coh_post_msg; first by case:(server_send_safe_coh pf).
case: (pf)=>H[C']P/=.
by apply: (prec_safe _ P).
-
by apply: coh_dom_upd=>//; case: (server_send_safe_in pf).
-
by rewrite validU; apply: cohVl C.
move=>n Ni.
rewrite /local_coh/=.
rewrite /getLocal/=findU; case: ifP=>B; last by case: C=>_ _ _/(_ n Ni).
move/eqP: B=>Z; subst n this; rewrite eqxx (cohVl C)/=.
split.
by rewrite validPt.
Admitted.

Lemma server_step_def this to d msg : server_send_safe this to d msg <-> exists b pf, @server_step this to d msg pf = Some b.
Proof.
split=>[pf/=|]; last by case=>?[].
rewrite /server_step.
Admitted.

Definition server_send_update_response_prec (ss : server_state) to m := exists e v b e0 v0 outstanding, m = [:: e; v; b] /\ let: r := Update (to, e, v) in r \in outstanding /\ ss = ServerState e0 v0 outstanding /\ b = if e0 <= e then 1 else 0.
Program Definition server_send_update_response_trans : send_trans ResourceCoh := @server_send_trans update_response_tag server_send_update_response_prec _.
Next Obligation.
case: H=>/eqP->H; rewrite /coh_msg eqxx; split=>//=.
case: H0=>[e][v][b][e0][v0][out][]->[U][_]->.
rewrite /msg_from_server /= eqxx.
left.
split=>//.
Admitted.

Definition server_send_read_response_prec (ss : server_state) to m := exists e e0 v0 outstanding, ss = ServerState e0 v0 outstanding /\ let: r := Read (to, e) in r \in outstanding /\ m = if e0 <= e then [:: e; v0 ] else [:: e].
Program Definition server_send_read_response_trans : send_trans ResourceCoh := @server_send_trans read_response_tag server_send_read_response_prec _.
Next Obligation.
case: H=>/eqP->H; rewrite /coh_msg eqxx; split=>//=.
case: H0=>[e][e0][v0][out][_][R]->.
rewrite /msg_from_server /= eqxx.
right.
split=>//.
Admitted.

Lemma rs_step_coh : r_step_coh_t server_recv_wf the_tag rs_step.
Proof.
move=>d from this m C pf tms D F Wf T/=.
rewrite /rs_step; case X: (this == server); last first.
-
split=>/=; first by apply: consume_coh.
+
by apply: coh_dom_upd.
+
by rewrite validU; apply: cohVl C.
by move=>n Ni/=; case: (C)=>_ _ _/(_ n Ni)=>L; rewrite -(getLocalU)// (cohVl C).
split=>/=; first by apply: consume_coh.
-
by apply: coh_dom_upd.
-
by rewrite validU; apply: cohVl C.
move=>n Ni/=; rewrite /local_coh/=.
rewrite /getLocal/=findU; case: ifP=>B/=; last by case: (C)=>_ _ _/(_ n Ni).
move/eqP: B X=>Z/eqP X; subst n this; rewrite eqxx (cohVl C)/=.
split; first by rewrite validPt.
Admitted.

Lemma client_send_this_in this to : HClient this to -> this \in nodes.
Proof.
case=>H _.
Admitted.

Lemma client_send_safe_coh this to d m : client_send_safe this to d m -> coh d.
Proof.
Admitted.

Lemma client_send_to_in this to : HClient this to -> to \in nodes.
Proof.
Admitted.

Lemma soup_coh_post_msg d m: soup_coh (dsoup d) -> coh_msg m -> soup_coh (post_msg (dsoup d) m).1.
Proof.
move=>[H1 H2]Cm; split=>[|i ms/=]; first by rewrite valid_fresh.
rewrite findUnL; last by rewrite valid_fresh.
case: ifP=>E; first by move/H2.
by move/findPt_inv=>[Z G]; subst i m.
