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
Module LockProtocol.
Section LockProtocol.
Variable server : nid.
Variable clients : seq nid.
Hypothesis Hnin : server \notin clients.
Hypothesis Huniq : uniq clients.
Definition nodes := [:: server] ++ clients.
Notation epoch := nat (only parsing).
Record server_state := ServerState { outstanding : seq nid; current_epoch : epoch; current_holder : option nid }.
Inductive client_state := | NotHeld | Held of epoch.
Definition acquire_tag := 0.
Definition grant_tag := 1.
Definition release_tag := 2.
Definition msg_from_server ms e := (tag ms == grant_tag) && (tms_cont ms == [:: e]).
Definition msg_from_client ms := ((tag ms == acquire_tag) || (tag ms == release_tag)) && (tms_cont ms == [::]).
Definition coh_msg pkt e := if from pkt == server then to pkt \in clients /\ msg_from_server (content pkt) e else if from pkt \in clients then to pkt == server /\ msg_from_client (content pkt) else False.
Definition st := ptr_nat 1.
Definition client_local_coh (cs : client_state) := [Pred h | h = st :-> cs].
Definition server_local_coh (ss : server_state) := [Pred h | h = st :-> ss].
Definition local_coh (n : nid) := [Pred h | valid h /\ if n == server then exists ss, server_local_coh ss h else n \in clients /\ exists cs, client_local_coh cs h].
Definition soup_coh : Pred soup := [Pred s | valid s /\ forall m ms, find m s = Some ms -> active ms -> exists e, coh_msg ms e].
Definition state_coh d := forall n, n \in nodes -> local_coh n (getLocal n d).
Definition lock_coh d := let: dl := dstate d in let: ds := dsoup d in [/\ soup_coh ds , dom dl =i nodes , valid dl & state_coh d].
Definition LockCoh := CohPred (CohPredMixin l1 l2 l3).
Definition server_send_step (ss : server_state) (to : nid) : server_state := if to \in clients then if outstanding ss is _ :: out' then ServerState out' (S (current_epoch ss)) (Some to) else ss else ss.
Definition client_send_step (cs : client_state) : client_state := NotHeld.
Definition server_recv_step (ss : server_state) (from : nid) (mtag : nat) (mbody : seq nat) : server_state := if mtag == acquire_tag then ServerState (rcons (outstanding ss) from) (current_epoch ss) (current_holder ss) else (* mtag == release_tag *) ServerState (outstanding ss) (current_epoch ss) None.
Definition client_recv_step (cs : client_state) (from : nid) (mtag : nat) (mbody : seq nat) : client_state := if mbody is [:: e] then Held e else NotHeld.
Section GetterLemmas.
Definition getSt_server d (C : LockCoh d) : server_state := match find st (getLocal server d) as f return _ = f -> _ with Some v => fun epf => icast (sym_eq (getLocal_server_st_tp C epf)) (dyn_val v) | _ => fun epf => ServerState [::] 0 None end (erefl _).
Program Definition getSt_client c d (C : LockCoh d) (pf : c \in nodes) : client_state.
case X: (c \in clients); last by exact: NotHeld.
exact: (match find st (getLocal c d) as f return _ = f -> _ with Some v => fun epf => icast (sym_eq (getLocal_client_st_tp C X epf)) (dyn_val v) | _ => fun epf => NotHeld end (erefl _)).
Defined.
End GetterLemmas.
Section ServerGenericSendTransitions.
Definition HServ this to := (this == server /\ to \in clients).
Variable the_tag : nat.
Variable prec : server_state -> nid -> seq nid -> Prop.
Hypothesis prec_safe : forall this to s m, HServ this to -> prec s to m -> coh_msg (Msg (TMsg the_tag m) this to true) (current_epoch s).
Notation coh := LockCoh.
Definition server_send_safe (this n : nid) (d : dstatelet) (msg : seq nat) := HServ this n /\ exists (C : coh d), prec (getSt_server C) n msg.
Definition server_step (this to : nid) (d : dstatelet) (msg : seq nat) (pf : server_send_safe this to d msg) := let C := server_send_safe_coh pf in let s := getSt_server C in Some (st :-> server_send_step s to).
Definition server_send_trans := SendTrans server_send_safe_coh server_send_safe_in server_step_def server_step_coh.
End ServerGenericSendTransitions.
Section ServerSendTransitions.
Definition server_send_grant_prec (ss : server_state) to m := exists rest e, ss = ServerState (to :: rest) e None /\ m = [:: e].
Program Definition server_send_grant_trans : send_trans LockCoh := @server_send_trans grant_tag server_send_grant_prec _.
Next Obligation.
case: H=>/eqP->H; rewrite /coh_msg eqxx; split=>//=.
case: H0=>[rest] [e] []-> ->/=.
by rewrite /msg_from_server /= eqxx.
End ServerSendTransitions.
Section ServerGenericReceiveTransitions.
Notation coh := LockCoh.
Variable the_tag : nat.
Variable server_recv_wf : forall d, coh d -> nid -> nid -> TaggedMessage -> bool.
Definition rs_step : receive_step_t coh := fun this (from : nid) (m : seq nat) d (pf : coh d) (pt : this \in nodes) => if (this == server) then let s := getSt_server pf in st :-> server_recv_step s from the_tag m else getLocal this d.
Definition rs_recv_trans := ReceiveTrans rs_step_coh.
End ServerGenericReceiveTransitions.
Section ServerReceiveTransitions.
Definition s_matches_tag (ss : server_state) from t := (t == acquire_tag) || ((t == release_tag) && (current_holder ss == Some from)).
Definition server_msg_wf d (C : LockCoh d) (this from : nid) := [pred m : TaggedMessage | s_matches_tag (getSt_server C) from (tag m)].
Definition server_recv_acquire_trans := rs_recv_trans acquire_tag server_msg_wf.
Definition server_recv_release_trans := rs_recv_trans release_tag server_msg_wf.
End ServerReceiveTransitions.
Section ClientGenericSendTransitions.
Definition HClient this to := (this \in clients /\ to == server).
Variable the_tag : nat.
Variable prec : client_state -> nid -> seq nat -> Prop.
Hypothesis prec_safe : forall this to s m, HClient this to -> prec s to m -> msg_from_client (TMsg the_tag m).
Notation coh := LockCoh.
Definition client_send_safe (this n : nid) (d : dstatelet) (msg : seq nat) := HClient this n /\ exists (HC : HClient this n) (C : coh d), prec (getSt_client C (client_send_this_in HC)) n msg.
Definition client_step (this to : nid) (d : dstatelet) (msg : seq nat) (pf : client_send_safe this to d msg) := let C := client_send_safe_coh pf in let s := getSt_client C (client_send_this_in (proj1 pf)) in Some (st :-> client_send_step s).
Definition client_send_trans := SendTrans client_send_safe_coh client_send_safe_in client_step_def client_step_coh.
End ClientGenericSendTransitions.
Section ClientSendTransitions.
Definition client_send_acquire_prec (cs : client_state) (to : nid) (m : seq nat) := cs = NotHeld /\ m = [::].
Program Definition client_send_acquire_trans : send_trans LockCoh := @client_send_trans acquire_tag client_send_acquire_prec _.
Next Obligation.
apply/andP=>/=.
split=>//.
by case: H0=>_/eqP.
Definition client_send_release_prec (cs : client_state) (to : nid) (m : seq nat) := (exists e, cs = Held e) /\ m = [::].
Program Definition client_send_release_trans : send_trans LockCoh := @client_send_trans release_tag client_send_release_prec _.
Next Obligation.
apply/andP=>/=.
split=>//.
by case: H0=>_/eqP.
End ClientSendTransitions.
Section ClientGenericReceiveTransitions.
Notation coh := LockCoh.
Variable the_tag : nat.
Variable client_recv_wf : forall d, coh d -> nid -> nid -> TaggedMessage -> bool.
Definition rc_step : receive_step_t coh := fun this (from : nid) (m : seq nat) d (pf : coh d) (pt : this \in nodes) => if (this \in clients) then let s := getSt_client pf pt in st :-> client_recv_step s from the_tag m else getLocal this d.
Definition rc_recv_trans := ReceiveTrans rc_step_coh.
End ClientGenericReceiveTransitions.
Section ClientReceiveTransitions.
Definition client_msg_wf d (_ : LockCoh d) (this from : nid) := [pred m : TaggedMessage | true].
Definition client_receive_grant_trans := rc_recv_trans grant_tag client_msg_wf.
End ClientReceiveTransitions.
Section Protocol.
Variable l : Label.
Definition lock_sends := [:: server_send_grant_trans; client_send_acquire_trans; client_send_release_trans ].
Definition lock_receives := [:: server_recv_acquire_trans; server_recv_release_trans; client_receive_grant_trans ].
Program Definition LockProtocol : protocol := @Protocol _ l _ lock_sends lock_receives _ _.
End Protocol.
End LockProtocol.
Module Exports.
Section Exports.
Definition LockProtocol := LockProtocol.
End Exports.
End Exports.
End LockProtocol.
Export LockProtocol.Exports.

Lemma server_send_safe_in this to d m : server_send_safe this to d m -> this \in nodes /\ to \in nodes.
Proof.
by case=>[]=>G _; move/server_send_to_in: (G)->; case: G=>/eqP-> _; rewrite inE eqxx.
