From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Rely.
From DiSeL Require Import Actions Injection Process Always HoareTriples InferenceRules.
From DiSeL Require Import SeqLib.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Module CalculatorProtocol.
Section CalculatorProtocol.
Definition input := seq nat.
Variable f : input -> option nat.
Variable prec : input -> bool.
Hypothesis prec_valid : forall i, prec i -> exists v, f i = Some v.
Variable cs: seq nid.
Variable cls : seq nid.
Notation nodes := (cs ++ cls).
Hypothesis Huniq : uniq nodes.
Definition st := ptr_nat 1.
Definition perm := (nid * nat * (seq nat))%type.
Definition cstate := seq perm.
Definition all_valid (s : cstate) := all (fun e => prec e.2) s.
Definition localCoh (n : nid) : Pred heap := [Pred h | exists (s : cstate), h = st :-> s /\ all_valid s].
Definition req : nat := 0.
Definition resp : nat := 1.
Definition tags := [:: req; resp].
Definition cohMsg (ms: msg TaggedMessage) : Prop := let body := content ms in if tag body == resp then [/\ from ms \in cs, to ms \in cls & exists v args, tms_cont body = [:: v] ++ args] else [/\ tag body == req, from ms \in cls, to ms \in cs & exists args, tms_cont body = args /\ prec args].
Definition soupCoh : Pred soup := [Pred s | valid s /\ forall m ms, find m s = Some ms -> cohMsg ms].
Definition calcoh d : Prop := let: dl := dstate d in let: ds := dsoup d in [/\ soupCoh ds, dom dl =i nodes, valid dl & forall n, n \in nodes -> localCoh n (getLocal n d)].
Definition CalCoh := CohPred (CohPredMixin l1 l2 l3).
Definition getSt n d (C : CalCoh d) : cstate := match find st (getLocal n d) as f return _ = f -> _ with Some v => fun epf => icast (sym_eq (cohSt C epf)) (dyn_val v) | _ => fun epf => [::] end (erefl _).
Notation coh := CalCoh.
Section ServerReceiveTransition.
Definition sr_wf d (_ : coh d) (this from : nid) msg := prec msg.
Definition sr_step : receive_step_t coh := fun this (from : nid) (m : seq nat) d (pf : coh d) (pt : this \in nodes) => if this \in cs then let s := getSt this pf in st :-> ((from, this, m) :: s) else getLocal this d.
Definition server_recv_trans := ReceiveTrans sr_step_coh.
End ServerReceiveTransition.
Section ServerSendTransition.
Definition entry_finder (to : nid) msg := let: ans := head 0 msg in fun e : perm => let: (n, _, args) := e in [&& n == to, f args == Some ans & msg == ans :: args].
Definition can_send (s : cstate) to msg := has (entry_finder to msg) s.
Definition ss_safe (this to : nid) (d : dstatelet) (msg : seq nat) := to \in cls /\ this \in cs /\ exists (C : coh d), has (entry_finder to msg) (getSt this C).
Definition ss_step (this to : nid) (d : dstatelet) (msg : seq nat) (pf : ss_safe this to d msg) := let C := ss_safe_coh pf in let s := getSt this C in Some (st :-> remove_elem s (to, this, (behead msg))).
Definition server_send_trans := SendTrans ss_safe_coh ss_safe_in ss_safe_def ss_step_coh.
End ServerSendTransition.
Section ClientSendTransition.
Definition cs_safe (this to : nid) (d : dstatelet) (msg : seq nat) := [/\ to \in cs, this \in cls, coh d & prec msg].
Definition cs_step (this to : nid) (d : dstatelet) (msg : seq nat) (pf : cs_safe this to d msg) := let C := cs_safe_coh pf in let s := getSt this C in Some (st :-> ((this, to, msg)::s)).
Definition client_send_trans := SendTrans cs_safe_coh cs_safe_in cs_safe_def cs_step_coh.
End ClientSendTransition.
Section ClientReceiveTransition.
Definition cr_wf d (C : coh d) this from (msg : seq nat) := let s := getSt this C in let: args := (behead msg) in [&& (this, from, args) \in s & size msg > 2].
Definition cr_step : receive_step_t coh := fun this (from : nid) (m : seq nat) d (pf : coh d) (pt : this \in nodes) => let s := getSt this pf : seq perm in st :-> remove_elem s (this, from, (behead m) : seq nat).
Definition client_recv_trans := ReceiveTrans cr_step_coh.
End ClientReceiveTransition.
Section Protocol.
Variable l : Label.
Definition cal_sends := [:: server_send_trans; client_send_trans].
Definition cal_receives := [:: server_recv_trans; client_recv_trans].
Program Definition CalculatorProtocol : protocol := @Protocol _ l _ cal_sends cal_receives _ _.
End Protocol.
End CalculatorProtocol.
Module Exports.
Definition CalculatorProtocol := CalculatorProtocol.
Definition CalCoh := CalCoh.
Definition server_send_trans := server_send_trans.
Definition server_recv_trans := server_recv_trans.
Definition client_send_trans := client_send_trans.
Definition client_recv_trans := client_recv_trans.
Definition req := req.
Definition resp := resp.
Notation input := (seq nat).
Definition cstate := cstate.
Definition getSt := getSt.
Definition getStK := getStK.
Definition getStE := getStE.
Definition getStE' := getStE'.
End Exports.
End CalculatorProtocol.
Export CalculatorProtocol.Exports.

Lemma ss_safe_this this to d m : ss_safe this to d m -> this \in cs.
Proof.
by case=>_[?][].
