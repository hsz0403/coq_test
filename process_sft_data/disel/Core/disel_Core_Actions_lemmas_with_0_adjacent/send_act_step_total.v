From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX Protocols Worlds NetworkSem.
Require Classical_Prop.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Actions.
Section Actions.
Variable W : world.
Notation getS s l := (getStatelet s l).
Structure action (V : Type) (this : nid) := Action { (* a_lab : Label; *) (* a_lab_dom : a_lab \in ddom W; *) a_safe : state -> Prop; a_safe_coh : forall s, a_safe s -> s \In Coh W; (* safe_coh : forall s, a_safe s -> coh (getP a_lab) (getS s a_lab); *) a_step : forall s1, (a_safe s1) -> state -> V -> Prop; step_total : forall s (pf : a_safe s), exists s' r, a_step pf s' r; (* step_coh : forall s1 s2 r, Coh W s1 -> *) (* a_safe s1 -> a_step s1 s2 r -> coh (getP a_lab) (getS s2 a_lab); *) (* step_frame : forall s1 s2 r z, *) (* a_lab != z -> Coh W s1 -> *) (* a_safe s1 -> a_step s1 s2 r -> getS s1 z = getS s2 z; *) (* Action step semantics respects the overall network semantics *) step_sem : forall s1 (pf : a_safe s1) s2 r, a_step pf s2 r -> network_step W this s1 s2 }.
End Actions.
Section SkipActionWrapper.
Variable W : world.
Notation getP l := (getProtocol W l).
Notation getS s l := (getStatelet s l).
Variable this : nid.
Variable l : Label.
Variable p : protocol.
Variable pf : getP l = p.
Definition skip_safe s := Coh W s.
Variable V : Type.
Variable f : forall s, coh p (getS s l) -> V.
Definition skip_step s1 (pf : skip_safe s1) (s2 : state) r := [/\ s1 \In Coh W, s1 = s2 & r = f (safe_local pf)].
Definition skip_action_wrapper := Action skip_safe_coh skip_step_total skip_step_sem.
End SkipActionWrapper.
Section TryReceiveActionWrapper.
Variable W : world.
Notation getP l := (getProtocol W l).
Notation getS s l := (getStatelet s l).
Variable this : nid.
Variable filter : Label -> nid -> nat -> pred (seq nat).
Variable f_valid_label : forall l n t m , filter l n t m -> l \in dom (getc W).
Definition tryrecv_act_safe (s : state) := s \In Coh W.
Definition tryrecv_act_step s1 s2 (r : option (nid * nat * seq nat)) := exists (pf : s1 \In Coh W), (* No message to receive -- all relevant messages are marked *) ([/\ (forall l m tms from rt b, this \in nodes (getP l) (getS s1 l) -> Some (Msg tms from this b) = find m (dsoup (getS s1 l)) -> rt \In (rcv_trans (getP l)) -> tag tms = (t_rcv rt) -> (* This is required for safety *) msg_wf rt (coh_s l pf) this from tms -> (* The filter applies *) filter l from (t_rcv rt) (tms_cont tms) -> ~~b), r = None & s2 = s1] \/ (* There is a message to receive and the transition can be executed *) exists l m tms from rt (pf' : this \in nodes (getP l) (getS s1 l)), let: d := getS s1 l in [/\ [/\ Some (Msg tms from this true) = find m (dsoup (getS s1 l)), rt \In (rcv_trans (getP l)), tag tms = (t_rcv rt), (* This is required for safety *) msg_wf rt (coh_s l pf) this from tms & (* The filter applies *) filter l from (t_rcv rt) (tms_cont tms)], let loc' := receive_step rt from tms (coh_s l pf) pf' in let: f' := upd this loc' (dstate d) in let: s' := consume_msg (dsoup d) m in s2 = upd l (DStatelet f' s') s1 & r = Some (from, tag tms, tms_cont tms)]).
Import Classical_Prop.
Definition tryrecv_action_wrapper := Action tryrecv_act_safe_coh tryrecv_act_step_total tryrecv_act_step_sem.
End TryReceiveActionWrapper.
Section SendActionWrapper.
Variable W : world.
Variable p : protocol.
Notation getP l := (getProtocol W l).
Notation getS s l := (getStatelet s l).
Variable this : nid.
Variable l : Label.
Variable pf : (getProtocol W l) = p.
Variable st: send_trans (coh p).
Variable pf' : st \In (snd_trans p).
Variable msg : seq nat.
Variable to : nid.
Definition can_send (s : state) := (l \in dom s) && (this \in nodes p (getS s l)).
Definition filter_hooks (h : hooks) := um_filter (fun e => e.2 == (l, t_snd st)) h.
Definition send_act_safe s := [/\ Coh W s, send_safe st this to (getS s l) msg, can_send s & (* All hooks from a "reduced footprint" are applicable *) all_hooks_fire (filter_hooks (geth W)) l (t_snd st) s this msg to].
Definition send_act_step s1 (S: send_act_safe s1) s2 r := r = msg /\ exists b, Some b = send_step (safe_safe S) /\ let: d := getS s1 l in let: f' := upd this b (dstate d) in let: s' := (post_msg (dsoup d) (Msg (TMsg (t_snd st) msg) this to true)).1 in s2 = upd l (DStatelet f' s') s1.
Definition send_action_wrapper := Action send_act_safe_coh send_act_step_total send_act_step_sem.
End SendActionWrapper.
End Actions.
Module ActionExports.
Definition action := Actions.action.
Definition a_safe := Actions.a_safe.
Definition a_step := Actions.a_step.
Definition a_safe_coh := Actions.a_safe_coh.
Definition a_step_total := Actions.step_total.
Definition a_step_sem := Actions.step_sem.
Definition a_step_other := Actions.step_other.
Definition skip_action_wrapper := Actions.skip_action_wrapper.
Definition send_action_wrapper := Actions.send_action_wrapper.
Definition tryrecv_action_wrapper := Actions.tryrecv_action_wrapper.
End ActionExports.
Export ActionExports.

Lemma send_act_step_total s (S: send_act_safe s): exists s' r , send_act_step S s' r.
Proof.
rewrite /send_act_step/send_act_safe.
case: S=>C S J K.
move/(s_safe_def): (S)=>[b][S']E.
set s2 := let: d := getS s l in let: f' := upd this b (dstate d) in let: s' := (post_msg (dsoup d) (Msg (TMsg (t_snd st) msg) this to true)).1 in upd l (DStatelet f' s') s.
exists s2, msg; split=>//; exists b; split=>//.
move: (safe_safe (And4 C S J K))=> S''.
by rewrite -E (pf_irr S'' S') .
