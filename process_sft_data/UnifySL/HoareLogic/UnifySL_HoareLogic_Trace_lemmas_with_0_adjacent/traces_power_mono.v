Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Sets.Ensembles.
Require Import Logic.lib.Stream.SigStream.
Require Import Logic.lib.Stream.StreamFunctions.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.HoareLogic.ProgramState.
Definition trace (state: Type): Type := stream (state * MetaState state).
Identity Coercion trace_stream: trace >-> stream.
Definition singleton_trace {state: Type} s ms: trace state := fin_stream ((s, ms) :: nil).
Definition sequential_trace {state: Type} (tr: trace state) : Prop := forall k s ms s' ms', tr k = Some (s, ms) -> tr (S k) = Some (s' , ms') -> ms = Terminating s'.
Definition sound_trace {state: Type} (R: state -> MetaState state -> Prop) (tr: trace state) : Prop := forall k s ms, tr k = Some (s, ms) -> R s ms.
Inductive begin_end_state {state: Type}: state -> trace state -> MetaState state -> Prop := | begin_end_empty: forall s, begin_end_state s empty_stream (Terminating s) | begin_end_fin: forall s ms s' ms' tr n, is_n_stream (S n) tr -> tr 0 = Some (s, ms) -> tr n = Some (s', ms') -> begin_end_state s tr ms' | begin_end_inf: forall s ms tr, is_inf_stream tr -> tr 0 = Some (s, ms) -> begin_end_state s tr NonTerminating.
Definition begin_state {state: Type} (tr: trace state) (s: state): Prop := exists ms, begin_end_state s tr ms.
Definition end_state {state: Type} (tr: trace state) (ms: MetaState state): Prop := exists s, begin_end_state s tr ms.
Definition ctrace2trace {cmd: Type} {state: Type}: trace (cmd * state) -> trace state := stream_map (fun p => match p with ((c, s), mcs) => (s, lift_function snd mcs) end).
Definition traces (state: Type): Type := Ensemble (trace state).
Definition traces_app {state: Type} (d1 d2: traces state): traces state := fun tr => (exists tr1 tr2, d1 tr1 /\ d2 tr2 /\ tr = stream_app tr1 tr2) \/ (exists tr1, d1 tr1 /\ (end_state tr1 NonTerminating \/ end_state tr1 Error) /\ tr = tr1).
Fixpoint traces_power {state: Type} (d: traces state) (n: nat): traces state := match n with | 0 => is_empty_stream | S n => traces_app (traces_power d n) d end.
Definition traces_pstar {state: Type} (d: traces state): traces state := fun tr => exists n, traces_power d n tr.
Definition traces_pomega {state: Type} (d: traces state): traces state := fun tr => exists f, tr = stream_capp f /\ forall n, d (f n).
Module Type FORWARD_TRACE.
Declare Module F: FORWARD.
Parameter forward_trace: forall {state: Type} {state_R: Relation state}, traces state.
Parameter forward_trace_with_test: forall {state: Type} {state_R: Relation state} (P: state -> Prop), traces state.
Axiom singleton_trace_forward: forall {state: Type} {state_R: Relation state} s ms, F.forward (Terminating s) ms -> forward_trace (singleton_trace s ms).
Axiom singleton_trace_forward_test: forall {state: Type} {state_R: Relation state} (P: _ -> Prop) s ms, F.forward (Terminating s) ms -> P s -> forward_trace_with_test P (singleton_trace s ms).
End FORWARD_TRACE.
Module ForwardTrace (F': FORWARD) <: FORWARD_TRACE with Module F := F'.
Module F := F'.
Export F.
Definition forward_trace {state: Type} {state_R: Relation state}: traces state := fun tr => is_fin_stream tr /\ forall n s ms, tr n = Some (s, ms) -> forward (Terminating s) ms.
Definition forward_trace_with_test {state: Type} {state_R: Relation state} (P: state -> Prop) : traces state := fun tr => forward_trace tr /\ exists s, begin_state tr s /\ P s.
End ForwardTrace.
Module Partial := ForwardTrace (ProgramState.Partial).
Module Total := ForwardTrace (ProgramState.Total).

Lemma traces_power_mono {state: Type}: forall (d1 d2: traces state) (n: nat), Included _ d1 d2 -> Included _ (traces_power d1 n) (traces_power d2 n).
Proof.
intros.
induction n.
+
hnf; intros; auto.
+
simpl.
apply traces_app_mono; auto.
