Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Stream.SigStream.
Require Import Logic.lib.Stream.SigStream.
Require Import Logic.lib.Stream.StreamFunctions.

Lemma cut_omega_exists {A: Type}: forall (h: stream A) (P: A -> Prop), (exists a, h 0 = Some a /\ P a) -> (exists hs, (forall n, is_fin_stream (hs n)) /\ h = stream_capp hs /\ (forall m n a, hs m (S n) = Some a -> ~ P a) /\ (forall n, exists a, hs n 0 = Some a /\ P a)) \/ (exists hs: list (stream A), (Forall is_fin_stream hs) /\ h = fold_right stream_app empty_stream hs /\ (Forall (fun h0: stream A => forall n a, h0 (S n) = Some a -> ~ P a) hs) /\ (Forall (fun h0: stream A => exists a, h0 0 = Some a /\ P a) hs)).
Proof.
intros.
