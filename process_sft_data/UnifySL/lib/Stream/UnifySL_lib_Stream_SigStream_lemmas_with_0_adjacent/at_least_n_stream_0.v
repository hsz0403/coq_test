Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Export Coq.Logic.Classical.
Require Export Coq.Logic.Classical_Prop.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Classes.Equivalence.
Require Export Coq.Classes.Morphisms.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.NatChoice.
Definition stream (A: Type): Type := {h: nat -> option A | forall x y, x < y -> h x = None -> h y = None}.
Definition stream_get {A: Type} (h: stream A) (n: nat) := proj1_sig h n.
Coercion stream_get: stream >-> Funclass.
Tactic Notation "stream_extensionality" ident(x) := match goal with [ |- ?X = ?Y ] => apply stream_extensionality; intro x end.
Definition is_n_stream {A: Type} (n: nat) (h: stream A): Prop := h n = None /\ forall n', n' < n -> h n' <> None.
Definition is_fin_stream {A: Type} (h: stream A): Prop := exists n, h n = None.
Definition is_inf_stream {A: Type} (h: stream A): Prop := forall n, h n <> None.
Definition is_at_least_n_stream {A: Type} (n: nat) (h: stream A): Prop := forall n', n' < n -> h n' <> None.
Definition is_at_most_n_stream {A: Type} (n: nat) (h: stream A): Prop := h n = None.
Definition is_empty_stream {A: Type}: stream A -> Prop := is_n_stream 0.

Lemma at_least_n_stream_0 {A: Type}: forall (h: stream A), is_at_least_n_stream 0 h <-> True.
Proof.
intros.
split; auto.
intros _.
hnf; intros.
omega.
