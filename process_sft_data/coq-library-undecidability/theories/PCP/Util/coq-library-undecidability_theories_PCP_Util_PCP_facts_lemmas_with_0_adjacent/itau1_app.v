Require Import List.
Import ListNotations.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Set Implicit Arguments.
Unset Strict Implicit.
Definition cards {X : Type} (x: list X) := map (fun a => ([a], [a])) x.
Definition card_eq : forall x y : card bool, {x = y} + {x <> y}.
Proof.
intros.
repeat decide equality.
Defined.
Hint Rewrite (@tau1_app nat) (@tau2_app nat) (@tau1_cards nat) (@tau2_cards nat) : list.
Implicit Types a b : nat.
Implicit Types x y z : string nat.
Implicit Types d e : card nat.
Implicit Types A R P : stack nat.
Fixpoint sym (R : stack nat) := match R with [] => [] | (x, y) :: R => x ++ y ++ sym R end.
Hint Resolve sym_word_l sym_word_R : core.
Coercion sing (n : nat) := [n].
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts.
From Undecidability Require Export PCP.PCP.
From Undecidability.Shared Require Export ListAutomation.
Import ListAutomationNotations.
Local Definition BSRS := list (card bool).
Local Notation "x / y" := (x, y).
Fixpoint L_PCP n : list (BSRS * (string bool * string bool)) := match n with | 0 => [] | S n => L_PCP n ++ [ (C, (x, y)) | (C, x, y) ∈ (L_T BSRS n × L_T (string bool) n × L_T (string bool) n), (x/y) el C ] ++ [ (C, (x ++ u, y ++ v)) | ( (C, (u,v)), x, y) ∈ (L_PCP n × L_T (string bool) n × L_T (string bool) n), (x,y) el C ] end.

Lemma itau1_app {X : Type} {P : stack X} A B : itau1 P (A++B) = itau1 P A ++ itau1 P B.
Proof.
induction A; simpl; auto; rewrite app_ass; simpl; f_equal; auto.
