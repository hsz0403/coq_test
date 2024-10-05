Require Import Undecidability.StringRewriting.SR.
Require Import Undecidability.StringRewriting.Util.Definitions.
Require Import List.
Import ListNotations.
Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Shared.ListAutomation.
Import ListAutomationNotations.
Import RuleNotation.
Set Default Proof Using "Type".
Section SRH_SR.
Local Notation "A <<= B" := (incl A B) (at level 70).
Local Notation symbol := nat.
Local Notation string := (string nat).
Local Notation SRS := (SRS nat).
Variables (R : SRS) (x0 : string) (a0 : symbol).
Notation Sigma := (a0 :: x0 ++ sym R).
Definition P := R ++ map (fun a => [a; a0] / [a0]) Sigma ++ map (fun a => [a0; a] / [a0]) Sigma.
End SRH_SR.

Lemma equi : SRH (R, x0, a0) <-> SR (P, x0, [a0]).
Proof.
split.
-
intros (y & H & Hi).
unfold SR.
transitivity y.
eapply (rewt_subset H).
unfold P.
eapply incl_appl.
eapply incl_refl.
eapply x_rewt_a0.
firstorder.
eapply rewt_sym with (x := x0); eauto.
-
intros H.
unfold SRH, SR in *.
eapply SR_SRH in H; eauto.
