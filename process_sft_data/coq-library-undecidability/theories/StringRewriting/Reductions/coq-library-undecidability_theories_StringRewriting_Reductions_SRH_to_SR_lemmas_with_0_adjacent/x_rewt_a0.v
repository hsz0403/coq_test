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

Lemma x_rewt_a0 x : a0 el x -> x <<= Sigma -> rewt P x [a0].
Proof.
intros (y & z & ->) % in_split ?.
transitivity (y ++ [a0]).
eapply rewt_app_L, rewt_a0_L.
eapply cons_incl.
eapply app_incl_R.
eassumption.
eapply rewt_a0_R.
eapply app_incl_l.
eassumption.
