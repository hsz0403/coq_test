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

Lemma rewt_a0_L x : x <<= Sigma -> rewt P (a0 :: x) [a0].
Proof.
intros.
induction x.
-
reflexivity.
-
econstructor.
replace (a0 :: a :: x) with ([] ++ [a0;a] ++ x) by now simpl_list.
econstructor.
unfold P.
rewrite !in_app_iff, !in_map_iff.
eauto 9.
firstorder.
