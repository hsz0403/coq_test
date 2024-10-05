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

Lemma rewt_a0_R x : x <<= Sigma -> rewt P (x ++ [a0]) [a0].
Proof.
induction x using rev_ind.
-
econstructor.
-
econstructor.
replace ((x1 ++ [x]) ++ [a0]) with (x1 ++ ([x] ++ [a0]) ++ []).
econstructor.
cbn.
unfold P.
rewrite !in_app_iff, !in_map_iff.
eauto 9.
now simpl_list.
rewrite app_nil_r.
firstorder.
