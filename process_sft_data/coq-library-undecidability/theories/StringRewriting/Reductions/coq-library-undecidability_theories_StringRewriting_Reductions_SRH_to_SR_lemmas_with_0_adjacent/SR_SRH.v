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

Lemma SR_SRH x : x <<= Sigma -> rewt P x [a0] -> exists y, rewt R x y /\ a0 el y.
Proof.
intros.
pattern x; refine (rewt_induct _ _ H0).
+
exists [a0].
split.
reflexivity.
eauto.
+
clear H H0.
intros.
inv H.
destruct H1 as [y []].
unfold P in H2.
eapply in_app_iff in H2 as [ | [ (? & ? & ?) % in_map_iff | (? & ? & ?) % in_map_iff ] % in_app_iff].
*
exists y.
eauto using rewS, rewB, rewR.
*
inv H2.
eauto 9 using rewS, rewB, rewR.
*
inv H2.
eauto 9 using rewS, rewB, rewR.
