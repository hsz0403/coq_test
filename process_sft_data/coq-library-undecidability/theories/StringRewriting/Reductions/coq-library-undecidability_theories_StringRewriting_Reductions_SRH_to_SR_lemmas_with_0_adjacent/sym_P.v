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

Lemma sym_P : sym P <<= Sigma.
Proof.
unfold P.
rewrite !sym_app.
eapply incl_app; [ | eapply incl_app].
-
eauto.
-
eapply sym_map.
cbn.
intros ? [-> | [ | ] % in_app_iff] ? [ | [ | ]]; subst; eauto.
inv H.
eauto.
inv H0.
inv H0.
eauto.
eauto.
inv H0.
eauto.
inv H1.
-
eapply sym_map.
cbn.
intros ? [-> | [ | ] % in_app_iff] ? [ | [ | ]]; subst; eauto.
inv H.
eauto.
inv H0.
inv H0.
eauto.
eauto.
inv H0.
eauto.
inv H1.
