Require Import List.
Import ListNotations.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Require Import Undecidability.Shared.ListAutomation.
Require Import Undecidability.Synthetic.Definitions.
Set Default Proof Using "Type".
Section derivable_iff_PCPX.
Variable X : Type.
Implicit Type P : stack X.
End derivable_iff_PCPX.

Theorem PCPX_iff_dPCP P : PCPX P <-> dPCP P.
Proof.
split.
-
intros (A & H1 & H2 & H3); exists (tau1 A).
rewrite H3 at 2; apply PCPX_derivable.
exists A; auto.
-
intros (u & Hu).
apply derivable_PCPX in Hu.
destruct Hu as (A & H1 & H2 & H3 & H4).
exists A; subst; auto.
