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

Lemma reductionRL (X : Type) : @dPCP X ⪯ @PCPX X.
Proof.
exists id; intro; now rewrite PCPX_iff_dPCP.
