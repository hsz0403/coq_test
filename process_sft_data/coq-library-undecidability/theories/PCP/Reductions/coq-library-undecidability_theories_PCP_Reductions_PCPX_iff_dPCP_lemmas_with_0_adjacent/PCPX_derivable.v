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

Lemma PCPX_derivable P u v : (exists A, A <<= P /\ A <> nil /\ tau1 A = u /\ tau2 A = v) -> derivable P u v.
Proof.
intros (A & H1 & H2 & <- & <-).
revert H1; pattern A; revert A H2.
eapply list_ind_ne; cbn; intros (x,y) H.
-
simpl_list; constructor 1; auto.
-
constructor 2; eauto.
