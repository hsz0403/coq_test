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

Lemma derivable_PCPX P u v : derivable P u v -> exists A, A <<= P /\ A <> nil /\ tau1 A = u /\ tau2 A = v.
Proof.
induction 1 as [ x y | x y ? ? ? ? (A & ? & ? & ? & ?)].
-
exists [(x,y)]; repeat split; cbn; simpl_list; auto; discriminate.
-
exists ((x,y) :: A); repeat split; simpl; auto; try discriminate; congruence.
