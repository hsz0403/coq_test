Require Import List.
Import ListNotations.
Require Import Undecidability.CFG.CFP.
Require Import Undecidability.CFG.Util.Facts.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Require Import Undecidability.PCP.Util.PCP_facts.
Require Import Undecidability.Shared.ListAutomation.
Require Import Undecidability.Synthetic.Definitions.
Require Import Arith Lia.
Set Default Proof Using "Type".
Section PCP_CFPP.
Variable P : stack nat.
Definition Sigma := sym P.
Notation "#" := (fresh Sigma).
Definition gamma (A : stack nat) := map (fun '(x,y) => (x, rev y)) A.
Definition palin {X} (A : list X) := A = rev A.
End PCP_CFPP.

Lemma gamma_invol A : gamma (gamma A) = A.
Proof.
induction A as [ | (x,y) ]; cbn.
-
reflexivity.
-
simpl_list.
now rewrite <- IHA at 2.
