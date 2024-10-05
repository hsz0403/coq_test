Require Import List.
Import ListNotations.
Require Import Undecidability.CFG.CFP.
Require Import Undecidability.CFG.Util.Facts.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Require Import Undecidability.PCP.Util.PCP_facts.
Require Import Undecidability.Shared.ListAutomation.
Require Import Undecidability.Synthetic.Definitions.
Require Import Setoid Morphisms Arith Lia.
Set Default Proof Using "Type".
Section PCP_CFPI.
Variable P : stack nat.
Definition Sigma := sym P.
Notation "#" := (fresh Sigma).
Definition gamma1 (A : stack nat) := map (fun '(x, y) => (x, (x ++ [#] ++ y ++ [#]))) A.
Definition gamma2 (A : stack nat) := map (fun '(x, y) => (y, (x ++ [#] ++ y ++ [#]))) A.
Fixpoint gamma (A : stack nat) := match A with | [] => [] | (x, y) :: A => gamma A ++ x ++ [#] ++ y ++ [#] end.
End PCP_CFPI.

Lemma sigma_gamma2 A : sigma # (gamma2 A) = tau2 A ++ [#] ++ gamma A.
Proof.
induction A as [ | (x,y) ] ; cbn.
-
reflexivity.
-
unfold gamma2 in IHA.
cbn in *.
rewrite IHA.
now simpl_list.
