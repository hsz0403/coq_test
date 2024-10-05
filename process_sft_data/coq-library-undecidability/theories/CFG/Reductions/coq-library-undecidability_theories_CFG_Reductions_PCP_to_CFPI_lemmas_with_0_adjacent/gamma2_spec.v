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

Lemma gamma2_spec B C : B <<= gamma2 C -> exists A, A <<= C /\ gamma2 A = B.
Proof.
induction B as [ | (x,y)]; cbn; intros.
-
eauto.
-
assert ((x, y) el gamma2 C) by firstorder.
unfold gamma2 in H0.
eapply in_map_iff in H0 as ((x',y') & ? & ?).
inv H0.
assert (B <<= gamma2 C) as (A & Hi & He) % IHB by firstorder.
exists ((x', x) :: A).
split.
+
intuition.
+
now subst.
