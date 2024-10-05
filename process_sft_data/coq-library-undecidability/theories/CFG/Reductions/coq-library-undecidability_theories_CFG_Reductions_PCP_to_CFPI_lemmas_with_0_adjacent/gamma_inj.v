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

Lemma gamma_inj A1 A2 : ~ # el sym A1 -> ~ # el sym A2 -> gamma A1 = gamma A2 -> A1 = A2.
Proof.
intros H.
revert A2.
induction A1 as [ | (x,y) ]; cbn; intros.
-
destruct A2; inv H1.
reflexivity.
destruct c, (gamma A2), l; cbn in *; inv H3.
-
destruct A2 as [ | (x',y')]; cbn in H1.
+
destruct (gamma A1), x; inv H1.
+
eapply (f_equal (@rev _)) in H1.
repeat (autorewrite with list in H1; cbn in H1).
inv H1.
eapply list_prefix_inv in H3 as [].
rewrite rev_eq in H1.
subst.
assert (x = x').
*
destruct A1 as [ | (x1, y1)], A2 as [ | (x2, y2)]; repeat (cbn in *; autorewrite with list in H2).
--
rewrite rev_eq in H2.
congruence.
--
exfalso.
enough (~ # el rev x).
eapply H1.
rewrite H2.
cbn.
simpl_list.
cbn.
eauto.
intros ? % In_rev; eauto.
--
exfalso.
enough (~ # el rev x').
eapply H1.
rewrite <- H2.
cbn.
simpl_list.
cbn.
eauto.
intros ? % In_rev; eauto.
--
eapply list_prefix_inv in H2 as [].
rewrite rev_eq in H1.
congruence.
intros ? % In_rev; eauto.
intros ? % In_rev; eauto.
*
subst.
f_equal.
eapply app_inv_head in H2.
rewrite rev_eq in H2.
eapply IHA1 in H2; eauto.
intros ?.
eapply H.
cbn.
eauto.
intros ?.
eapply H0.
cbn.
eauto.
*
intros ? % In_rev.
eapply H.
cbn.
eauto.
*
intros ? % In_rev.
eapply H0.
cbn.
eauto.
