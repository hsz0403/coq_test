Require Import Arith List Wellfounded.
From Undecidability.Shared.Libs.DLW.Utils Require Import php.
From Undecidability.Shared.Libs.DLW.Wf Require Import acc_irr measure_ind wf_chains.
Set Implicit Arguments.
Section sincl.
Variable (X : Type).
Implicit Type (l m : list X).
Definition sincl l m := incl l m /\ exists x, ~ In x l /\ In x m.
End sincl.
Arguments wf_sincl {X}.
Section rincl_fin.
Variable (X : Type) (M : list X).
Definition rincl_fin l m := (forall x, In x m -> In x M -> In x l) /\ exists x, ~ In x m /\ In x l /\ In x M.
End rincl_fin.
Arguments wf_rincl_fin {X}.

Lemma sincl_chain n m l : chain sincl n m l -> incl m l /\ exists ll, ~ list_has_dup ll /\ length ll = n /\ incl ll l /\ forall x, In x m -> In x ll -> False.
Proof.
induction 1 as [ m | n m l k H1 H2 (H7 & ll & H3 & H4 & H5 & H6) ].
+
split.
*
intros ?; auto.
*
exists nil; simpl; repeat split; auto.
-
inversion 1.
-
intros _ [].
+
split.
*
intros ? ?; apply H7, H1; auto.
*
destruct H1 as (G1 & x & G2 & G3).
exists (x::ll); simpl; repeat split; auto.
-
contradict H3.
apply list_has_dup_cons_inv in H3.
destruct H3 as [ H3 | ]; auto.
destruct (H6 x); auto.
-
apply incl_cons; auto.
-
intros y F1 [ F2 | F2 ]; subst.
**
tauto.
**
apply (H6 y); auto.
