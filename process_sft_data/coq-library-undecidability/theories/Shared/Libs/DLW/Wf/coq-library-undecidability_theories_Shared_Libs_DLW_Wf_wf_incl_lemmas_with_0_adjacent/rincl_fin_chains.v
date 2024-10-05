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

Lemma rincl_fin_chains n m l : chain rincl_fin n m l -> exists ll, ~ list_has_dup ll /\ incl ll M /\ length ll = n /\ incl ll m.
Proof.
induction 1 as [ x | n m k l H1 H2 (ll & H3 & H4 & H5 & H6) ].
+
exists nil.
repeat split; simpl; auto; inversion 1.
+
destruct H1 as (H1 & a & G1 & G2 & G3).
exists (a::ll).
repeat split.
*
contradict H3.
apply list_has_dup_cons_inv in H3.
destruct H3 as [ H3 | ]; auto.
destruct G1; apply H6; auto.
*
apply incl_cons; auto.
*
simpl; f_equal; auto.
*
apply incl_cons; auto.
intros ? ?; auto.
