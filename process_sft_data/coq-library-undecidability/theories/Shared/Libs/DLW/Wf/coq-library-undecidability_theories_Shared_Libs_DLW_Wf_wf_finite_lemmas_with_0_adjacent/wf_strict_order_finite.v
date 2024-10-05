Require Import Arith List Lia.
From Undecidability.Shared.Libs.DLW.Utils Require Import php.
From Undecidability.Shared.Libs.DLW.Wf Require Import wf_chains.
Set Implicit Arguments.
Section wf_strict_order_list.
Variable (X : Type) (R : X -> X -> Prop).
Hypothesis (Rirrefl : forall x, ~ R x x) (Rtrans : forall x y z, R x y -> R y z -> R x z).
Implicit Type l : list X.
Fact chain_trans n x y : chain R n x y -> n = 0 /\ x = y \/ R x y.
Proof.
induction 1 as [ x | n x y z H1 H2 IH2 ]; auto.
destruct IH2 as [ [] | ]; subst; right; auto.
apply Rtrans with (1 := H1); auto.
Variable (m : list X) (Hm : forall x y, R x y -> In x m).
Fact chain_list_incl l x y : chain_list R l x y -> l = nil \/ incl l m.
Proof.
induction 1 as [ x | x l y z H1 H2 IH2 ]; simpl; auto; right.
apply incl_cons.
+
apply Hm with (1 := H1); auto.
+
destruct IH2; auto; subst l; intros _ [].
End wf_strict_order_list.
Section wf_strict_order_finite.
Variable (X : Type) (HX : exists l, forall x : X, In x l) (R : X -> X -> Prop) (Rirrefl : forall x, ~ R x x) (Rtrans : forall x y z, R x y -> R y z -> R x z).
End wf_strict_order_finite.

Theorem wf_strict_order_finite : well_founded R.
Proof.
destruct HX as (m & Hm).
apply wf_strict_order_list with (m := m); auto.
