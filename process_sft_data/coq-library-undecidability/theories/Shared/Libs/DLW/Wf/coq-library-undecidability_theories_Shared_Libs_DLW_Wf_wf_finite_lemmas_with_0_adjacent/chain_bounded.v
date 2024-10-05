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

Lemma chain_bounded n x y : chain R n x y -> n <= length m.
Proof.
intros H.
destruct (le_lt_dec n (length m)) as [ | C ]; auto.
destruct chain_chain_list with (1 := H) as (ll & H1 & H2).
cut (list_has_dup ll).
+
intros H3.
apply list_has_dup_equiv in H3.
destruct H3 as (z & l & u & r & ->).
apply chain_list_app_inv in H1.
destruct H1 as (a & _ & H1).
apply chain_list_cons_inv in H1.
destruct H1 as (<- & k & H3 & H1).
apply chain_list_app_inv in H1.
destruct H1 as (p & H4 & H1).
apply chain_list_cons_inv in H1.
destruct H1 as (<- & _ & _ & _).
apply chain_list_chain in H4.
destruct (chain_irrefl (S (length u)) z) as [ | [] ]; try discriminate.
constructor 2 with k; auto.
+
apply chain_list_incl in H1.
destruct H1 as [ -> | H1 ].
*
subst; simpl in C; lia.
*
apply finite_php_dup with (2 := H1); lia.
