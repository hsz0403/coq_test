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

Corollary sincl_chain_bounded l m n : chain sincl n m l -> n <= length l.
Proof.
intros H.
apply sincl_chain in H.
destruct H as (_ & ll & H1 & H2 & H3 & _).
destruct (le_lt_dec n (length l)) as [ | C ]; auto.
subst; destruct H1.
apply finite_php_dup with l; auto.
