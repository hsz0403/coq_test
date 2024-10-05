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

Theorem wf_rincl_fin : well_founded rincl_fin.
Proof.
apply wf_chains.
intros l; exists (length M).
intros ? ?; apply rincl_fin_chain_bounded.
