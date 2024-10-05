Require Import List Arith Lia Permutation.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_list.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.Shared.Libs.DLW.Wf Require Import measure_ind.
Set Implicit Arguments.
Section fp_quotient.
Variable (X : Type).
Implicit Type (R : X -> X -> Prop).
Record fp_quotient R := Mk_finite_partial_quotient { fpq_size : nat; fpq_class : X -> option (pos fpq_size); fpq_repr : pos fpq_size -> X; fpq_eq : forall c, fpq_class (fpq_repr c) = Some c; fpq_None : forall x, ~ R x x <-> fpq_class x = None; fpq_Some : forall x y, R x y <-> fpq_class x = fpq_class y /\ fpq_class x <> None; }.
Let per R := (forall x y, R x y -> R y x) /\ (forall x y z, R x y -> R y z -> R x z).
Let dec R := forall x y, { R x y } + { ~ R x y }.
Let Some_inj K (x y : K) : Some x = Some y -> x = y.
Proof.
inversion 1; auto.
Record fin_quotient R := Mk_finite_quotient { fq_size : nat; fq_class : X -> pos fq_size; fq_repr : pos fq_size -> X; fq_surj : forall c, fq_class (fq_repr c) = c; fq_equiv : forall x y, R x y <-> fq_class x = fq_class y }.
End fp_quotient.

Let Some_inj K (x y : K) : Some x = Some y -> x = y.
Proof.
inversion 1; auto.
