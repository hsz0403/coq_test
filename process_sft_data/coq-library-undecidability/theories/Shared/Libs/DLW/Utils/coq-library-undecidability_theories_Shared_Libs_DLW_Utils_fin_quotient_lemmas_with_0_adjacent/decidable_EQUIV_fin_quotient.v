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

Theorem decidable_EQUIV_fin_quotient l R : (forall x, R x x) -> (forall x y, R x y -> R y x) -> (forall x y z, R x y -> R y z -> R x z) (* R is an equivalence *) -> (forall x y, { R x y } + { ~ R x y }) (* R is decidable *) -> (forall x : X, exists y, In y l /\ R x y) (* finitely many classes *) -> fin_quotient R.
Proof.
intros H1 H2 H3 H4 H5.
destruct (@decibable_PER_fp_quotient l R) as [ n cl rp Q1 Q2 Q3 ]; simpl; auto.
+
intros x; split; auto; intros _; exists x; auto.
+
split; auto.
+
assert (forall x, { y | cl x = Some y }) as H.
{
intros x; case_eq (cl x).
*
intros p; exists p; auto.
*
intros C; exfalso.
apply Q2 in C.
apply C; auto.
}
set (cl' x := proj1_sig (H x)).
assert (H' : forall x, cl x = Some (cl' x)).
{
intros x; apply (proj2_sig (H x)).
}
generalize cl' H'; clear H cl' H'; intros cl' H.
exists n cl' rp.
*
intro x.
generalize (Q1 x); rewrite H.
injection 1; auto.
*
intros x y; rewrite Q3.
split.
-
intros (C1 & _).
apply Some_inj; rewrite <- H, <- H; auto.
-
intros E; rewrite H, H, E; split; auto; discriminate.
