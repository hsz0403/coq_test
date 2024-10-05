From Undecidability.Shared.Libs.PSL Require Import BasicDefinitions.
From Undecidability.Shared.Libs.PSL Require Import FiniteTypes.FinTypes.
From Undecidability.Shared.Libs.PSL Require Import Vectors.Vectors.
From Undecidability.Shared.Libs.PSL Require Import Vectors.VectorDupfree.
Import VectorNotations2.
From Undecidability.Shared.Libs.PSL Require Import FiniteTypes.Cardinality.
Definition Fin_initVect (n : nat) : Vector.t (Fin.t n) n := tabulate (fun i : Fin.t n => i).
Definition Fin_initVect_nth (n : nat) (k : Fin.t n) : Vector.nth (Fin_initVect n) k = k.
Proof.
unfold Fin_initVect.
apply nth_tabulate.
Import VecToListCoercion.
Instance Fin_finTypeC n : finTypeC (EqType (Fin.t n)).
Proof.
constructor 1 with (enum := Fin_initVect n).
intros x.
cbn in x.
eapply dupfreeCount.
-
eapply tolist_dupfree.
apply Fin_initVect_dupfree.
-
eapply tolist_In.
apply Fin_initVect_full.
Defined.
Hint Extern 4 (finTypeC (EqType (Fin.t _))) => eapply Fin_finTypeC : typeclass_instances.
Fixpoint Vector_pow {X: Type} (A: list X) n {struct n} : list (Vector.t X n) := match n with | 0 => [Vector.nil _] | S n => concat (map (fun a => map (fun v => a:::v) (Vector_pow A n) ) A) end.
Instance Vector_finTypeC (A:finType) n: finTypeC (EqType (Vector.t A n)).
Proof.
exists (undup ((Vector_pow (elem A) n))).
cbn in *.
intros v.
eapply dupfreeCount.
-
eapply dupfree_undup.
-
rewrite undup_id_equi.
induction v; cbn.
+
eauto.
+
eapply in_concat_iff.
eexists; split.
2:eapply in_map_iff.
2:eexists.
2:split.
2:reflexivity.
eapply in_map_iff.
eauto.
eapply elem_spec.
Defined.
Hint Extern 4 (finTypeC (EqType (Vector.t _ _))) => eapply Vector_finTypeC : typeclass_instances.
Instance finTypeC_Prod (F1 F2: finType) : finTypeC (EqType (F1 * F2)).
Proof.
econstructor.
apply prod_enum_ok.
Defined.

Lemma prod_enum_ok (T1 T2: finType) (x: T1 * T2): BasicDefinitions.count (prodLists (elem T1) (elem T2)) x = 1.
Proof.
destruct x as [x y].
rewrite ProdCount.
unfold elem.
now repeat rewrite enum_ok.
