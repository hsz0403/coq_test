From Undecidability.Shared.Libs.PSL Require Import Prelim.
From Undecidability.Shared.Libs.PSL Require Import Tactics.Tactics.
From Undecidability.Shared.Libs.PSL Require Import Vectors.Vectors.
From Undecidability.Shared.Libs.PSL Require Import FiniteTypes.FinTypes.
From Undecidability.Shared.Libs.PSL Require Lists.Dupfree.
Require Import Coq.Vectors.Vector.
Open Scope vector_scope.
Import VectorNotations2.
Inductive dupfree X : forall n, Vector.t X n -> Prop := dupfreeVN : dupfree (@Vector.nil X) | dupfreeVC n (x : X) (V : Vector.t X n) : ~ Vector.In x V -> dupfree V -> dupfree (x ::: V).
Ltac vector_dupfree := match goal with | [ |- dupfree (Vector.nil _) ] => constructor | [ |- dupfree (?a ::: ?bs)] => constructor; [vector_not_in | vector_dupfree] end.
Goal dupfree [| 4; 8; 15; 16; 23; 42 |].
Proof.
vector_dupfree.
Goal dupfree [| Fin.F1 (n := 1) |].
Proof.
vector_dupfree.
Import VecToListCoercion.
Section Count.
Variable (X : eqType).
Definition count (n : nat) (x : X) (xs : t X n) := fold_right (fun y c => if Dec (x = y) then S c else c) xs 0.
End Count.

Lemma dupfree_nth_injective (X : Type) (n : nat) (xs : Vector.t X n) : dupfree xs -> forall (i j : Fin.t n), xs[@i] = xs[@j] -> i = j.
Proof.
induction 1; intros; cbn -[nth] in *.
-
inv i.
-
dependent destruct i; dependent destruct j; cbn -[nth] in *; auto.
+
cbn in *.
contradict H.
eapply vect_nth_In; eauto.
+
cbn in *.
contradict H.
eapply vect_nth_In; eauto.
+
f_equal.
now apply IHdupfree.
