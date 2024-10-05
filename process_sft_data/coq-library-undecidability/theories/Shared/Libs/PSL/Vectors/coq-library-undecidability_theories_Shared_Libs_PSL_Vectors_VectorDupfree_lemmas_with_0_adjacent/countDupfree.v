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

Lemma countDupfree (n : nat) (xs : t X n) : (forall x : X, In x xs -> count x xs = 1) <-> dupfree xs.
Proof.
split; intros H.
{
induction xs; cbn -[count] in *.
-
constructor.
-
constructor.
+
intros H2.
specialize (H h ltac:(now constructor)).
cbn in H.
decide (h = h); try tauto.
inv H.
contradict H2.
now eapply count0_notIn.
+
apply IHxs.
intros x Hx.
specialize (H x ltac:(now constructor)).
cbn in H.
decide (x = h); inv H; auto.
rewrite H1.
contradict Hx.
now eapply count0_notIn.
}
{
induction H as [ | n x' xs HIn HDup IH ]; intros; cbn in *.
-
inv H.
-
decide (x = x') as [ -> | D].
+
f_equal.
exact (count0_notIn' HIn).
+
apply (IH x).
now apply In_cons in H as [ -> | H].
}
