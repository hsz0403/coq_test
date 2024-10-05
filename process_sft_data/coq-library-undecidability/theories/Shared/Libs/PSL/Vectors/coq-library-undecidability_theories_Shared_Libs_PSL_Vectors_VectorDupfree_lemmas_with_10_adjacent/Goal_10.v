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

Goal dupfree [| Fin.F1 (n := 1) |].
Proof.
Admitted.

Lemma dupfree_cons (X : Type) (n : nat) (x : X) (xs : Vector.t X n) : dupfree (x ::: xs) -> dupfree xs /\ ~ In x xs.
Proof.
intros H1.
inv H1.
Admitted.

Lemma dupfree_replace (X : Type) (n : nat) (xs : Vector.t X n) (x : X) : dupfree xs -> ~ In x xs -> forall i, dupfree (replace xs i x).
Proof.
revert x.
induction xs; intros; cbn.
-
inv i.
-
dependent destruct i; cbn.
+
constructor; auto.
*
intros H1.
contradict H0.
now econstructor.
*
inv H.
existT_eq'.
assumption.
+
apply dupfree_cons in H as (H&H').
assert (~In x xs).
{
intros H1.
contradict H0.
now constructor.
}
specialize (IHxs x H H1 p).
constructor.
*
intros [ -> | H2] % In_replace.
contradict H0.
constructor.
tauto.
*
Admitted.

Lemma dupfree_tabulate_injective (X : Type) (n : nat) (f : Fin.t n -> X) : (forall x y, f x = f y -> x = y) -> dupfree (tabulate f).
Proof.
intros H.
revert f H.
induction n; intros; cbn.
-
constructor.
-
constructor.
+
intros (x & H2 % H) % in_tabulate.
congruence.
+
eapply IHn.
Admitted.

Lemma dupfree_map_injective (X Y : Type) (n : nat) (f : X -> Y) (V : Vector.t X n) : (forall x y, f x = f y -> x = y) -> dupfree V -> dupfree (map f V).
Proof.
intros HInj.
induction 1.
-
cbn.
constructor.
-
cbn.
constructor; auto.
Admitted.

Lemma tolist_dupfree (X : Type) (n : nat) (xs : Vector.t X n) : dupfree xs -> Dupfree.dupfree xs.
Proof.
induction 1.
-
cbn.
constructor.
-
cbn.
constructor; auto.
intros H1.
contradict H.
Admitted.

Lemma count0_notIn (n : nat) (x : X) (xs : t X n) : count x xs = 0 -> ~ In x xs.
Proof.
revert x.
induction xs; intros; cbn in *.
-
vector_not_in.
-
intros H1.
decide (x=h); try congruence.
apply In_cons in H1 as [-> | H1]; try tauto.
Admitted.

Lemma count0_notIn' (n : nat) (x : X) (xs : t X n) : ~ In x xs -> count x xs = 0.
Proof.
induction xs; intros; cbn in *.
-
reflexivity.
-
decide (x = h) as [ -> | D ].
+
contradict H.
constructor.
+
apply IHxs.
intros H2.
contradict H.
Admitted.

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
Admitted.

Lemma replace_nochange (n : nat) (xs : Vector.t X n) (p : Fin.t n) : replace xs p xs[@p] = xs.
Proof.
eapply eq_nth_iff.
intros ? ? <-.
decide (p = p1) as [ -> | D].
-
now rewrite replace_nth.
-
Admitted.

Goal dupfree [| 4; 8; 15; 16; 23; 42 |].
Proof.
vector_dupfree.
