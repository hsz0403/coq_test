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

Lemma count_replace (n : nat) (xs : t X n) (x y : X) (i : Fin.t n) : bool2nat (Dec (x = y)) + count x xs = bool2nat (Dec (x = xs[@i])) + count x (replace xs i y).
Proof.
induction xs; intros; cbn -[nth count] in *.
-
inv i.
-
dependent destruct i; cbn -[nth count] in *.
+
decide (x = y) as [ D | D ]; cbn -[nth count] in *; cbn -[bool2nat dec2bool count].
*
rewrite <- D in *.
decide (x = h) as [ -> | D2]; cbn [dec2bool bool2nat plus]; auto.
cbv [count].
cbn.
rewrite D.
decide (y = y); try tauto.
decide (y = h); congruence.
*
decide (x = h); subst; cbn [bool2nat dec2bool plus]; cbv [count]; try reflexivity.
--
cbn.
decide (h = h); try tauto.
decide (h = y); tauto.
--
cbn.
decide (x = h); try tauto.
decide (x = y); tauto.
+
cbn.
decide (x = y); cbn.
*
decide (x = h); cbn; f_equal.
--
decide (x = xs[@p]); cbn; repeat f_equal; subst.
++
symmetry.
now apply replace_nochange.
++
cbn in *.
specialize (IHxs p).
decide (h = xs[@p]); tauto.
--
decide (x = xs[@p]); cbn; repeat f_equal; subst.
++
symmetry.
now apply replace_nochange.
++
cbn in *.
specialize (IHxs p).
decide (y = xs[@p]); tauto.
*
decide (x = h); cbn; f_equal.
--
decide (x = xs[@p]); cbn; f_equal; subst.
++
cbn in *.
specialize (IHxs p).
decide (xs[@p] = xs[@p]); cbn in *; try tauto.
++
specialize (IHxs p).
cbn in *.
decide (h = xs[@p]); cbn in *; tauto.
--
decide (x = xs[@p]); cbn; auto.
++
specialize (IHxs p).
cbn in *.
decide (x = xs[@p]); cbn in *; tauto.
++
specialize (IHxs p).
cbn in *.
decide (x = xs[@p]); cbn in *; tauto.
