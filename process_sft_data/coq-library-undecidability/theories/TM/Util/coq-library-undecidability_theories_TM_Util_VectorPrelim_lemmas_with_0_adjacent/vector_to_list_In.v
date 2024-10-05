From Undecidability Require Import TM.Util.TM_facts.
Require Import Lia.
Fixpoint vector_to_list (X : Type) (n : nat) (v : Vector.t X n) : list X := match v with | Vector.nil _ => List.nil | Vector.cons _ x n v' => x :: vector_to_list v' end.

Lemma vector_to_list_In (X : Type) (n : nat) (xs : Vector.t X n) (x : X) : In x (vector_to_list xs) <-> Vector.In x xs.
Proof.
split.
-
induction xs as [ | y n xs IH]; intros; cbn in *.
+
auto.
+
destruct H as [ <- | H].
*
now constructor.
*
now constructor; auto.
-
induction xs as [ | y n xs IH]; intros; cbn in *.
+
inv H.
+
apply In_cons in H as [<- | H].
*
now constructor.
*
now constructor; auto.
