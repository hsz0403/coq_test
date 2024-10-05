Require Export Arith.
Require Export Nat_complements.
Require Export misc.
Require Export Zbase.
Require Export Zle.
Inductive and_set_set_set (S1 S2 : Set) : Set := and_set_set_set_i : S2 -> S1 -> and_set_set_set S1 S2.
Definition and_recZ (p : nat) (P : Z -> Set) := forall n : nat, n <= p -> and_set_set_set (P (pos n)) (P (neg n)).

Lemma Zrec1 : forall P : Z -> Set, (forall n : Z, (forall m : Z, lt_absZ m n -> P m) -> P n) -> P OZ.
intros; apply (H OZ); intros.
unfold lt_absZ in H0; unfold absZ at 2 in H0; elim (lt_OZ m); assumption.
