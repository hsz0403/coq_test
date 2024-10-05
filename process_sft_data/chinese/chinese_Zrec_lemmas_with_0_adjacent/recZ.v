Require Export Arith.
Require Export Nat_complements.
Require Export misc.
Require Export Zbase.
Require Export Zle.
Inductive and_set_set_set (S1 S2 : Set) : Set := and_set_set_set_i : S2 -> S1 -> and_set_set_set S1 S2.
Definition and_recZ (p : nat) (P : Z -> Set) := forall n : nat, n <= p -> and_set_set_set (P (pos n)) (P (neg n)).

Theorem recZ : forall P : Z -> Set, (forall n : Z, (forall m : Z, lt_absZ m n -> P m) -> P n) -> forall p : Z, P p.
intros; elim p.
exact (Zrec1 P H).
intro n; cut (and_recZ n P).
intros.
elim (H0 n); auto with arith.
apply Zrec4; trivial with arith.
intro n; cut (and_recZ n P).
intros.
elim (H0 n); auto with arith.
apply Zrec4; trivial with arith.
