Require Export Arith.
Require Export Nat_complements.
Require Export misc.
Require Export Zbase.
Require Export Zle.
Inductive and_set_set_set (S1 S2 : Set) : Set := and_set_set_set_i : S2 -> S1 -> and_set_set_set S1 S2.
Definition and_recZ (p : nat) (P : Z -> Set) := forall n : nat, n <= p -> and_set_set_set (P (pos n)) (P (neg n)).

Lemma Zrec3 : forall (P : Z -> Set) (p : nat), (forall n : Z, (forall m : Z, lt_absZ m n -> P m) -> P n) -> and_recZ p P -> and_recZ (S p) P.
split.
elim (lt_succ n p H1); intros.
elim (H0 n a); intros; trivial with arith.
rewrite b.
apply (H (neg (S p))).
simple destruct m.
intros; apply (Zrec1 P H).
unfold lt_absZ in |- *; unfold absZ in |- *; unfold ltZ in |- *; unfold leZ in |- *; intros.
elim (H0 n0); auto with arith.
unfold lt_absZ in |- *; unfold absZ in |- *; unfold ltZ in |- *; unfold leZ in |- *; intros.
elim (H0 n0); auto with arith.
elim (lt_succ n p H1); intros.
elim (H0 n); intros; trivial with arith.
rewrite b.
apply (H (pos (S p))).
simple destruct m.
intros; apply (Zrec1 P H).
unfold lt_absZ in |- *; unfold absZ in |- *; unfold ltZ in |- *; unfold leZ in |- *; intros.
elim (H0 n0); auto with arith.
unfold lt_absZ in |- *; unfold absZ in |- *; unfold ltZ in |- *; unfold leZ in |- *; intros.
elim (H0 n0); auto with arith.
