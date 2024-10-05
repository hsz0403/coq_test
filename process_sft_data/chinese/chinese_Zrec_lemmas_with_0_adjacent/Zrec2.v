Require Export Arith.
Require Export Nat_complements.
Require Export misc.
Require Export Zbase.
Require Export Zle.
Inductive and_set_set_set (S1 S2 : Set) : Set := and_set_set_set_i : S2 -> S1 -> and_set_set_set S1 S2.
Definition and_recZ (p : nat) (P : Z -> Set) := forall n : nat, n <= p -> and_set_set_set (P (pos n)) (P (neg n)).

Lemma Zrec2 : forall P : Z -> Set, (forall n : Z, (forall m : Z, lt_absZ m n -> P m) -> P n) -> and_recZ 0 P.
unfold and_recZ in |- *; intros; apply and_set_set_set_i.
elim (le_n_O_eq n H0).
apply (H (neg 0)); intros.
rewrite (tech_lt_abs_OZ m).
apply (Zrec1 P H).
exact H1.
elim (le_n_O_eq n H0).
apply (H (pos 0)); intros.
rewrite (tech_lt_abs_OZ m).
apply (Zrec1 P H).
exact H1.
