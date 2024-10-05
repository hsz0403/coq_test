Require Export Arith.
Require Export Nat_complements.
Require Export misc.
Require Export Zbase.
Require Export Zle.
Inductive and_set_set_set (S1 S2 : Set) : Set := and_set_set_set_i : S2 -> S1 -> and_set_set_set S1 S2.
Definition and_recZ (p : nat) (P : Z -> Set) := forall n : nat, n <= p -> and_set_set_set (P (pos n)) (P (neg n)).

Lemma lt_OZ : forall m : Z, ~ ltZ (absZ m) OZ.
intros; unfold ltZ in |- *; elim m.
unfold not in |- *; simpl in |- *; intros; exact H.
unfold not in |- *; simpl in |- *; intros; exact H.
unfold not in |- *; simpl in |- *; intros; exact H.
