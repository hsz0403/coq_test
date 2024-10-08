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
Admitted.

Lemma Zrec1 : forall P : Z -> Set, (forall n : Z, (forall m : Z, lt_absZ m n -> P m) -> P n) -> P OZ.
intros; apply (H OZ); intros.
Admitted.

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
Admitted.

Theorem Zrec4 : forall P : Z -> Set, (forall n : Z, (forall m : Z, lt_absZ m n -> P m) -> P n) -> forall p : nat, and_recZ p P.
intros; elim p.
exact (Zrec2 P H).
Admitted.

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
Admitted.

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
