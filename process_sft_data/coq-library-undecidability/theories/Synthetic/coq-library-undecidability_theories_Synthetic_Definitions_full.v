Definition complement {X} (P : X -> Prop) := fun x : X => ~ P x.
Definition reflects (b : bool) (P : Prop) := P <-> b = true.
Definition decider {X} (f : X -> bool) (P : X -> Prop) : Prop := forall x, reflects (f x) (P x).
Definition decidable {X} (P : X -> Prop) : Prop := exists f : X -> bool, decider f P.
Definition enumerator {X} (f : nat -> option X) (P : X -> Prop) : Prop := forall x, P x <-> exists n, f n = Some x.
Definition enumerable {X} (P : X -> Prop) : Prop := exists f : nat -> option X, enumerator f P.
Definition semi_decider {X} (f : X -> nat -> bool) (P : X -> Prop) : Prop := forall x, P x <-> exists n, f x n = true.
Definition semi_decidable {X} (P : X -> Prop) : Prop := exists f : X -> nat -> bool, semi_decider f P.
Definition reduction {X Y} (f : X -> Y) (P : X -> Prop) (Q : Y -> Prop) := forall x, P x <-> Q (f x).
Definition reduces {X Y} (P : X -> Prop) (Q : Y -> Prop) := exists f : X -> Y, reduction f P Q.
Notation "P ⪯ Q" := (reduces P Q) (at level 70).