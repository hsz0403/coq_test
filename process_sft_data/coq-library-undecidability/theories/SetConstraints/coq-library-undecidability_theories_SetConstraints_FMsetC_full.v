Require Import PeanoNat List.
Import ListNotations.
Definition mset_eq (A B: list nat) : Prop := forall c, count_occ Nat.eq_dec A c = count_occ Nat.eq_dec B c.
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).
Inductive msetc : Set := | msetc_zero : nat -> msetc | msetc_sum : nat -> nat -> nat -> msetc | msetc_h : nat -> nat -> msetc.
Definition msetc_sem (φ: nat -> list nat) (c: msetc) := match c with | msetc_zero x => φ x ≡ [0] | msetc_sum x y z => φ x ≡ (φ y) ++ (φ z) | msetc_h x y => φ x ≡ map S (φ y) end.
Definition FMsetC_SAT (l : list msetc) := exists φ, forall c, In c l -> msetc_sem φ c.