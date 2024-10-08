Set Implicit Arguments.
Require Import List Arith Lia Morphisms Wf.
Import ListNotations.
Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y) := fun x => g (f x).
Notation "f >> g" := (funcomp g f) (at level 50).
Fixpoint it (n: nat) {X: Type} (f: X -> X) (s: X) := match n with | 0 => s | S n => f (it n f s) end.
Instance max_proper: Proper (le ++> le ++> le) max.
Proof.
intros a b ? c d ?; transitivity (max a d); eauto using Nat.max_le_compat_l, Nat.max_le_compat_r.
Instance plus_proper: Proper (le ++> le ++> le) plus.
Proof.
intros a b ? c d ?; transitivity (a + d); eauto using plus_le_compat_l, plus_le_compat_r.
Instance lt_le_subrel: subrelation lt le.
Proof.
intros ?? H; unfold lt in *; transitivity (S x); eauto.
Fixpoint Sum (N: list nat) := match N with | nil => 0 | n :: N => n + Sum N end.
Hint Rewrite Sum_app : listdb.
Definition cast {X: Type} {P: X -> Type} {x y: X} (A: P x) (H: x = y): P y := @eq_rect X x P A y H.

Lemma it_commute n X f (s: X): f (it n f s) = it n f (f s).
Proof.
Admitted.

Instance max_proper: Proper (le ++> le ++> le) max.
Proof.
Admitted.

Instance plus_proper: Proper (le ++> le ++> le) plus.
Proof.
Admitted.

Instance lt_le_subrel: subrelation lt le.
Proof.
Admitted.

Lemma Sum_in x N: In x N -> x <= Sum N.
Proof.
Admitted.

Lemma Sum_app N1 N2: Sum (N1 ++ N2) = Sum N1 + Sum N2.
Proof.
Admitted.

Lemma it_plus n m X f (s: X): it (n + m) f s = it n f (it m f s).
Proof.
induction n; cbn; congruence.
