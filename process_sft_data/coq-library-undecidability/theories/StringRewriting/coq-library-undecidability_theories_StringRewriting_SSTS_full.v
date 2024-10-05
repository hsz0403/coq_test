Require Import List Relation_Operators.
Definition Ssts := list ((nat * nat) * (nat * nat)).
Inductive step (ssts: Ssts) : list nat -> list nat -> Prop := | step_intro {u v: list nat} {a b c d: nat} : In ((a, b), (c, d)) ssts -> step ssts (u ++ a :: b :: v) (u ++ c :: d :: v).
Definition multi_step (ssts: Ssts) : list nat -> list nat -> Prop := clos_refl_trans (list nat) (step ssts).
Definition SSTS01 : Ssts -> Prop := fun ssts => exists n, multi_step ssts (repeat 0 (1+n)) (repeat 1 (1+n)).