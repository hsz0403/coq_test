Require Import ZArith.
Require Import Ensembles.
Module NaiveLang.
Definition expr := (nat -> Z) -> Prop.
Definition context := expr -> Prop.
Definition impp (e1 e2 : expr) : expr := fun st => e1 st -> e2 st.
Definition andp (e1 e2 : expr) : expr := fun st => e1 st /\ e2 st.
Definition orp (e1 e2 : expr) : expr := fun st => e1 st \/ e2 st.
Definition falsep : expr := fun st => False.
Definition derivable (Phi: context) (e : expr) : Prop := forall st, (forall e0, Phi e0 -> e0 st) -> e st.
End NaiveLang.