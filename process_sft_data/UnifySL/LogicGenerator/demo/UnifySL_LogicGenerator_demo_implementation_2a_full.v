Require Import ZArith.
Module NaiveLang.
Definition expr := (nat -> Z) -> Prop.
Definition impp (e1 e2 : expr) : expr := fun st => e1 st -> e2 st.
Definition provable (e : expr) : Prop := forall st, e st.
End NaiveLang.