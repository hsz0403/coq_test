Require Import ZArith.
Module NaiveLang.
Definition expr := (nat -> option Z) -> Prop.
Definition context := expr -> Prop.
Definition impp (e1 e2 : expr) : expr := fun st => e1 st -> e2 st.
Definition andp (e1 e2 : expr) : expr := fun st => e1 st /\ e2 st.
Definition orp (e1 e2 : expr) : expr := fun st => e1 st \/ e2 st.
Definition falsep : expr := fun st => False.
Definition join : (nat -> option Z) -> (nat -> option Z) -> (nat -> option Z) -> Prop := fun x y z => forall p: nat, (exists v, x p = Some v /\ y p = None /\ z p = Some v) \/ (exists v, x p = None /\ y p = Some v /\ z p = Some v) \/ (x p = None /\ y p = None /\ z p = None).
Definition sepcon (e1 e2 : expr) : expr := fun st => exists st1 st2, join st1 st2 st /\ e1 st1 /\ e2 st2.
Definition emp : expr := fun st => forall p, st p = None.
Definition provable (e : expr) : Prop := forall st, e st.
End NaiveLang.