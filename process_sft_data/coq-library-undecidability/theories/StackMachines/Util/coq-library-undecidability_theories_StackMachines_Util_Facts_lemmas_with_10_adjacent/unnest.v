Require Import Lia.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Arguments measure_ind {X}.
Arguments measure_rect {X}.

Lemma measure_ind {X : Type} (f : X -> nat) (P : X -> Prop) : (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
apply : well_founded_ind.
apply : Wf_nat.well_founded_lt_compat.
move => *.
Admitted.

Lemma measure_rect {X : Type} (f : X -> nat) (P : X -> Type) : (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
apply : well_founded_induction_type.
apply : Wf_nat.well_founded_lt_compat.
move => *.
Admitted.

Lemma copy {A : Prop} : A -> A * A.
Proof.
Admitted.

Lemma unnest (X Y Z: Type): X -> (Y -> Z) -> (X -> Y) -> Z.
Proof.
by auto.
