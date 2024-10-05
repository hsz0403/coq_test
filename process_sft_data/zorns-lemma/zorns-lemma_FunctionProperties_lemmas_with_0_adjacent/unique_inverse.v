Require Export Image.
Arguments injective {U} {V}.
Definition surjective {X Y:Type} (f:X->Y) := forall y:Y, exists x:X, f x = y.
Definition bijective {X Y:Type} (f:X->Y) := injective f /\ surjective f.
Inductive invertible {X Y:Type} (f:X->Y) : Prop := | intro_invertible: forall g:Y->X, (forall x:X, g (f x) = x) -> (forall y:Y, f (g y) = y) -> invertible f.
Require Import Description.
Require Import FunctionalExtensionality.
Definition function_inverse {X Y:Type} (f:X->Y) (i:invertible f) : { g:Y->X | (forall x:X, g (f x) = x) /\ (forall y:Y, f (g y) = y) } := (constructive_definite_description _ (unique_inverse f i)).

Lemma unique_inverse: forall {X Y:Type} (f:X->Y), invertible f -> exists! g:Y->X, (forall x:X, g (f x) = x) /\ (forall y:Y, f (g y) = y).
Proof.
intros.
destruct H.
exists g.
red; split.
tauto.
intros.
destruct H1.
extensionality y.
transitivity (g (f (x' y))).
rewrite H2.
reflexivity.
rewrite H.
reflexivity.
