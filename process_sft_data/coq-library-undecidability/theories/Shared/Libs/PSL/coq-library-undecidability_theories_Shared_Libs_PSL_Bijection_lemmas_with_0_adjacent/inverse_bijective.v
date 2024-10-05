From Undecidability.Shared.Libs.PSL Require Import Base.
Section Bijection.
Variable X Y : Type.
Definition left_inverse (f : X -> Y) (g : Y -> X) := forall x : X, g (f x) = x.
Definition right_inverse (f : X -> Y) (g : Y -> X) := forall y : Y, f (g y) = y.
Definition inverse (f : X -> Y) (g : Y -> X) := left_inverse f g /\ right_inverse f g.
Definition injective (f : X -> Y) := forall x y, f x = f y -> x = y.
Definition surjective (f : X -> Y) := forall y, exists x, f x = y.
Definition bijective (f : X -> Y) := injective f /\ surjective f.
End Bijection.

Lemma inverse_bijective f g : inverse f g -> bijective f.
Proof.
intros (HInv1&HInv2).
hnf.
split.
-
eapply left_inv_inj; eauto.
-
eapply right_inv_surjective; eauto.
