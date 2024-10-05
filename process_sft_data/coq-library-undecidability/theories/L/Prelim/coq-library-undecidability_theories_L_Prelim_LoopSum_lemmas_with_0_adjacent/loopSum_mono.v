From Undecidability.L.Prelim Require Import ARS MoreBase.
Definition loopSum {X} {Y} := fix loopSum n (f:X -> X + Y) (x:X) {struct n}:= match n with 0 => None | S n => match f x with | inl x' => loopSum n f x' | inr y => Some y end end.
Arguments loopSum _ _ !_.
Definition loopSum_mono X Y f x y n n': n <= n' -> @loopSum X Y n f x = Some y -> loopSum n' f x = Some y.
Proof.
induction n in n',x|-*;intros H.
now inversion 1.
-
inv H.
easy.
cbn.
destruct _.
2:easy.
apply IHn.
lia.
Definition optionFToSum {X} f (x:X) : X + X := match f x with None => inr x | Some y => inl y end.

Definition loopSum_mono X Y f x y n n': n <= n' -> @loopSum X Y n f x = Some y -> loopSum n' f x = Some y.
Proof.
induction n in n',x|-*;intros H.
now inversion 1.
-
inv H.
easy.
cbn.
destruct _.
2:easy.
apply IHn.
lia.
