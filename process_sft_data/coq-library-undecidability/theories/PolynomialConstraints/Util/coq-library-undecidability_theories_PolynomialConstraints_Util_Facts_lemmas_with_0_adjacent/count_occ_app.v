Require Import List.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma count_occ_app {X : Type} {D : forall x y : X, {x = y} + {x <> y}} {A B c} : count_occ D (A ++ B) c = count_occ D A c + count_occ D B c.
Proof.
elim: A B; first done.
move=> a A IH B /=.
rewrite IH.
by case: (D a c).
