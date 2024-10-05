Require Import ssreflect ssrbool ssrfun.
Require Import Arith Psatz.
Require Import List.
Import ListNotations.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Definition Forall_norm := (@Forall_app_iff, @Forall_singleton_iff, @Forall_cons_iff, @Forall_nil_iff).
Module NatNat.
Definition encode '(x, y) : nat := y + (nat_rec _ 0 (fun i m => (S i) + m) (y + x)).
Definition decode (n : nat) : nat * nat := nat_rec _ (0, 0) (fun _ '(x, y) => if x is S x then (x, S y) else (S y, 0)) n.
End NatNat.

Lemma count_occ_app {X : Type} {D : forall x y : X, {x = y} + {x <> y}} {A B c}: count_occ D (A ++ B) c = count_occ D A c + count_occ D B c.
Proof.
elim: A B; first done.
move=> a A IH B /=.
rewrite IH.
by case: (D a c).
