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

Lemma Forall_flat_mapP {X Y: Type} {P: Y -> Prop} {f: X -> list Y} {A: list X}: Forall P (flat_map f A) <-> Forall (fun a => Forall P (f a)) A.
Proof.
elim: A.
-
move=> /=.
by constructor.
-
move=> a A IH.
by rewrite /flat_map -/(flat_map _ _) ? Forall_norm IH.
