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

Lemma nil_or_ex_max (A : list nat) : A = [] \/ exists a, In a A /\ Forall (fun b => a >= b) A.
Proof.
elim: A; first by left.
move=> a A [-> | [b [? Hb]]]; right.
-
exists a.
constructor; by [left | constructor].
-
case: (le_lt_dec a b)=> ?.
+
exists b.
constructor; by [right | constructor].
+
exists a.
constructor; first by left.
constructor; first done.
apply: Forall_impl Hb.
by lia.
