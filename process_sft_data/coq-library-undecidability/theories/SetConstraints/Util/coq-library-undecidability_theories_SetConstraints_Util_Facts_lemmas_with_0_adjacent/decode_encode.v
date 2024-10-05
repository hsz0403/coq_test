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

Lemma decode_encode {xy: nat * nat} : decode (encode xy) = xy.
Proof.
move Hn: (encode xy) => n.
elim: n xy Hn.
{
by move=> [[|?] [|?]].
}
move=> n IH [x [|y [H]]] /=.
{
move: x => [|x [H]] /=; first done.
by rewrite (IH (0, x)) /= -?H ?PeanoNat.Nat.add_0_r.
}
by rewrite (IH (S x, y)) /= -?H ?PeanoNat.Nat.add_succ_r.
