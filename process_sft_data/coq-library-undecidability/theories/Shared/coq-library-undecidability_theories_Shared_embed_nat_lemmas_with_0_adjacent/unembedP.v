Require Import PeanoNat.
Definition embed '(x, y) : nat := y + (nat_rec _ 0 (fun i m => (S i) + m) (y + x)).
Definition unembed (n : nat) : nat * nat := nat_rec _ (0, 0) (fun _ '(x, y) => match x with S x => (x, S y) | _ => (S y, 0) end) n.
Arguments embed : simpl never.
Module EmbedNatNotations.
Notation "⟨ a , b ⟩" := (embed (a, b)) (at level 0).
End EmbedNatNotations.

Lemma unembedP {n: nat} : embed (unembed n) = n.
Proof.
induction n as [|n IH]; [reflexivity|].
simpl.
revert IH.
case (unembed n).
intros x y.
case x as [|x]; intro Hx; rewrite <- Hx; simpl.
rewrite Nat.add_0_r.
reflexivity.
rewrite ?Nat.add_succ_r.
simpl.
rewrite ?Nat.add_succ_r.
reflexivity.
