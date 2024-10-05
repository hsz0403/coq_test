Require Import List Lia.
Import ListNotations.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Require Import Undecidability.Synthetic.Definitions.
Definition to_bitstring (n : nat) : string bool := Nat.iter n (cons true) [].
Fixpoint f_s (x : string nat) : string bool := match x with | nil => nil | a :: x => to_bitstring a ++ [false] ++ f_s x end.
Definition f_c '(x,y) := (f_s x, f_s y).
Definition f (P : stack nat) : stack bool := map f_c P.
Fixpoint g_s' (x : string bool) (n : nat) : string nat := match x with | nil => nil | true :: x' => g_s' x' (S n) | false :: x' => n :: g_s' x' 0 end.
Definition g_s x := g_s' x 0.
Definition g_c '(x,y) := (g_s x, g_s y).
Definition g (P : stack bool) : stack nat := map g_c P.

Lemma f_g_s'_inv x : g_s (f_s x) = x.
Proof.
unfold g_s.
setoid_rewrite <- app_nil_r at 2.
rewrite g_s'_app.
destruct x; eauto.
cbn.
now rewrite app_nil_r.
