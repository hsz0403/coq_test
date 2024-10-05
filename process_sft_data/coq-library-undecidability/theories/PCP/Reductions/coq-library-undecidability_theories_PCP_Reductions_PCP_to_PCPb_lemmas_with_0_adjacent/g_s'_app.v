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

Lemma g_s'_app n x y : g_s' (f_s x ++ y) n = match x with nil => g_s' y n | m :: x => n + m :: x ++ g_s' y 0 end.
Proof.
revert n y.
induction x as [ | m]; intros; cbn in *.
-
reflexivity.
-
revert n; induction m; intros; cbn in *.
+
destruct x.
*
do 2 f_equal.
lia.
*
rewrite IHx.
f_equal.
lia.
+
rewrite IHm.
f_equal.
lia.
