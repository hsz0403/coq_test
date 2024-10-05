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

Theorem reduction : PCP ⪯ PCPb.
Proof.
exists f.
intros B.
split.
-
intros (A & HP & He & H).
exists (f A).
repeat split.
+
now eapply f_subset.
+
destruct A; cbn; congruence.
+
unfold f, f_c, f_s.
setoid_rewrite tau1_f.
setoid_rewrite tau2_f.
now rewrite H.
-
intros (A & HP & He & H).
exists (g A).
repeat split.
+
eapply f_g_subset; eauto.
+
destruct A; cbn; congruence.
+
erewrite tau1_g, tau2_g, H; eauto.
