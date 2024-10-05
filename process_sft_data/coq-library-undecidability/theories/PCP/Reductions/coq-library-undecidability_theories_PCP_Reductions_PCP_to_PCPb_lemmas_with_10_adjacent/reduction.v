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

Lemma bitstring_false a : ~ false el to_bitstring a.
Proof.
Admitted.

Lemma f_s_app x y : f_s (x ++ y) = f_s x ++ f_s y.
Proof.
induction x; cbn.
-
reflexivity.
-
rewrite IHx.
Admitted.

Lemma tau1_f A : tau1 (f A) = f_s (tau1 A).
Proof.
induction A as [ | (x,y) ]; cbn.
-
reflexivity.
-
unfold f in IHA.
Admitted.

Lemma tau2_f A : tau2 (f A) = f_s (tau2 A).
Proof.
induction A as [ | (x,y) ]; cbn.
-
reflexivity.
-
unfold f in IHA.
Admitted.

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
Admitted.

Lemma f_g_s'_inv x : g_s (f_s x) = x.
Proof.
unfold g_s.
setoid_rewrite <- app_nil_r at 2.
rewrite g_s'_app.
destruct x; eauto.
cbn.
Admitted.

Lemma tau1_g A B : A <<= f B -> tau1 (g A) = g_s (tau1 A).
Proof.
induction A as [ | (x,y)]; cbn.
-
reflexivity.
-
unfold g in IHA.
intros.
rewrite !IHA.
assert ( (x, y) el map f_c B) as ((x',y') & ? & ?) % in_map_iff by firstorder; inv H0.
rewrite g_s'_app.
destruct x'.
+
cbn.
reflexivity.
+
rewrite f_g_s'_inv.
cbn.
reflexivity.
+
Admitted.

Lemma tau2_g A B : A <<= f B -> tau2 (g A) = g_s (tau2 A).
Proof.
induction A as [ | (x,y)]; cbn.
-
reflexivity.
-
unfold g in IHA.
intros.
rewrite !IHA.
assert ( (x, y) el map f_c B) as ((x',y') & ? & ?) % in_map_iff by firstorder; inv H0.
rewrite g_s'_app.
destruct y'.
+
cbn.
reflexivity.
+
rewrite f_g_s'_inv.
cbn.
reflexivity.
+
Admitted.

Lemma f_subset B A : A <<= B -> f A <<= f B.
Proof.
induction A in B |- *; intros H; cbn.
*
firstorder.
*
intros ? [| H0]; subst.
-
unfold f.
eapply in_map_iff.
exists a.
constructor; eauto.
apply H; simpl; auto.
-
eapply IHA in H0; eauto.
Admitted.

Lemma f_g_subset B A : A <<= f B -> g A <<= B.
Proof.
revert B; induction A; intros B H; cbn.
*
firstorder.
*
assert (a el f B) by firstorder.
unfold f in H0.
eapply in_map_iff in H0 as ((x,y) & ? & ?).
inv H0.
intros ? [|]; subst.
cbn.
now rewrite !f_g_s'_inv.
Admitted.

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
