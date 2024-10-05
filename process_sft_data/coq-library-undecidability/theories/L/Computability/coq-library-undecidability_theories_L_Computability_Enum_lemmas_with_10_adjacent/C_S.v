From Undecidability.L Require Import Util.L_facts.
Import L_Notations.
Notation "A '.[' i ']'" := (elAt A i) (no associativity, at level 50).
Fixpoint appCross A B := match A with | nil => nil | a :: A => map (app a) B ++ appCross A B end.
Fixpoint T n := match n with | 0 => [#n] | S n => let A := T n in A ++ [#(S n)] ++ filter (fun x => Dec (~ x el A)) ( map lam A ++ appCross A A ) end.
Fixpoint exh_size s := match s with | #n => n | app s1 s2 => 1 + exh_size s1 + exh_size s2 | lam s => 1 + exh_size s end.
Definition g s := match pos s (T (exh_size s)) with None => 0 | Some n => n end.
Definition g_inv n := match elAt (T n) n with None => #0 | Some n => n end.
Hint Unfold left_inverse injective right_inverse surjective : core.
Hint Unfold left_inverse injective surjective g g_inv : core.
Fixpoint C (n : nat) := match n with | 0 => [(0,0)] | S n => C n ++ (S n, 0) :: filter (fun x => Dec (not (x el C n))) (map (fun p : nat * nat => let (p1,p2) := p in (p1,S p2)) (C n)) end.
Definition eSize (p : nat * nat) := let (n,m) := p in 1 + n + m.
Definition c n : nat * nat := match elAt (C n) n with None => (0,0) | Some p => p end.
Definition c_inv p : nat := match pos p (C (eSize p)) with None => 0 | Some p => p end.

Lemma disjoint_symm X (A B : list X) : disjoint A B <-> disjoint B A.
Proof.
Admitted.

Lemma map_lam A : forall x, x el map lam A -> exists t, x = lam t.
Proof.
Admitted.

Lemma appCross_app A B : forall x, x el appCross A B -> exists s t, x = app s t.
Proof.
induction A.
-
inversion 1.
-
simpl; intros.
rewrite in_app_iff in H.
destruct H; eauto.
rewrite in_map_iff in H.
Admitted.

Lemma T_var_not n m : m > n -> ~ #m el T n.
Proof.
induction n.
-
destruct m; destruct 2; try lia.
congruence.
auto.
-
simpl; intros A; rewrite !in_app_iff.
intros [H | H].
+
eapply IHn; now try lia.
+
destruct H as [H | H].
inv H; lia.
rewrite filter_app in H.
rewrite in_app_iff in H.
destruct H as [H | H]; rewrite in_filter_iff in H; destruct H as [H1 H2].
*
rewrite in_map_iff in H1.
destruct H1 as [x [H1 _]].
inv H1.
*
Admitted.

Lemma appCross_dupfree A B : dupfree A -> dupfree B -> dupfree (appCross A B).
Proof with eauto using dupfree; intuition.
induction 1; intros dpf_B; simpl...
eapply dupfree_app...
-
eapply disjoint_forall.
intros y D Hy.
edestruct (appCross_app Hy) as [y1 [y2 Hyy]]; subst.
eapply appCross_correct in Hy as [].
eapply in_map_iff in D.
destruct D as [d [D1 D2]].
inv D1...
-
eapply dupfree_map...
Admitted.

Lemma dupfree_T : forall n, dupfree (T n).
Proof.
induction n.
-
simpl.
repeat econstructor.
eauto.
-
simpl.
eapply dupfree_app.
+
eapply disjoint_symm, disjoint_cons.
split.
*
eapply T_var_not; lia.
*
rewrite filter_app, disjoint_symm, disjoint_forall.
intros s A B.
eapply in_app_iff in B.
destruct B; eapply in_filter_iff in H;rewrite Dec_reflect in *;tauto.
+
eassumption.
+
eapply dupfreeC.
rewrite in_filter_iff.
intros [A _].
rewrite in_app_iff in A.
destruct A.
eapply map_lam in H.
destruct H; inv H.
eapply appCross_app in H.
destruct H as [s [t H]].
inv H.
eapply dupfree_filter.
eapply dupfree_app.
rewrite disjoint_forall.
intros x A B.
destruct (map_lam A), (appCross_app B) as [x1 [x2 B1]].
subst.
inv B1.
eapply dupfree_map; congruence.
Admitted.

Lemma T_dup n1 n2 m1 m2 x : T n1 .[m1 ] = Some x -> T n2 .[m2] = Some x -> m1 = m2.
Proof.
Admitted.

Lemma g_g_inv n : g(g_inv n) = n.
Proof.
unfold g_inv.
destruct (T n .[ n ] ) eqn:B.
unfold g.
destruct( pos t (T (exh_size t)) ) eqn:A.
-
eapply pos_elAt, T_dup in A; eauto.
-
assert (HIn : t el T (exh_size t)) by eapply T_exhaustive.
eapply el_elAt in HIn.
destruct HIn.
eapply elAt_el in H.
eapply el_pos in H.
destruct H.
rewrite H in A.
congruence.
-
eapply nth_error_none in B.
assert (|T n| > n) by eapply T_longenough.
Admitted.

Lemma g_T : bijective g.
Proof.
split.
-
eauto using left_inv_inj, g_inv_g.
-
Admitted.

Lemma sublist_C : forall n : nat, exists x B, C (S n) = C n ++ x :: B.
Proof.
Admitted.

Lemma C_ge p n1 n2 m : n2 >= n1 -> C n1 .[ m ] = Some p -> C n2 .[ m ] = Some p.
Proof.
remember (S n1) as n1'.
Admitted.

Lemma C_exhaustive p : p el C( eSize p ).
Proof.
destruct p as [n m].
induction m.
-
simpl.
rewrite plus_0_r.
destruct n; simpl; auto.
-
simpl.
decide ( (n,S m) el C (n + S m) ).
+
auto.
+
eapply in_app_iff.
right.
right.
eapply in_filter_iff.
split.
*
eapply in_map_iff.
exists (n, m).
split.
reflexivity.
assert (n + S m = 1 + n + m) by lia.
rewrite H.
eassumption.
*
rewrite Dec_reflect.
Admitted.

Lemma C_longenough n : |C n| > n.
Proof.
induction n; simpl.
-
lia.
-
rewrite app_length.
simpl.
Admitted.

Lemma c_c_inv p : c (c_inv p) = p.
Proof.
unfold c_inv.
destruct( pos p (C (eSize p)) ) eqn:A.
unfold c.
destruct (elAt (C n) n ) eqn:B.
-
eapply pos_elAt in A.
destruct (lt_eq_lt_dec n (eSize p)) as [[D | D] | D].
+
eapply C_ge in B.
rewrite B in A.
now inv A.
lia.
+
subst.
cut (Some p = Some p0); try congruence.
now rewrite <- A, <- B.
+
eapply C_ge in A.
rewrite A in B.
now inv B.
lia.
-
eapply nth_error_none in B.
assert (|C n| > n) by eapply C_longenough.
lia.
-
assert (HIn : p el C (eSize p)) by eapply C_exhaustive.
eapply el_elAt in HIn.
destruct HIn.
eapply elAt_el in H.
eapply el_pos in H.
destruct H.
rewrite H in *.
Admitted.

Lemma c_surj : surjective c.
Proof.
eapply right_inv_surjective.
unfold right_inverse.
Admitted.

Lemma C_S p n m : C n .[ m ] = Some p -> C (S n).[ m ] = Some p.
Proof.
destruct (sublist_C n) as [x [B H]].
rewrite H.
eapply elAt_app.
