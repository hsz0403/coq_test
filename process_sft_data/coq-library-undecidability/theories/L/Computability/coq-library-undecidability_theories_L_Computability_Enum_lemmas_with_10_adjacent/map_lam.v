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

Lemma T_ge s n1 n2 m : n2 >= n1 -> T n1 .[ m ] = Some s -> T n2 .[ m ] = Some s.
Proof.
remember (S n1) as n1'.
Admitted.

Lemma appCross_correct A B s t : (s el A /\ t el B) <-> (app s t) el appCross A B.
Proof.
split.
-
induction A; simpl; intuition; subst; eauto using in_map.
-
Admitted.

Lemma T_var n : #n el T n.
Proof.
Admitted.

Lemma T_app s t n : s el T n -> t el T n -> s t el T (S n).
Proof.
intros; simpl.
decide (s t el T n); auto; simpl.
rewrite in_app_iff; simpl.
rewrite in_filter_iff, in_app_iff, <- appCross_correct.
Admitted.

Lemma T_el_ge s n m : n >= m -> s el T m -> s el T n.
Proof.
Admitted.

Lemma T_lam s n : s el T n -> lam s el T (S n).
Proof.
intros; simpl; decide (lam s el T n); auto.
rewrite in_app_iff; simpl; rewrite in_filter_iff, in_app_iff, in_map_iff.
right.
right.
Admitted.

Lemma T_exhaustive s : s el (T (exh_size s)).
Proof with simpl; repeat rewrite in_app_iff; repeat rewrite in_filter_iff; try rewrite <- appCross_correct; eauto using in_filter_iff, in_app_iff, appCross_correct, el_elAt, elAt_el, T_ge, in_map.
induction s.
-
destruct n; simpl; auto.
-
eapply T_app; eapply T_el_ge; try eassumption; fold exh_size plus; lia.
-
Admitted.

Lemma T_longenough m : |T m| > m.
Proof.
induction m.
-
simpl; lia.
-
simpl.
rewrite app_length.
simpl.
Admitted.

Lemma g_inv_g s : g_inv (g s) = s.
Proof.
unfold g.
destruct( pos s (T (exh_size s)) ) eqn:A.
unfold g_inv.
destruct (T n .[ n ] ) eqn:B.
-
eapply pos_elAt in A.
destruct (lt_eq_lt_dec n (exh_size s)) as [[D | D] | D].
+
eapply T_ge in B.
rewrite B in A.
now inv A.
lia.
+
subst.
assert (Some s = Some t) by now rewrite <- A, <- B.
congruence.
+
eapply T_ge in A.
rewrite A in B.
now inv B.
lia.
-
eapply nth_error_none in B.
assert (|T n| > n) by eapply T_longenough.
lia.
-
assert (HIn : s el T (exh_size s)) by eapply T_exhaustive.
eapply el_elAt in HIn; eauto.
destruct HIn.
eapply elAt_el in H.
eapply el_pos in H.
destruct H.
Admitted.

Lemma disjoint_symm X (A B : list X) : disjoint A B <-> disjoint B A.
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

Lemma C_S p n m : C n .[ m ] = Some p -> C (S n).[ m ] = Some p.
Proof.
destruct (sublist_C n) as [x [B H]].
rewrite H.
Admitted.

Lemma C_ge p n1 n2 m : n2 >= n1 -> C n1 .[ m ] = Some p -> C n2 .[ m ] = Some p.
Proof.
remember (S n1) as n1'.
Admitted.

Lemma map_lam A : forall x, x el map lam A -> exists t, x = lam t.
Proof.
intros x B; rewrite in_map_iff in B; destruct B as [? [B _]]; subst; eauto.
