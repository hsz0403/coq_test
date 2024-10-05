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

Lemma sublist_T : forall n : nat, exists (x : term) (B : list term), T (S n) = T n ++ x :: B.
Proof.
intros n.
exists (# (S n)).
simpl.
Admitted.

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

Lemma T_S s n m : T n .[ m ] = Some s -> T (S n).[ m ] = Some s.
Proof.
destruct (sublist_T n) as [x [B H]].
rewrite H.
eapply elAt_app.
