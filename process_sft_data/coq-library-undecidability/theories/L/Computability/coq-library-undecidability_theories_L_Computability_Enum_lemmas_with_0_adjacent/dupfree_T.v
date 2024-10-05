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
now eapply appCross_dupfree.
