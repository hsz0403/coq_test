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
congruence.
