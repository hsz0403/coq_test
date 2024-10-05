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

Lemma T_dup n1 n2 m1 m2 x : T n1 .[m1 ] = Some x -> T n2 .[m2] = Some x -> m1 = m2.
Proof.
destruct (lt_eq_lt_dec n1 n2) as [[H | H] | H]; try subst; try eapply lt_le_weak in H; eauto using (T_ge), dupfree_elAt, dupfree_T.
