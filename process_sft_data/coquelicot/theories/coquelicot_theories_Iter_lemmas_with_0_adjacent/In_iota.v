Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Rcomplements.
Require Import List Omega.
Require Import mathcomp.ssreflect.seq mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype.
Section Iter.
Context {I T : Type}.
Context (op : T -> T -> T).
Context (x0 : T).
Context (neutral_l : forall x, op x0 x = x).
Context (neutral_r : forall x, op x x0 = x).
Context (assoc : forall x y z, op x (op y z) = op (op x y) z).
Fixpoint iter (l : list I) (f : I -> T) := match l with | nil => x0 | cons h l' => op (f h) (iter l' f) end.
Definition iter' (l : list I) (f : I -> T) := fold_right (fun i acc => op (f i) acc) x0 l.
End Iter.
Section Iter_nat.
Context {T : Type}.
Context (op : T -> T -> T).
Context (x0 : T).
Context (neutral_l : forall x, op x0 x = x).
Context (neutral_r : forall x, op x x0 = x).
Context (assoc : forall x y z, op x (op y z) = op (op x y) z).
Definition iter_nat (a : nat -> T) n m := iter op x0 (iota n (S m - n)) a.
End Iter_nat.

Lemma In_iota (n m k : nat) : (n <= m <= k)%nat <-> In m (iota n (S k - n)).
Proof.
generalize (mem_iota n (S k - n) m).
case: In_mem => // H H0.
apply sym_eq in H0.
case/andP: H0 => H0 H1.
apply Rcomplements.SSR_leq in H0.
apply SSR_leq in H1.
change ssrnat.addn with Peano.plus in H1.
split => // _.
split => //.
case: (le_dec n (S m)).
intro ; omega.
intro H2.
rewrite not_le_minus_0 in H1 => //.
contradict H2.
by eapply le_trans, le_n_Sn.
contradict H2.
by eapply le_trans, le_n_Sn.
change ssrnat.addn with Peano.plus in H0.
split => // H1.
case: H1 => /= H1 H2.
apply sym_eq in H0.
apply Bool.andb_false_iff in H0.
case: H0 => //.
move/SSR_leq: H1 ; by case: ssrnat.leq.
rewrite -le_plus_minus ; try omega.
move/le_n_S/SSR_leq: H2 ; by case: ssrnat.leq.
