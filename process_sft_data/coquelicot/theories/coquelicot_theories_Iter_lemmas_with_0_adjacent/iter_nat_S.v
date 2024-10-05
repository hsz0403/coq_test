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

Lemma iter_nat_S a n m : iter_nat (fun n => a (S n)) n m = iter_nat a (S n) (S m).
Proof.
rewrite /iter_nat iter_comp.
apply (f_equal (fun l => iter _ _ l _)).
rewrite MyNat.sub_succ.
elim: (S m - n)%nat {1 3}(n) => {n m} [ | n IH] m //=.
by rewrite IH.
