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

Lemma iter_nat_ext_loc (a b : nat -> T) (n m : nat) : (forall k, (n <= k <= m)%nat -> a k = b k) -> iter_nat a n m = iter_nat b n m.
Proof.
intros Heq.
apply iter_ext.
intros k Hk.
apply Heq.
by apply In_iota.
