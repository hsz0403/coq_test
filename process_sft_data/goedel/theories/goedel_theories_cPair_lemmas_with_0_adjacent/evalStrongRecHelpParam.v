Require Import Arith.
Require Import Coq.Lists.List.
Require Import extEqualNat.
Require Import primRec.
Require Vector.
Require Import Div2.
Definition sumToN (n : nat) := nat_rec (fun _ => nat) 0 (fun x y : nat => S x + y) n.
Definition cPair (a b : nat) := a + sumToN (a + b).
Section CPair_Injectivity.
Remark cPairInjHelp : forall a b c d : nat, cPair a b = cPair c d -> a + b = c + d.
Proof.
assert (forall a b : nat, a < b -> a + sumToN a < sumToN b).
simple induction b.
intros.
elim (lt_n_O _ H).
intros.
simpl in |- *.
assert (a <= n).
apply lt_n_Sm_le.
assumption.
induction (le_lt_or_eq a n H1).
apply lt_trans with (sumToN n).
auto.
apply le_lt_n_Sm.
apply le_plus_r.
rewrite H2.
apply lt_n_Sn.
unfold cPair in |- *.
assert (forall a b c d : nat, a <= c -> b <= d -> a + sumToN c = b + sumToN d -> c = d).
intros.
induction (le_or_lt c d).
induction (le_lt_or_eq _ _ H3).
assert (a + sumToN c < sumToN d).
apply le_lt_trans with (c + sumToN c).
apply plus_le_compat_r.
auto.
auto.
rewrite H2 in H5.
elim (lt_not_le _ _ H5).
apply le_plus_r.
auto.
assert (b + sumToN d < sumToN c).
apply le_lt_trans with (d + sumToN d).
apply plus_le_compat_r.
auto.
auto.
rewrite <- H2 in H4.
elim (lt_not_le _ _ H4).
apply le_plus_r.
intros.
eapply H0.
apply le_plus_l.
apply le_plus_l.
auto.
End CPair_Injectivity.
Section CPair_projections.
Let searchXY (a : nat) := boundedSearch (fun a y : nat => ltBool a (sumToN (S y))) a.
Definition cPairPi1 (a : nat) := a - sumToN (searchXY a).
Definition cPairPi2 (a : nat) := searchXY a - cPairPi1 a.
Remark searchXYIsPR : isPR 1 searchXY.
Proof.
unfold searchXY in |- *.
apply boundSearchIsPR with (P := fun a y : nat => ltBool a (sumToN (S y))).
unfold isPRrel in |- *.
apply compose2_2IsPR with (h := charFunction 2 ltBool) (f := fun a y : nat => a) (g := fun a y : nat => sumToN (S y)).
apply pi1_2IsPR.
apply filter01IsPR with (g := fun y : nat => sumToN (S y)).
apply compose1_1IsPR.
apply succIsPR.
apply sumToNIsPR.
apply ltIsPR.
End CPair_projections.
Section CPair_Order.
End CPair_Order.
Section code_nat_list.
Fixpoint codeList (l : list nat) : nat := match l with | nil => 0 | n :: l' => S (cPair n (codeList l')) end.
Definition codeNth (n m : nat) : nat.
intros.
assert nat.
induction n as [| n Hrecn].
exact m.
exact (cPairPi2 (pred Hrecn)).
exact (cPairPi1 (pred H)).
Defined.
Let drop (n : nat) : forall (l : list nat), list nat.
induction n as [| n Hrecn].
exact (fun l => l).
intros.
apply Hrecn.
destruct l.
exact (nil (A:=nat)).
exact l.
Defined.
End code_nat_list.
Section Strong_Recursion.
Definition evalStrongRecHelp (n : nat) (f : naryFunc (S (S n))) : naryFunc (S n) := evalPrimRecFunc n (evalComposeFunc n 0 (Vector.nil _) (codeList nil)) (evalComposeFunc (S (S n)) 2 (Vector.cons _ f _ (Vector.cons _ (evalProjFunc (S (S n)) n (lt_S _ _ (lt_n_Sn _))) _ (Vector.nil _))) (fun a b : nat => S (cPair a b))).
Definition evalStrongRec (n : nat) (f : naryFunc (S (S n))) : naryFunc (S n) := evalComposeFunc (S n) 1 (Vector.cons _ (fun z : nat => evalStrongRecHelp n f (S z)) _ (Vector.nil _)) (fun z : nat => cPairPi1 (pred z)).
Let listValues (f : naryFunc 2) (n : nat) : list nat.
intros.
induction n as [| n Hrecn].
exact nil.
exact (evalStrongRec _ f n :: Hrecn).
Defined.
End Strong_Recursion.

Lemma evalStrongRecHelpParam : forall (a n c : nat) (f : naryFunc (S (S (S a)))), extEqual a (evalStrongRecHelp (S a) f n c) (evalStrongRecHelp a (fun x y : nat => f x y c) n).
Proof.
intros.
unfold evalStrongRecHelp in |- *.
eapply extEqualTrans.
apply extEqualSym.
apply evalPrimRecParam.
assert (extEqual (S a) (evalPrimRecFunc a (evalComposeFunc (S a) 0 (Vector.nil (naryFunc (S a))) (codeList nil) c) (fun x y : nat => evalComposeFunc (S (S (S a))) 2 (Vector.cons (naryFunc (S (S (S a)))) f 1 (Vector.cons (naryFunc (S (S (S a)))) (evalProjFunc (S (S (S a))) (S a) (lt_S (S a) (S (S a)) (lt_n_Sn (S a)))) 0 (Vector.nil (naryFunc (S (S (S a))))))) (fun a0 b : nat => S (cPair a0 b)) x y c)) (evalPrimRecFunc a (evalComposeFunc a 0 (Vector.nil (naryFunc a)) (codeList nil)) (evalComposeFunc (S (S a)) 2 (Vector.cons (naryFunc (S (S a))) (fun x y : nat => f x y c) 1 (Vector.cons (naryFunc (S (S a))) (evalProjFunc (S (S a)) a (lt_S a (S a) (lt_n_Sn a))) 0 (Vector.nil (naryFunc (S (S a)))))) (fun a0 b : nat => S (cPair a0 b))))).
apply (extEqualPrimRec a (evalComposeFunc (S a) 0 (Vector.nil (naryFunc (S a))) (codeList nil) c)).
simpl in |- *.
apply extEqualRefl.
simpl in |- *.
fold (naryFunc a) in |- *.
induction (sumbool_rec (fun _ : {a = S a} + {a <> S a} => {S a = S (S a)} + {S a <> S (S a)}) (fun a0 : a = S a => left (S a <> S (S a)) (f_equal S a0)) (fun b : a <> S a => right (S a = S (S a)) (not_eq_S a (S a) b)) (eq_nat_dec a (S a))).
elim (lt_not_le (S a) (S (S a))).
apply lt_n_Sn.
rewrite <- a0.
auto.
induction (sumbool_rec (fun _ : {a = a} + {a <> a} => {S a = S a} + {S a <> S a}) (fun a0 : a = a => left (S a <> S a) (f_equal S a0)) (fun b0 : a <> a => right (S a = S a) (not_eq_S a a b0)) (eq_nat_dec a a)).
induction (eq_nat_dec a (S a)).
elim (lt_not_le a (S a)).
apply lt_n_Sn.
rewrite <- a1.
auto.
induction (eq_nat_dec a a).
intros.
apply extEqualRefl.
elim b1.
auto.
elim b0.
auto.
apply (H n).
