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

Lemma evalStrongRecIsPR : forall (n : nat) (f : naryFunc (S (S n))), isPR _ f -> isPR _ (evalStrongRec n f).
Proof.
intros.
unfold evalStrongRec, evalStrongRecHelp in |- *.
fold (naryFunc (S n)) in |- *.
set (A := evalPrimRecFunc n (evalComposeFunc n 0 (Vector.nil (naryFunc n)) (codeList nil)) (evalComposeFunc (S (S n)) 2 (Vector.cons (naryFunc (S (S n))) f 1 (Vector.cons (naryFunc (S (S n))) (evalProjFunc (S (S n)) n (lt_S n (S n) (lt_n_Sn n))) 0 (Vector.nil (naryFunc (S (S n)))))) (fun a b : nat => S (cPair a b)))) in *.
assert (isPR (S n) A).
unfold A in |- *.
assert (isPR 2 (fun a b : nat => S (cPair a b))).
apply compose2_1IsPR.
apply cPairIsPR.
apply succIsPR.
assert (isPR 1 (fun z : nat => cPairPi1 (pred z))).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi1IsPR.
induction H as (x, p).
induction H0 as (x0, p0).
induction H1 as (x1, p1).
exists (primRecFunc n (composeFunc n 0 (PRnil _) zeroFunc) (composeFunc (S (S n)) 2 (PRcons _ _ x (PRcons _ _ (projFunc (S (S n)) n (lt_S n (S n) (lt_n_Sn n))) (PRnil _))) x0)).
apply extEqualTrans with (evalPrimRecFunc n (evalComposeFunc n 0 (Vector.nil _) 0) (evalComposeFunc (S (S n)) 2 (Vector.cons _ (evalPrimRec _ x) _ (Vector.cons _ (evalProjFunc (S (S n)) n (lt_S n (S n) (lt_n_Sn n))) _ (Vector.nil _))) (evalPrimRec _ x0))).
apply extEqualRefl.
apply extEqualPrimRec.
simpl in |- *.
apply extEqualRefl.
apply extEqualCompose.
unfold extEqualVector, extEqualVectorGeneral, Vector.t_rect in |- *.
repeat split; auto.
apply extEqualRefl.
auto.
assert (isPR (S n) (fun z : nat => A (S z))).
apply compose1_NIsPR.
auto.
apply succIsPR.
clear H0.
assert (isPR 1 (fun z : nat => cPairPi1 (pred z))).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi1IsPR.
induction H0 as (x, p).
induction H1 as (x0, p0).
exists (composeFunc (S n) 1 (PRcons _ _ x0 (PRnil _)) x).
simpl in |- *.
fold (naryFunc n) in |- *.
intros.
apply extEqualCompose.
unfold extEqualVector in |- *.
simpl in |- *.
repeat split.
apply (p0 c).
auto.
