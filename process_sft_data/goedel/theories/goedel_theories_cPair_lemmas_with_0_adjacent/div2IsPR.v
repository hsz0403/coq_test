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

Lemma div2IsPR : isPR 1 div2.
Proof.
assert (isPR 1 (evalStrongRec 0 (fun n recs : nat => switchPR n (switchPR (pred n) (S (codeNth (n - S (pred (pred n))) recs)) 0) 0))).
apply evalStrongRecIsPR.
assert (isPR 2 (fun n recs : nat => 0)).
exists (composeFunc 2 0 (PRnil _) zeroFunc).
simpl in |- *.
auto.
apply compose2_3IsPR with (f1 := fun n recs : nat => n) (f2 := fun n recs : nat => switchPR (pred n) (S (codeNth (n - S (pred (pred n))) recs)) 0) (f3 := fun n recs : nat => 0).
apply pi1_2IsPR.
apply compose2_3IsPR with (f1 := fun n recs : nat => pred n) (f2 := fun n recs : nat => S (codeNth (n - S (pred (pred n))) recs)) (f3 := fun n recs : nat => 0).
apply filter10IsPR.
apply predIsPR.
apply compose2_1IsPR with (f := fun n recs : nat => codeNth (n - S (pred (pred n))) recs).
apply compose2_2IsPR with (f := fun n recs : nat => n - S (pred (pred n))) (g := fun n recs : nat => recs).
apply filter10IsPR with (g := fun n : nat => n - S (pred (pred n))).
apply compose1_2IsPR with (f := fun n : nat => n) (f' := fun n : nat => S (pred (pred n))).
apply idIsPR.
apply compose1_1IsPR with (f := fun n : nat => pred (pred n)).
apply compose1_1IsPR; apply predIsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply succIsPR.
auto.
apply switchIsPR.
auto.
apply switchIsPR.
induction H as (x, p).
exists x.
eapply extEqualTrans.
apply p.
clear p x.
simpl in |- *.
intros.
set (f := fun n recs : nat => switchPR n (switchPR (pred n) (S (codeNth (n - S (pred (pred n))) recs)) 0) 0) in *.
elim c using ind_0_1_SS.
unfold evalStrongRec in |- *.
simpl in |- *.
auto.
unfold evalStrongRec in |- *.
simpl in |- *.
apply cPairProjections1.
intros.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
rewrite computeEvalStrongRecHelp.
unfold f at 2 in |- *.
set (A := S (S n) - S (pred (pred (S (S n))))) in *.
simpl in |- *.
rewrite cPairProjections1.
apply eq_S.
rewrite <- H.
unfold A in |- *.
apply evalStrongRecHelp1.
auto.
