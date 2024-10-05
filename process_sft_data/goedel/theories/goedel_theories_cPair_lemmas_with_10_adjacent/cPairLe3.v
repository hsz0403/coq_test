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

Lemma cPairProjections : forall a : nat, cPair (cPairPi1 a) (cPairPi2 a) = a.
Proof.
assert (forall a b : nat, b < sumToN a -> cPair (cPairPi1 b) (cPairPi2 b) = b).
intros.
induction a as [| a Hreca].
simpl in H.
elim (lt_n_O _ H).
induction (le_or_lt (sumToN a) b).
assert (searchXY b = a).
apply cPairProjectionsHelp; auto.
unfold cPair in |- *.
replace (cPairPi1 b + cPairPi2 b) with a.
unfold cPairPi1 in |- *.
rewrite H1.
rewrite plus_comm.
rewrite <- le_plus_minus.
reflexivity.
auto.
unfold cPairPi2 in |- *.
rewrite <- le_plus_minus.
auto.
unfold cPairPi1 in |- *.
rewrite H1.
simpl in H.
apply (fun p n m : nat => plus_le_reg_l n m p) with (sumToN a).
rewrite <- le_plus_minus.
rewrite plus_comm.
apply lt_n_Sm_le.
auto.
auto.
apply Hreca.
auto.
intros.
apply H with (S a).
apply lt_le_trans with (S a).
apply lt_n_Sn.
Admitted.

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
Admitted.

Lemma cPairPi1IsPR : isPR 1 cPairPi1.
Proof.
unfold cPairPi1 in |- *.
apply compose1_2IsPR with (g := minus) (f := fun x : nat => x) (f' := fun a : nat => sumToN (searchXY a)).
apply idIsPR.
apply compose1_1IsPR.
apply searchXYIsPR.
apply sumToNIsPR.
Admitted.

Lemma cPairPi2IsPR : isPR 1 cPairPi2.
Proof.
unfold cPairPi2 in |- *.
apply compose1_2IsPR with (g := minus) (f := searchXY) (f' := cPairPi1).
apply searchXYIsPR.
apply cPairPi1IsPR.
Admitted.

Lemma cPairProjections1 : forall a b : nat, cPairPi1 (cPair a b) = a.
Proof.
intros.
unfold cPair in |- *.
unfold cPairPi1 in |- *.
replace (searchXY (a + sumToN (a + b))) with (a + b).
rewrite plus_comm.
apply minus_plus.
symmetry in |- *.
apply cPairProjectionsHelp.
simpl in |- *.
apply le_lt_n_Sm.
apply plus_le_compat_r.
apply le_plus_l.
Admitted.

Lemma cPairProjections2 : forall a b : nat, cPairPi2 (cPair a b) = b.
Proof.
intros.
unfold cPairPi2 in |- *.
rewrite cPairProjections1.
unfold cPair in |- *.
replace (searchXY (a + sumToN (a + b))) with (a + b).
apply minus_plus.
symmetry in |- *.
apply cPairProjectionsHelp.
simpl in |- *.
apply le_lt_n_Sm.
apply plus_le_compat_r.
apply le_plus_l.
Admitted.

Lemma cPairLe1 : forall a b : nat, a <= cPair a b.
Proof.
intros.
unfold cPair in |- *.
Admitted.

Lemma cPairLe1A : forall a : nat, cPairPi1 a <= a.
intros.
apply le_trans with (cPair (cPairPi1 a) (cPairPi2 a)).
apply cPairLe1.
rewrite cPairProjections.
Admitted.

Lemma cPairLe2 : forall a b : nat, b <= cPair a b.
Proof.
intros.
unfold cPair in |- *.
eapply le_trans.
apply le_plus_r.
apply plus_le_compat_l.
apply le_trans with (a + b).
apply le_plus_r.
Admitted.

Lemma cPairLe2A : forall a : nat, cPairPi2 a <= a.
intros.
apply le_trans with (cPair (cPairPi1 a) (cPairPi2 a)).
apply cPairLe2.
rewrite cPairProjections.
Admitted.

Lemma cPairLt1 : forall a b : nat, a < cPair a (S b).
Proof.
intros.
unfold cPair in |- *.
rewrite (plus_comm a (S b)).
simpl in |- *.
rewrite plus_comm.
simpl in |- *.
rewrite plus_comm.
unfold lt in |- *.
apply le_n_S.
Admitted.

Lemma cPairLt2 : forall a b : nat, b < cPair (S a) b.
Proof.
intros.
unfold cPair in |- *.
simpl in |- *.
unfold lt in |- *.
apply le_n_S.
eapply le_trans.
apply le_plus_r.
apply plus_le_compat_l.
apply le_S.
eapply le_trans.
apply le_plus_l.
rewrite plus_comm.
Admitted.

Lemma codeListInj : forall l m : list nat, codeList l = codeList m -> l = m.
Proof.
intro.
induction l as [| a l Hrecl].
intros.
destruct m as [| n l].
reflexivity.
discriminate H.
intros.
destruct m as [| n l0].
discriminate H.
simpl in H.
replace n with a.
rewrite (Hrecl l0).
reflexivity.
eapply cPairInj2.
apply eq_add_S.
apply H.
eapply cPairInj1.
apply eq_add_S.
Admitted.

Definition codeNth (n m : nat) : nat.
intros.
assert nat.
induction n as [| n Hrecn].
exact m.
exact (cPairPi2 (pred Hrecn)).
Admitted.

Let drop (n : nat) : forall (l : list nat), list nat.
induction n as [| n Hrecn].
exact (fun l => l).
intros.
apply Hrecn.
destruct l.
exact (nil (A:=nat)).
Admitted.

Lemma codeNthCorrect : forall (n : nat) (l : list nat), codeNth n (codeList l) = nth n l 0.
Proof.
unfold codeNth in |- *.
set (A := fun l : list nat => match l with | nil => nil (A:=nat) | _ :: l0 => l0 end) in *.
assert (forall l : list nat, cPairPi2 (pred (codeList l)) = codeList (A l)).
destruct l.
simpl in |- *.
apply (cPairProjections2 0 0).
simpl in |- *.
apply cPairProjections2.
assert (forall (n : nat) (l : list nat), nat_rec (fun _ : nat => nat) (codeList l) (fun _ Hrecn : nat => cPairPi2 (pred Hrecn)) n = codeList (drop n l)).
simple induction n.
simpl in |- *.
reflexivity.
simpl in |- *.
intros.
rewrite H0.
rewrite H.
unfold A in |- *.
clear H0.
generalize l.
clear l.
induction n0 as [| n0 Hrecn0]; simpl in |- *; intros.
reflexivity.
destruct l.
apply (Hrecn0 nil).
apply Hrecn0.
intros.
replace (nth n l 0) with match drop n l with | nil => 0 | a :: _ => a end.
rewrite H0.
destruct (drop n l).
simpl in |- *.
apply (cPairProjections1 0 0).
simpl in |- *.
apply cPairProjections1.
generalize l.
clear l.
induction n as [| n Hrecn].
destruct l; reflexivity.
destruct l.
simpl in Hrecn.
destruct n; apply (Hrecn nil).
simpl in |- *.
Admitted.

Lemma codeNthIsPR : isPR 2 codeNth.
Proof.
intros.
unfold codeNth in |- *.
apply compose2_1IsPR with (g := fun x : nat => cPairPi1 (pred x)) (f := fun n m : nat => nat_rec (fun _ : nat => nat) m (fun _ Hrecn : nat => cPairPi2 (pred Hrecn)) n).
apply ind1ParamIsPR with (g := fun m : nat => m) (f := fun _ Hrecn m : nat => cPairPi2 (pred Hrecn)).
apply filter010IsPR with (g := fun x : nat => cPairPi2 (pred x)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi2IsPR.
apply idIsPR.
apply compose1_1IsPR.
apply predIsPR.
Admitted.

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
Admitted.

Lemma computeEvalStrongRecHelp : forall (n : nat) (f : naryFunc (S (S n))) (c : nat), evalStrongRecHelp n f (S c) = compose2 n (evalStrongRecHelp n f c) (fun a0 : nat => evalComposeFunc n 2 (Vector.cons (naryFunc n) (f c a0) 1 (Vector.cons (naryFunc n) (evalConstFunc n a0) 0 (Vector.nil (naryFunc n)))) (fun a1 b0 : nat => S (cPair a1 b0))).
Proof.
intros.
unfold evalStrongRecHelp at 1 in |- *.
simpl in |- *.
fold (naryFunc n) in |- *.
induction (eq_nat_dec n (S n)).
elim (lt_not_le n (S n)).
apply lt_n_Sn.
rewrite <- a.
auto.
induction (eq_nat_dec n n).
replace (evalPrimRecFunc n (evalComposeFunc n 0 (Vector.nil (naryFunc n)) 0) (fun a0 a1 : nat => evalComposeFunc n 2 (Vector.cons (naryFunc n) (f a0 a1) 1 (Vector.cons (naryFunc n) (evalConstFunc n a1) 0 (Vector.nil (naryFunc n)))) (fun a2 b0 : nat => S (cPair a2 b0))) c) with (evalStrongRecHelp n f c).
reflexivity.
unfold evalStrongRecHelp at 1 in |- *.
simpl in |- *.
fold (naryFunc n) in |- *.
induction (eq_nat_dec n (S n)).
elim b.
auto.
induction (eq_nat_dec n n).
reflexivity.
elim b1.
auto.
elim b0.
Admitted.

Let listValues (f : naryFunc 2) (n : nat) : list nat.
intros.
induction n as [| n Hrecn].
exact nil.
Admitted.

Lemma cPairLe3 : forall a b c d : nat, a <= b -> c <= d -> cPair a c <= cPair b d.
Proof.
intros.
unfold cPair in |- *.
apply le_trans with (a + sumToN (b + d)).
apply plus_le_compat_l.
apply sumToN2.
apply le_trans with (a + d).
apply plus_le_compat_l.
auto.
apply plus_le_compat_r.
auto.
apply plus_le_compat_r.
auto.
