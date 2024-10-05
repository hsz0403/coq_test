Require Import primRec.
Require Import cPair.
Require Import Arith.
Require Import code.
Require Import folProp.
Require Import extEqualNat.
Require Import codeList.
Section Well_Formed_Term.
Variable L : Language.
Variable codeF : Functions L -> nat.
Variable codeArityF : nat -> nat.
Hypothesis codeArityFIsPR : isPR 1 codeArityF.
Hypothesis codeArityFIsCorrect1 : forall f : Functions L, codeArityF (codeF f) = S (arity L (inr _ f)).
Hypothesis codeArityFIsCorrect2 : forall n : nat, codeArityF n <> 0 -> exists f : Functions L, codeF f = n.
Let Term := Term L.
Let Terms := Terms L.
Let var := var L.
Let apply := apply L.
Definition wellFormedTermTerms : nat -> nat := evalStrongRec 0 (fun t recs : nat => cPair (switchPR (cPairPi1 t) (charFunction 2 beq_nat (codeArityF (pred (cPairPi1 t))) (S (codeLength (cPairPi2 t))) * cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)) 1) (switchPR t (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs) * cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)) 1)).
Definition wellFormedTerm (t : nat) : nat := cPairPi1 (wellFormedTermTerms t).
Definition wellFormedTerms (ts : nat) : nat := cPairPi2 (wellFormedTermTerms ts).
Remark wellFormedTermTermsCorrect2 : forall n : nat, (wellFormedTerm n <> 0 -> exists t : Term, codeTerm L codeF t = n) /\ (wellFormedTerms n <> 0 -> exists m : nat, (exists ts : Terms m, codeTerms L codeF m ts = n)).
Proof.
assert (multLemma1 : forall a b : nat, a * b <> 0 -> a <> 0).
unfold not in |- *; intros.
apply H.
rewrite H0.
simpl in |- *.
reflexivity.
assert (multLemma2 : forall a b : nat, a * b <> 0 -> b <> 0).
intros.
rewrite mult_comm in H.
eapply multLemma1.
apply H.
assert (forall m n : nat, n < m -> (wellFormedTerm n <> 0 -> exists t : Term, codeTerm L codeF t = n) /\ (wellFormedTerms n <> 0 -> exists m : nat, (exists ts : Terms m, codeTerms L codeF m ts = n))).
intro.
induction m as [| m Hrecm].
intros.
elim (lt_not_le _ _ H).
apply le_O_n.
intros.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H)).
apply Hrecm; auto.
unfold wellFormedTerm in |- *.
unfold wellFormedTerms in |- *.
unfold wellFormedTermTerms in |- *.
set (A := fun t recs : nat => cPair (switchPR (cPairPi1 t) (charFunction 2 beq_nat (codeArityF (pred (cPairPi1 t))) (S (codeLength (cPairPi2 t))) * cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)) 1) (switchPR t (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs) * cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)) 1)) in *.
unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
rewrite cPairProjections1.
split.
unfold A at 1 in |- *.
rewrite cPairProjections1.
assert (cPair (cPairPi1 n) (cPairPi2 n) = n).
apply cPairProjections.
destruct (cPairPi1 n).
simpl in |- *.
intros.
exists (var (cPairPi2 n)).
transitivity (cPair 0 (cPairPi2 n)).
reflexivity.
assumption.
rewrite evalStrongRecHelp1.
simpl in |- *.
intros.
induction (eq_nat_dec (codeArityF n0) (S (codeLength (cPairPi2 n)))).
assert (wellFormedTerms (cPairPi2 n) <> 0).
eapply multLemma2.
apply H2.
assert (cPairPi2 n < m).
apply lt_le_trans with (cPair (S n0) (cPairPi2 n)).
apply cPairLt2.
rewrite H1.
rewrite H0.
apply le_n.
induction (Hrecm _ H4).
clear H5.
induction (H6 H3).
induction H5 as (x0, H5).
assert (codeArityF n0 <> 0).
unfold not in |- *; intros.
rewrite H7 in a.
discriminate a.
induction (codeArityFIsCorrect2 _ H7).
rewrite <- H8 in a.
rewrite codeArityFIsCorrect1 in a.
injection a.
clear a.
intro.
rewrite <- H5 in H9.
rewrite lengthTerms in H9.
cut (codeTerms L codeF x x0 = cPairPi2 n).
clear H5.
generalize x0.
clear x0.
rewrite <- H9.
intros.
exists (apply x1 x0).
transitivity (cPair (S n0) (cPairPi2 n)).
rewrite <- H8.
rewrite <- H5.
reflexivity.
assumption.
assumption.
rewrite beq_nat_not_refl in H2.
elim H2.
reflexivity.
assumption.
apply lt_le_trans with (cPair (S n0) (cPairPi2 n)).
apply cPairLt2.
rewrite H1.
apply le_n.
unfold A at 1 in |- *.
rewrite cPairProjections2.
destruct n.
simpl in |- *.
intros.
exists 0.
exists (Tnil L).
reflexivity.
repeat rewrite evalStrongRecHelp1.
simpl in |- *.
intros.
assert (cPairPi1 n < m).
rewrite <- H0.
apply le_lt_n_Sm.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe1.
rewrite cPairProjections.
apply le_n.
assert (cPairPi2 n < m).
rewrite <- H0.
apply le_lt_n_Sm.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe2.
rewrite cPairProjections.
apply le_n.
induction (Hrecm _ H2).
clear H5.
induction (Hrecm _ H3).
clear H5.
assert (wellFormedTerm (cPairPi1 n) <> 0).
eapply multLemma1.
apply H1.
assert (wellFormedTerms (cPairPi2 n) <> 0).
eapply multLemma2.
apply H1.
induction (H4 H5).
induction (H6 H7).
induction H9 as (x1, H9).
exists (S x0).
exists (Tcons L x0 x x1).
rewrite <- (cPairProjections n).
rewrite <- H8.
rewrite <- H9.
reflexivity.
simpl in |- *.
apply le_lt_n_Sm.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe2.
rewrite cPairProjections.
apply le_n.
apply le_lt_n_Sm.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe1.
rewrite cPairProjections.
apply le_n.
intros.
eapply H.
apply lt_n_Sn.
Remark wellFormedTermTermsIsPR : isPR 1 wellFormedTermTerms.
Proof.
unfold wellFormedTermTerms in |- *.
apply evalStrongRecIsPR.
apply compose2_2IsPR with (f := fun t recs : nat => switchPR (cPairPi1 t) (charFunction 2 beq_nat (codeArityF (pred (cPairPi1 t))) (S (codeLength (cPairPi2 t))) * cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)) 1) (g := fun t recs : nat => switchPR t (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs) * cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)) 1).
apply compose2_3IsPR with (f1 := fun t recs : nat => cPairPi1 t) (f2 := fun t recs : nat => charFunction 2 beq_nat (codeArityF (pred (cPairPi1 t))) (S (codeLength (cPairPi2 t))) * cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)) (f3 := fun t recs : nat => 1).
apply filter10IsPR.
apply cPairPi1IsPR.
apply compose2_2IsPR with (f := fun t recs : nat => charFunction 2 beq_nat (codeArityF (pred (cPairPi1 t))) (S (codeLength (cPairPi2 t)))) (g := fun t recs : nat => cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)).
apply filter10IsPR with (g := fun t : nat => charFunction 2 beq_nat (codeArityF (pred (cPairPi1 t))) (S (codeLength (cPairPi2 t)))).
apply compose1_2IsPR with (f := fun t : nat => codeArityF (pred (cPairPi1 t))) (f' := fun t : nat => S (codeLength (cPairPi2 t))).
apply compose1_1IsPR with (f := fun t : nat => pred (cPairPi1 t)).
apply compose1_1IsPR.
apply cPairPi1IsPR.
apply predIsPR.
apply codeArityFIsPR.
apply compose1_1IsPR with (f := fun t : nat => codeLength (cPairPi2 t)).
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply codeLengthIsPR.
apply succIsPR.
apply eqIsPR.
apply compose2_1IsPR with (f := fun t recs : nat => codeNth (t - S (cPairPi2 t)) recs).
apply compose2_2IsPR with (f := fun t recs : nat => t - S (cPairPi2 t)) (g := fun t recs : nat => recs).
apply filter10IsPR with (g := fun t : nat => t - S (cPairPi2 t)).
apply compose1_2IsPR with (f := fun t : nat => t) (f' := fun t : nat => S (cPairPi2 t)).
apply idIsPR.
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply cPairPi2IsPR.
apply multIsPR.
apply filter10IsPR with (g := fun _ : nat => 1).
apply const1_NIsPR.
apply switchIsPR.
apply compose2_3IsPR with (f1 := fun t recs : nat => t) (f2 := fun t recs : nat => cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs) * cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)) (f3 := fun t recs : nat => 1).
apply pi1_2IsPR.
apply compose2_2IsPR with (f := fun t recs : nat => cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs)) (g := fun t recs : nat => cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)).
apply compose2_1IsPR with (f := fun t recs : nat => codeNth (t - S (cPairPi1 (pred t))) recs).
apply compose2_2IsPR with (f := fun t recs : nat => t - S (cPairPi1 (pred t))) (g := fun t recs : nat => recs).
apply filter10IsPR with (g := fun t : nat => t - S (cPairPi1 (pred t))).
apply compose1_2IsPR with (f := fun t : nat => t) (f' := fun t : nat => S (cPairPi1 (pred t))).
apply idIsPR.
apply compose1_1IsPR with (f := fun t : nat => cPairPi1 (pred t)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi1IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply cPairPi1IsPR.
apply compose2_1IsPR with (f := fun t recs : nat => codeNth (t - S (cPairPi2 (pred t))) recs).
apply compose2_2IsPR with (f := fun t recs : nat => t - S (cPairPi2 (pred t))) (g := fun t recs : nat => recs).
apply filter10IsPR with (g := fun t : nat => t - S (cPairPi2 (pred t))).
apply compose1_2IsPR with (f := fun t : nat => t) (f' := fun t : nat => S (cPairPi2 (pred t))).
apply idIsPR.
apply compose1_1IsPR with (f := fun t : nat => cPairPi2 (pred t)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply cPairPi2IsPR.
apply multIsPR.
apply filter10IsPR with (g := fun _ : nat => 1).
apply const1_NIsPR.
apply switchIsPR.
apply cPairIsPR.
Section Well_Formed_Formula.
Variable codeR : Relations L -> nat.
Variable codeArityR : nat -> nat.
Hypothesis codeArityRIsPR : isPR 1 codeArityR.
Hypothesis codeArityRIsCorrect1 : forall r : Relations L, codeArityR (codeR r) = S (arity L (inl _ r)).
Hypothesis codeArityRIsCorrect2 : forall n : nat, codeArityR n <> 0 -> exists r : Relations L, codeR r = n.
Let Formula := Formula L.
Let equal := equal L.
Let atomic := atomic L.
Let impH := impH L.
Let notH := notH L.
Let forallH := forallH L.
Definition wellFormedFormula : nat -> nat := evalStrongRec 0 (fun f recs : nat => switchPR (cPairPi1 f) (switchPR (pred (cPairPi1 f)) (switchPR (pred (pred (cPairPi1 f))) (switchPR (pred (pred (pred (cPairPi1 f)))) (charFunction 2 beq_nat (codeArityR (pred (pred (pred (pred (cPairPi1 f)))))) (S (codeLength (cPairPi2 f))) * wellFormedTerms (cPairPi2 f)) (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)) (codeNth (f - S (cPairPi2 f)) recs)) (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs * codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)) (wellFormedTerm (cPairPi1 (cPairPi2 f)) * wellFormedTerm (cPairPi2 (cPairPi2 f)))).
End Well_Formed_Formula.
End Well_Formed_Term.

Remark wellFormedTermTermsCorrect2 : forall n : nat, (wellFormedTerm n <> 0 -> exists t : Term, codeTerm L codeF t = n) /\ (wellFormedTerms n <> 0 -> exists m : nat, (exists ts : Terms m, codeTerms L codeF m ts = n)).
Proof.
assert (multLemma1 : forall a b : nat, a * b <> 0 -> a <> 0).
unfold not in |- *; intros.
apply H.
rewrite H0.
simpl in |- *.
reflexivity.
assert (multLemma2 : forall a b : nat, a * b <> 0 -> b <> 0).
intros.
rewrite mult_comm in H.
eapply multLemma1.
apply H.
assert (forall m n : nat, n < m -> (wellFormedTerm n <> 0 -> exists t : Term, codeTerm L codeF t = n) /\ (wellFormedTerms n <> 0 -> exists m : nat, (exists ts : Terms m, codeTerms L codeF m ts = n))).
intro.
induction m as [| m Hrecm].
intros.
elim (lt_not_le _ _ H).
apply le_O_n.
intros.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H)).
apply Hrecm; auto.
unfold wellFormedTerm in |- *.
unfold wellFormedTerms in |- *.
unfold wellFormedTermTerms in |- *.
set (A := fun t recs : nat => cPair (switchPR (cPairPi1 t) (charFunction 2 beq_nat (codeArityF (pred (cPairPi1 t))) (S (codeLength (cPairPi2 t))) * cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)) 1) (switchPR t (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs) * cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)) 1)) in *.
unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
rewrite cPairProjections1.
split.
unfold A at 1 in |- *.
rewrite cPairProjections1.
assert (cPair (cPairPi1 n) (cPairPi2 n) = n).
apply cPairProjections.
destruct (cPairPi1 n).
simpl in |- *.
intros.
exists (var (cPairPi2 n)).
transitivity (cPair 0 (cPairPi2 n)).
reflexivity.
assumption.
rewrite evalStrongRecHelp1.
simpl in |- *.
intros.
induction (eq_nat_dec (codeArityF n0) (S (codeLength (cPairPi2 n)))).
assert (wellFormedTerms (cPairPi2 n) <> 0).
eapply multLemma2.
apply H2.
assert (cPairPi2 n < m).
apply lt_le_trans with (cPair (S n0) (cPairPi2 n)).
apply cPairLt2.
rewrite H1.
rewrite H0.
apply le_n.
induction (Hrecm _ H4).
clear H5.
induction (H6 H3).
induction H5 as (x0, H5).
assert (codeArityF n0 <> 0).
unfold not in |- *; intros.
rewrite H7 in a.
discriminate a.
induction (codeArityFIsCorrect2 _ H7).
rewrite <- H8 in a.
rewrite codeArityFIsCorrect1 in a.
injection a.
clear a.
intro.
rewrite <- H5 in H9.
rewrite lengthTerms in H9.
cut (codeTerms L codeF x x0 = cPairPi2 n).
clear H5.
generalize x0.
clear x0.
rewrite <- H9.
intros.
exists (apply x1 x0).
transitivity (cPair (S n0) (cPairPi2 n)).
rewrite <- H8.
rewrite <- H5.
reflexivity.
assumption.
assumption.
rewrite beq_nat_not_refl in H2.
elim H2.
reflexivity.
assumption.
apply lt_le_trans with (cPair (S n0) (cPairPi2 n)).
apply cPairLt2.
rewrite H1.
apply le_n.
unfold A at 1 in |- *.
rewrite cPairProjections2.
destruct n.
simpl in |- *.
intros.
exists 0.
exists (Tnil L).
reflexivity.
repeat rewrite evalStrongRecHelp1.
simpl in |- *.
intros.
assert (cPairPi1 n < m).
rewrite <- H0.
apply le_lt_n_Sm.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe1.
rewrite cPairProjections.
apply le_n.
assert (cPairPi2 n < m).
rewrite <- H0.
apply le_lt_n_Sm.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe2.
rewrite cPairProjections.
apply le_n.
induction (Hrecm _ H2).
clear H5.
induction (Hrecm _ H3).
clear H5.
assert (wellFormedTerm (cPairPi1 n) <> 0).
eapply multLemma1.
apply H1.
assert (wellFormedTerms (cPairPi2 n) <> 0).
eapply multLemma2.
apply H1.
induction (H4 H5).
induction (H6 H7).
induction H9 as (x1, H9).
exists (S x0).
exists (Tcons L x0 x x1).
rewrite <- (cPairProjections n).
rewrite <- H8.
rewrite <- H9.
reflexivity.
simpl in |- *.
apply le_lt_n_Sm.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe2.
rewrite cPairProjections.
apply le_n.
apply le_lt_n_Sm.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe1.
rewrite cPairProjections.
apply le_n.
intros.
eapply H.
apply lt_n_Sn.
