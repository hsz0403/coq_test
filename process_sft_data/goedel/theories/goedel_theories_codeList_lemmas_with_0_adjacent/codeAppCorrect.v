Require Import primRec.
Require Import cPair.
Require Export Coq.Lists.List.
Require Import ListExt.
Require Import Arith.
Require Vector.
Require Import extEqualNat.
Definition codeLength : nat -> nat := evalStrongRec 0 (fun n Hrecs : nat => switchPR n (S (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) 0).
Definition codeApp : nat -> nat -> nat := evalStrongRec 1 (fun n Hrecs p1 : nat => switchPR n (S (cPair (cPairPi1 (pred n)) (codeNth (n - S (cPairPi2 (pred n))) Hrecs))) p1).
Definition codeListRemove (a l : nat) : nat := evalStrongRec 1 (fun n Hrecs p1 : nat => switchPR n (switchPR (charFunction 2 beq_nat (cPairPi1 (pred n)) p1) (codeNth (n - S (cPairPi2 (pred n))) Hrecs) (S (cPair (cPairPi1 (pred n)) (codeNth (n - S (cPairPi2 (pred n))) Hrecs)))) (codeList nil)) l a.
Definition codeIn (a l : nat) : nat := evalStrongRec 1 (fun n Hrecs p1 : nat => switchPR n (switchPR (charFunction 2 beq_nat (cPairPi1 (pred n)) p1) 1 (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) 0) l a.
Definition codeNoDup : nat -> nat := evalStrongRec 0 (fun l recs : nat => switchPR l (switchPR (codeIn (cPairPi1 (pred l)) (codeNth (l - S (cPairPi2 (pred l))) recs)) (codeNth (l - S (cPairPi2 (pred l))) recs) (S (cPair (cPairPi1 (pred l)) (codeNth (l - S (cPairPi2 (pred l))) recs)))) 0).

Lemma codeAppCorrect : forall l1 l2 : list nat, codeApp (codeList l1) (codeList l2) = codeList (l1 ++ l2).
Proof.
intros.
unfold codeApp in |- *.
set (f := fun n Hrecs p1 : nat => switchPR n (S (cPair (cPairPi1 (pred n)) (codeNth (n - S (cPairPi2 (pred n))) Hrecs))) p1) in *.
induction l1 as [| a l1 Hrecl1].
unfold evalStrongRec in |- *.
simpl in |- *.
rewrite cPairProjections1.
reflexivity.
simpl in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
rewrite computeEvalStrongRecHelp.
unfold f at 2 in |- *.
unfold pred in |- *.
set (n := S (cPair a (codeList l1))) in *.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
replace (codeList (l1 ++ l2)) with (codeNth (cPair a (codeList l1) - codeList l1) (evalStrongRecHelp 1 f n (codeList l2))).
reflexivity.
assert (extEqual 1 (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 f n) 0 (Vector.nil _)) (fun b : nat => codeNth (n - S (codeList l1)) b)) (evalStrongRec 1 f (codeList l1))).
apply (evalStrongRecHelp2 1).
unfold n in |- *.
apply le_lt_n_Sm.
apply cPairLe2.
simpl in H.
rewrite H.
auto.
