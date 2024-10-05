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

Lemma codeNoDupCorrect : forall l : list nat, codeNoDup (codeList l) = codeList (no_dup _ eq_nat_dec l).
Proof.
intros.
unfold codeNoDup in |- *.
set (g := fun l0 recs : nat => switchPR l0 (switchPR (codeIn (cPairPi1 (pred l0)) (codeNth (l0 - S (cPairPi2 (pred l0))) recs)) (codeNth (l0 - S (cPairPi2 (pred l0))) recs) (S (cPair (cPairPi1 (pred l0)) (codeNth (l0 - S (cPairPi2 (pred l0))) recs)))) 0) in *.
induction l as [| a l Hrecl].
simpl in |- *.
unfold evalStrongRec in |- *.
simpl in |- *.
rewrite cPairProjections1.
reflexivity.
simpl in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
unfold g at 1 in |- *.
repeat rewrite evalStrongRecHelp1.
unfold pred in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
rewrite Hrecl.
rewrite codeInCorrect.
induction (In_dec eq_nat_dec a (no_dup nat eq_nat_dec l)).
reflexivity.
reflexivity.
simpl in |- *.
apply le_lt_n_Sm.
apply cPairLe2A.
