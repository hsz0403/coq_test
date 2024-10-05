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

Lemma codeLengthCorrect : forall l : list nat, codeLength (codeList l) = length l.
Proof.
intros.
induction l as [| a l Hrecl].
reflexivity.
simpl in |- *.
unfold codeLength in |- *.
set (f := fun n Hrecs : nat => switchPR n (S (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) 0) in *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
unfold evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc in |- *.
unfold evalList in |- *.
unfold f at 1 in |- *.
rewrite evalStrongRecHelp1.
simpl in |- *.
rewrite cPairProjections1.
apply eq_S.
rewrite cPairProjections2.
apply Hrecl.
simpl in |- *.
apply le_lt_n_Sm.
generalize (cPair a (codeList l)).
intro.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe2.
rewrite cPairProjections.
apply le_n.
