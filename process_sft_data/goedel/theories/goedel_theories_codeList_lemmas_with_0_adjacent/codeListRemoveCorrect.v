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

Lemma codeListRemoveCorrect : forall (a : nat) (l : list nat), codeListRemove a (codeList l) = codeList (list_remove nat eq_nat_dec a l).
Proof.
intros.
unfold codeListRemove in |- *.
set (f := fun n Hrecs p1 : nat => switchPR n (switchPR (charFunction 2 beq_nat (cPairPi1 (pred n)) p1) (codeNth (n - S (cPairPi2 (pred n))) Hrecs) (S (cPair (cPairPi1 (pred n)) (codeNth (n - S (cPairPi2 (pred n))) Hrecs)))) (codeList nil)) in *.
induction l as [| a0 l Hrecl].
simpl in |- *.
unfold evalStrongRec in |- *.
simpl in |- *.
reflexivity.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
rewrite computeEvalStrongRecHelp.
unfold f at 2 in |- *.
unfold compose2 in |- *.
set (n := codeList (a0 :: l)) in *.
set (A := n - S (cPairPi2 (pred n))) in *.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
assert (extEqual 1 (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 f n) 0 (Vector.nil _)) (fun b : nat => codeNth (n - S (cPairPi2 (pred n))) b)) (evalStrongRec 1 f (cPairPi2 (pred n)))).
apply (evalStrongRecHelp2 1).
simpl in |- *.
unfold n in |- *.
rewrite cPairProjections2.
simpl in |- *.
apply le_lt_n_Sm.
apply cPairLe2.
simpl in H.
induction (eq_nat_dec a0 a).
rewrite a1.
rewrite <- beq_nat_refl.
simpl in |- *.
unfold A in |- *.
rewrite H.
rewrite cPairProjections2.
auto.
rewrite beq_nat_not_refl.
simpl in |- *.
replace (codeList (list_remove nat eq_nat_dec a l)) with (codeNth A (evalStrongRecHelp 1 f n a)).
reflexivity.
unfold A in |- *.
rewrite H.
simpl in |- *.
rewrite cPairProjections2.
auto.
auto.
