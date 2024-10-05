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

Lemma codeInCorrect : forall (a : nat) (l : list nat), codeIn a (codeList l) = match In_dec eq_nat_dec a l with | left _ => 1 | right _ => 0 end.
Proof.
intros.
induction l as [| a0 l Hrecl]; simpl in |- *.
unfold codeIn, evalStrongRec in |- *.
simpl in |- *.
rewrite cPairProjections1.
reflexivity.
unfold codeIn, evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
rewrite computeEvalStrongRecHelp.
unfold evalList in |- *.
set (f := fun n Hrecs p1 : nat => switchPR n (switchPR (charFunction 2 beq_nat (cPairPi1 (pred n)) p1) 1 (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) 0) in *.
set (m := cPairPi2 (pred (S (cPair a0 (codeList l))))) in *.
set (n := S (cPair a0 (codeList l))) in *.
simpl in |- *.
repeat rewrite cPairProjections1.
induction (eq_nat_dec a0 a).
rewrite a1.
rewrite <- beq_nat_refl.
simpl in |- *.
reflexivity.
rewrite beq_nat_not_refl.
simpl in |- *.
assert (extEqual _ (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 f n) 0 (Vector.nil _)) (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 f m)).
apply (evalStrongRecHelp2 1).
unfold m in |- *.
unfold n in |- *.
simpl in |- *.
rewrite cPairProjections2.
apply le_lt_n_Sm.
apply cPairLe2.
simpl in H.
rewrite H.
unfold codeIn in Hrecl.
move f after Hrecl; fold f in Hrecl.
unfold m, n in |- *.
simpl in |- *.
rewrite cPairProjections2.
rewrite Hrecl.
clear H f Hrecl.
induction (In_dec eq_nat_dec a l).
induction (In_dec eq_nat_dec a (a0 :: l)).
reflexivity.
elim b0.
simpl in |- *.
auto.
induction (In_dec eq_nat_dec a (a0 :: l)).
induction a1 as [H| H].
elim b; auto.
elim b0; auto.
reflexivity.
auto.
