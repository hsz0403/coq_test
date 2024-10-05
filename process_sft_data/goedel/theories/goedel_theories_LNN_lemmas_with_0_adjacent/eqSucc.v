Require Import Arith.
Require Import Ensembles.
Require Import Coq.Lists.List.
Require Export Languages.
Require Import folProof.
Require Import folProp.
Require Import folLogic3.
Definition Formula := Formula LNN.
Definition Formulas := Formulas LNN.
Definition System := System LNN.
Definition Sentence := Sentence LNN.
Definition Term := Term LNN.
Definition Terms := Terms LNN.
Definition var := var LNN.
Definition equal := equal LNN.
Definition impH := impH LNN.
Definition notH := notH LNN.
Definition iffH := iffH LNN.
Definition forallH := forallH LNN.
Definition orH := orH LNN.
Definition andH := andH LNN.
Definition existH := existH LNN.
Definition ifThenElseH := ifThenElseH LNN.
Definition SysPrf := SysPrf LNN.
Definition Plus (x y : Term) : Term := apply LNN Plus (Tcons LNN 1 x (Tcons LNN 0 y (Tnil LNN))).
Definition Times (x y : Term) : Term := apply LNN Times (Tcons LNN 1 x (Tcons LNN 0 y (Tnil LNN))).
Definition Succ (x : Term) : Term := apply LNN Succ (Tcons LNN 0 x (Tnil LNN)).
Definition Zero : Term := apply LNN Zero (Tnil LNN).
Definition LT (x y : Term) : Formula := atomic LNN LT (Tcons LNN 1 x (Tcons LNN 0 y (Tnil LNN))).
Section Free_Variables.
End Free_Variables.
Section Logic.
End Logic.
Fixpoint natToTerm (n : nat) : Term := match n with | O => Zero | S m => Succ (natToTerm m) end.

Lemma eqSucc : forall (T : System) (a b : Term), SysPrf T (equal a b) -> SysPrf T (equal (Succ a) (Succ b)).
Proof.
intros.
unfold Succ in |- *.
apply (equalFunction LNN).
simpl in |- *.
induction (consTerms LNN 0 (Tcons LNN 0 a (Tnil LNN))).
induction x as (a0, b0).
simpl in |- *.
induction (consTerms LNN 0 (Tcons LNN 0 b (Tnil LNN))).
induction x as (a1, b1).
simpl in |- *.
repeat split.
simpl in p.
inversion p.
simpl in p0.
inversion p0.
apply H.
