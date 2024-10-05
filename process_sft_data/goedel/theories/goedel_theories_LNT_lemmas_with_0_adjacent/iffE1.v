Require Import Arith.
Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Languages.
Require Import folProof.
Require Import folProp.
Require Import folLogic3.
Definition Formula := Formula LNT.
Definition Formulas := Formulas LNT.
Definition System := System LNT.
Definition Sentence := Sentence LNT.
Definition Term := Term LNT.
Definition Terms := Terms LNT.
Definition var := var LNT.
Definition equal := equal LNT.
Definition impH := impH LNT.
Definition notH := notH LNT.
Definition iffH := iffH LNT.
Definition forallH := forallH LNT.
Definition orH := orH LNT.
Definition andH := andH LNT.
Definition existH := existH LNT.
Definition ifThenElseH := ifThenElseH LNT.
Definition SysPrf := SysPrf LNT.
Definition Plus (x y : Term) : Term := apply LNT Plus (Tcons LNT 1 x (Tcons LNT 0 y (Tnil LNT))).
Definition Times (x y : Term) : Term := apply LNT Times (Tcons LNT 1 x (Tcons LNT 0 y (Tnil LNT))).
Definition Succ (x : Term) : Term := apply LNT Succ (Tcons LNT 0 x (Tnil LNT)).
Definition Zero : Term := apply LNT Zero (Tnil LNT).
Section Free_Variables.
End Free_Variables.
Section Logic.
End Logic.
Fixpoint natToTerm (n : nat) : Term := match n with | O => Zero | S m => Succ (natToTerm m) end.

Lemma iffE1 : forall (T : System) (f g : Formula), SysPrf T (iffH f g) -> SysPrf T (impH f g).
Proof.
apply (iffE1 LNT).
