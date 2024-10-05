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

Lemma iffI : forall (T : System) (f g : Formula), SysPrf T (impH f g) -> SysPrf T (impH g f) -> SysPrf T (iffH f g).
Proof.
Admitted.

Lemma iffE1 : forall (T : System) (f g : Formula), SysPrf T (iffH f g) -> SysPrf T (impH f g).
Proof.
Admitted.

Lemma iffE2 : forall (T : System) (f g : Formula), SysPrf T (iffH f g) -> SysPrf T (impH g f).
Proof.
Admitted.

Lemma forallI : forall (T : System) (f : Formula) (v : nat), ~ In_freeVarSys LNT v T -> SysPrf T f -> SysPrf T (forallH v f).
Proof.
Admitted.

Lemma forallE : forall (T : System) (f : Formula) (v : nat) (t : Term), SysPrf T (forallH v f) -> SysPrf T (substituteFormula LNT f v t).
Proof.
Admitted.

Lemma forallSimp : forall (T : System) (f : Formula) (v : nat), SysPrf T (forallH v f) -> SysPrf T f.
Proof.
Admitted.

Lemma existI : forall (T : System) (f : Formula) (v : nat) (t : Term), SysPrf T (substituteFormula LNT f v t) -> SysPrf T (existH v f).
Proof.
Admitted.

Lemma existE : forall (T : System) (f g : Formula) (v : nat), ~ In_freeVarSys LNT v T -> ~ In v (freeVarFormula LNT g) -> SysPrf T (existH v f) -> SysPrf T (impH f g) -> SysPrf T g.
Proof.
Admitted.

Lemma existSimp : forall (T : System) (f : Formula) (v : nat), SysPrf T f -> SysPrf T (existH v f).
Proof.
Admitted.

Lemma existSys : forall (T : System) (f g : Formula) (v : nat), ~ In_freeVarSys LNT v T -> ~ In v (freeVarFormula LNT g) -> SysPrf (Ensembles.Add _ T f) g -> SysPrf (Ensembles.Add _ T (existH v f)) g.
Proof.
Admitted.

Lemma nImp : forall (T : System) (f g : Formula), SysPrf T (andH f (notH g)) -> SysPrf T (notH (impH f g)).
Proof.
Admitted.

Lemma nOr : forall (T : System) (f g : Formula), SysPrf T (andH (notH f) (notH g)) -> SysPrf T (notH (orH f g)).
Proof.
Admitted.

Lemma nAnd : forall (T : System) (f g : Formula), SysPrf T (orH (notH f) (notH g)) -> SysPrf T (notH (andH f g)).
Proof.
Admitted.

Lemma nForall : forall (T : System) (f : Formula) (v : nat), SysPrf T (existH v (notH f)) -> SysPrf T (notH (forallH v f)).
Proof.
Admitted.

Lemma nExist : forall (T : System) (f : Formula) (v : nat), SysPrf T (forallH v (notH f)) -> SysPrf T (notH (existH v f)).
Proof.
Admitted.

Lemma impRefl : forall (T : System) (f : Formula), SysPrf T (impH f f).
Proof.
Admitted.

Lemma impTrans : forall (T : System) (f g h : Formula), SysPrf T (impH f g) -> SysPrf T (impH g h) -> SysPrf T (impH f h).
Proof.
Admitted.

Lemma orSym : forall (T : System) (f g : Formula), SysPrf T (orH f g) -> SysPrf T (orH g f).
Proof.
Admitted.

Lemma andSym : forall (T : System) (f g : Formula), SysPrf T (andH f g) -> SysPrf T (andH g f).
Proof.
Admitted.

Lemma iffRefl : forall (T : System) (f : Formula), SysPrf T (iffH f f).
Proof.
Admitted.

Lemma absurd1 : forall (T : System) (f : Formula), SysPrf T (impH f (notH f)) -> SysPrf T (notH f).
Proof.
apply (absurd1 LNT).
