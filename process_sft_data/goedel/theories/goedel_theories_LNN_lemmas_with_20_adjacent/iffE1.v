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

Lemma freeVarLT : forall x y : Term, freeVarFormula LNN (LT x y) = freeVarTerm LNN x ++ freeVarTerm LNN y.
Proof.
intros.
rewrite (app_nil_end (freeVarTerm LNN y)).
Admitted.

Lemma Axm : forall (T : System) (f : Formula), mem _ T f -> SysPrf T f.
Proof.
Admitted.

Lemma sysExtend : forall (T U : System) (f : Formula), Included _ T U -> SysPrf T f -> SysPrf U f.
Proof.
Admitted.

Lemma sysWeaken : forall (T : System) (f g : Formula), SysPrf T f -> SysPrf (Ensembles.Add _ T g) f.
Proof.
Admitted.

Lemma impI : forall (T : System) (f g : Formula), SysPrf (Ensembles.Add _ T g) f -> SysPrf T (impH g f).
Proof.
Admitted.

Lemma impE : forall (T : System) (f g : Formula), SysPrf T (impH g f) -> SysPrf T g -> SysPrf T f.
Proof.
Admitted.

Lemma contradiction : forall (T : System) (f g : Formula), SysPrf T f -> SysPrf T (notH f) -> SysPrf T g.
Proof.
Admitted.

Lemma nnE : forall (T : System) (f : Formula), SysPrf T (notH (notH f)) -> SysPrf T f.
Proof.
Admitted.

Lemma noMiddle : forall (T : System) (f : Formula), SysPrf T (orH (notH f) f).
Proof.
Admitted.

Lemma nnI : forall (T : System) (f : Formula), SysPrf T f -> SysPrf T (notH (notH f)).
Proof.
Admitted.

Lemma cp1 : forall (T : System) (f g : Formula), SysPrf T (impH (notH f) (notH g)) -> SysPrf T (impH g f).
Proof.
Admitted.

Lemma cp2 : forall (T : System) (f g : Formula), SysPrf T (impH g f) -> SysPrf T (impH (notH f) (notH g)).
Proof.
Admitted.

Lemma orI1 : forall (T : System) (f g : Formula), SysPrf T f -> SysPrf T (orH f g).
Proof.
Admitted.

Lemma orI2 : forall (T : System) (f g : Formula), SysPrf T g -> SysPrf T (orH f g).
Proof.
Admitted.

Lemma orE : forall (T : System) (f g h : Formula), SysPrf T (orH f g) -> SysPrf T (impH f h) -> SysPrf T (impH g h) -> SysPrf T h.
Proof.
Admitted.

Lemma orSys : forall (T : System) (f g h : Formula), SysPrf (Ensembles.Add _ T f) h -> SysPrf (Ensembles.Add _ T g) h -> SysPrf (Ensembles.Add _ T (orH f g)) h.
Proof.
Admitted.

Lemma andI : forall (T : System) (f g : Formula), SysPrf T f -> SysPrf T g -> SysPrf T (andH f g).
Proof.
Admitted.

Lemma andE1 : forall (T : System) (f g : Formula), SysPrf T (andH f g) -> SysPrf T f.
Proof.
Admitted.

Lemma andE2 : forall (T : System) (f g : Formula), SysPrf T (andH f g) -> SysPrf T g.
Proof.
Admitted.

Lemma iffI : forall (T : System) (f g : Formula), SysPrf T (impH f g) -> SysPrf T (impH g f) -> SysPrf T (iffH f g).
Proof.
Admitted.

Lemma iffE2 : forall (T : System) (f g : Formula), SysPrf T (iffH f g) -> SysPrf T (impH g f).
Proof.
Admitted.

Lemma forallI : forall (T : System) (f : Formula) (v : nat), ~ In_freeVarSys LNN v T -> SysPrf T f -> SysPrf T (forallH v f).
Proof.
Admitted.

Lemma forallE : forall (T : System) (f : Formula) (v : nat) (t : Term), SysPrf T (forallH v f) -> SysPrf T (substituteFormula LNN f v t).
Proof.
Admitted.

Lemma forallSimp : forall (T : System) (f : Formula) (v : nat), SysPrf T (forallH v f) -> SysPrf T f.
Proof.
Admitted.

Lemma existI : forall (T : System) (f : Formula) (v : nat) (t : Term), SysPrf T (substituteFormula LNN f v t) -> SysPrf T (existH v f).
Proof.
Admitted.

Lemma existE : forall (T : System) (f g : Formula) (v : nat), ~ In_freeVarSys LNN v T -> ~ In v (freeVarFormula LNN g) -> SysPrf T (existH v f) -> SysPrf T (impH f g) -> SysPrf T g.
Proof.
Admitted.

Lemma existSimp : forall (T : System) (f : Formula) (v : nat), SysPrf T f -> SysPrf T (existH v f).
Proof.
Admitted.

Lemma existSys : forall (T : System) (f g : Formula) (v : nat), ~ In_freeVarSys LNN v T -> ~ In v (freeVarFormula LNN g) -> SysPrf (Ensembles.Add _ T f) g -> SysPrf (Ensembles.Add _ T (existH v f)) g.
Proof.
Admitted.

Lemma absurd1 : forall (T : System) (f : Formula), SysPrf T (impH f (notH f)) -> SysPrf T (notH f).
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

Lemma iffSym : forall (T : System) (f g : Formula), SysPrf T (iffH f g) -> SysPrf T (iffH g f).
Proof.
Admitted.

Lemma iffE1 : forall (T : System) (f g : Formula), SysPrf T (iffH f g) -> SysPrf T (impH f g).
Proof.
apply (iffE1 LNN).
