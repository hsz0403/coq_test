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

Lemma LNN_dec : language_decideable LNN.
Proof.
unfold language_decideable in |- *.
Admitted.

Lemma freeVarPlus : forall x y : Term, freeVarTerm LNN (Plus x y) = freeVarTerm LNN x ++ freeVarTerm LNN y.
Proof.
intros.
rewrite (app_nil_end (freeVarTerm LNN y)).
Admitted.

Lemma freeVarTimes : forall x y : Term, freeVarTerm LNN (Times x y) = freeVarTerm LNN x ++ freeVarTerm LNN y.
Proof.
intros.
rewrite (app_nil_end (freeVarTerm LNN y)).
Admitted.

Lemma freeVarSucc : forall x : Term, freeVarTerm LNN (Succ x) = freeVarTerm LNN x.
Proof.
intros.
rewrite (app_nil_end (freeVarTerm LNN x)).
Admitted.

Lemma freeVarZero : freeVarTerm LNN Zero = nil.
Proof.
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

Lemma freeVarLT : forall x y : Term, freeVarFormula LNN (LT x y) = freeVarTerm LNN x ++ freeVarTerm LNN y.
Proof.
intros.
rewrite (app_nil_end (freeVarTerm LNN y)).
reflexivity.
