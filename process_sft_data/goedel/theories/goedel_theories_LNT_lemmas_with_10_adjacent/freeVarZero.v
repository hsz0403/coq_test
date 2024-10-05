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

Lemma LNT_dec : language_decideable LNT.
Proof.
unfold language_decideable in |- *.
Admitted.

Lemma freeVarPlus : forall x y : Term, freeVarTerm LNT (Plus x y) = freeVarTerm LNT x ++ freeVarTerm LNT y.
Proof.
intros.
rewrite (app_nil_end (freeVarTerm LNT y)).
Admitted.

Lemma freeVarTimes : forall x y : Term, freeVarTerm LNT (Times x y) = freeVarTerm LNT x ++ freeVarTerm LNT y.
Proof.
intros.
rewrite (app_nil_end (freeVarTerm LNT y)).
Admitted.

Lemma freeVarSucc : forall x : Term, freeVarTerm LNT (Succ x) = freeVarTerm LNT x.
Proof.
intros.
rewrite (app_nil_end (freeVarTerm LNT x)).
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

Lemma freeVarZero : freeVarTerm LNT Zero = nil.
Proof.
reflexivity.
