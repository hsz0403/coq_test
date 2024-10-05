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

Lemma existE : forall (T : System) (f g : Formula) (v : nat), ~ In_freeVarSys LNT v T -> ~ In v (freeVarFormula LNT g) -> SysPrf T (existH v f) -> SysPrf T (impH f g) -> SysPrf T g.
Proof.
Admitted.

Lemma existSimp : forall (T : System) (f : Formula) (v : nat), SysPrf T f -> SysPrf T (existH v f).
Proof.
Admitted.

Lemma existSys : forall (T : System) (f g : Formula) (v : nat), ~ In_freeVarSys LNT v T -> ~ In v (freeVarFormula LNT g) -> SysPrf (Ensembles.Add _ T f) g -> SysPrf (Ensembles.Add _ T (existH v f)) g.
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

Lemma iffTrans : forall (T : System) (f g h : Formula), SysPrf T (iffH f g) -> SysPrf T (iffH g h) -> SysPrf T (iffH f h).
Proof.
Admitted.

Lemma eqRefl : forall (T : System) (a : Term), SysPrf T (equal a a).
Proof.
Admitted.

Lemma eqSym : forall (T : System) (a b : Term), SysPrf T (equal a b) -> SysPrf T (equal b a).
Proof.
Admitted.

Lemma eqTrans : forall (T : System) (a b c : Term), SysPrf T (equal a b) -> SysPrf T (equal b c) -> SysPrf T (equal a c).
Proof.
Admitted.

Lemma eqPlus : forall (T : System) (a b c d : Term), SysPrf T (equal a b) -> SysPrf T (equal c d) -> SysPrf T (equal (Plus a c) (Plus b d)).
Proof.
intros.
unfold Plus in |- *.
apply (equalFunction LNT).
simpl in |- *.
induction (consTerms LNT 1 (Tcons LNT 1 a (Tcons LNT 0 c (Tnil LNT)))).
induction x as (a0, b0).
simpl in |- *.
induction (consTerms LNT 1 (Tcons LNT 1 b (Tcons LNT 0 d (Tnil LNT)))).
induction x as (a1, b1).
simpl in |- *.
induction (consTerms LNT 0 b0).
induction x as (a2, b2).
simpl in |- *.
induction (consTerms LNT 0 b1).
induction x as (a3, b3).
simpl in |- *.
repeat split.
simpl in p.
inversion p.
simpl in p0.
inversion p0.
apply H.
simpl in p.
inversion p.
rewrite <- p1 in H3.
simpl in H3.
inversion H3.
simpl in p0.
inversion p0.
rewrite <- p2 in H7.
inversion H7.
Admitted.

Lemma eqSucc : forall (T : System) (a b : Term), SysPrf T (equal a b) -> SysPrf T (equal (Succ a) (Succ b)).
Proof.
intros.
unfold Succ in |- *.
apply (equalFunction LNT).
simpl in |- *.
induction (consTerms LNT 0 (Tcons LNT 0 a (Tnil LNT))).
induction x as (a0, b0).
simpl in |- *.
induction (consTerms LNT 0 (Tcons LNT 0 b (Tnil LNT))).
induction x as (a1, b1).
simpl in |- *.
repeat split.
simpl in p.
inversion p.
simpl in p0.
inversion p0.
Admitted.

Lemma closedNatToTerm : forall a v : nat, ~ In v (freeVarTerm LNT (natToTerm a)).
Proof.
intros.
induction a as [| a Hreca].
auto.
simpl in |- *.
rewrite freeVarSucc.
Admitted.

Lemma eqTimes : forall (T : System) (a b c d : Term), SysPrf T (equal a b) -> SysPrf T (equal c d) -> SysPrf T (equal (Times a c) (Times b d)).
Proof.
intros.
unfold Times in |- *.
apply (equalFunction LNT).
simpl in |- *.
induction (consTerms LNT 1 (Tcons LNT 1 a (Tcons LNT 0 c (Tnil LNT)))).
induction x as (a0, b0).
simpl in |- *.
induction (consTerms LNT 1 (Tcons LNT 1 b (Tcons LNT 0 d (Tnil LNT)))).
induction x as (a1, b1).
simpl in |- *.
induction (consTerms LNT 0 b0).
induction x as (a2, b2).
simpl in |- *.
induction (consTerms LNT 0 b1).
induction x as (a3, b3).
simpl in |- *.
repeat split.
simpl in p.
inversion p.
simpl in p0.
inversion p0.
apply H.
simpl in p.
inversion p.
rewrite <- p1 in H3.
simpl in H3.
inversion H3.
simpl in p0.
inversion p0.
rewrite <- p2 in H7.
inversion H7.
apply H0.
