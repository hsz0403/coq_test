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

Lemma iffE1 : forall (T : System) (f g : Formula), SysPrf T (iffH f g) -> SysPrf T (impH f g).
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

Lemma orI2 : forall (T : System) (f g : Formula), SysPrf T g -> SysPrf T (orH f g).
Proof.
apply (orI2 LNN).
