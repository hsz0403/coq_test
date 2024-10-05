Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Peano_dec.
Require Import ListExt.
Require Import folProof.
Require Import folLogic.
Require Import folProp.
Section Replacement.
Variable L : Language.
Let Formula := Formula L.
Let Formulas := Formulas L.
Let System := System L.
Let Term := Term L.
Let Terms := Terms L.
Let var := var L.
Let apply := apply L.
Let equal := equal L.
Let atomic := atomic L.
Let impH := impH L.
Let notH := notH L.
Let forallH := forallH L.
Let orH := orH L.
Let andH := andH L.
Let existH := existH L.
Let iffH := iffH L.
Let ifThenElseH := ifThenElseH L.
Let SysPrf := SysPrf L.
End Replacement.

Lemma reduceNot : forall (f1 f2 : Formula) (T : System), SysPrf T (iffH f1 f2) -> SysPrf T (iffH (notH f1) (notH f2)).
Proof.
assert (forall (f1 f2 : Formula) (T : System), SysPrf T (iffH f1 f2) -> SysPrf T (impH (notH f1) (notH f2))).
intros.
apply (cp2 L).
apply (iffE2 L).
apply H.
intros.
apply (iffI L).
apply H.
assumption.
apply H.
apply (iffSym L).
assumption.
