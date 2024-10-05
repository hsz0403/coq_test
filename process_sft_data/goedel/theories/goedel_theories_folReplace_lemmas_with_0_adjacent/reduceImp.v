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

Lemma reduceImp : forall (f1 f2 f3 f4 : Formula) (T : System), SysPrf T (iffH f1 f3) -> SysPrf T (iffH f2 f4) -> SysPrf T (iffH (impH f1 f2) (impH f3 f4)).
Proof.
assert (forall (f1 f2 f3 f4 : Formula) (T : System), SysPrf T (iffH f1 f3) -> SysPrf T (iffH f2 f4) -> SysPrf T (impH (impH f1 f2) (impH f3 f4))).
intros.
repeat apply (impI L).
apply impE with f2.
repeat apply sysWeaken.
apply (iffE1 L).
apply H0.
apply impE with f1.
apply sysWeaken.
apply Axm; right; constructor.
apply impE with f3.
repeat apply sysWeaken.
apply (iffE2 L).
apply H.
apply Axm; right; constructor.
intros.
apply (iffI L).
apply H; auto.
apply H; apply (iffSym L); auto.
