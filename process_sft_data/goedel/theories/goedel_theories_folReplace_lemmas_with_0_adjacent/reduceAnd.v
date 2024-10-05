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

Lemma reduceAnd : forall (f1 f2 f3 f4 : Formula) (T : System), SysPrf T (iffH f1 f3) -> SysPrf T (iffH f2 f4) -> SysPrf T (iffH (andH f1 f2) (andH f3 f4)).
Proof.
assert (forall (f1 f2 f3 f4 : Formula) (T : System), SysPrf T (iffH f1 f3) -> SysPrf T (iffH f2 f4) -> SysPrf T (impH (andH f1 f2) (andH f3 f4))).
intros.
apply (impI L).
apply (andI L).
apply impE with f1.
apply sysWeaken.
apply (iffE1 L).
assumption.
eapply (andE1 L).
apply Axm; right; constructor.
apply impE with f2.
apply sysWeaken.
apply (iffE1 L).
assumption.
eapply (andE2 L).
apply Axm; right; constructor.
intros.
apply (iffI L).
apply H; auto.
apply H; apply (iffSym L); auto.
