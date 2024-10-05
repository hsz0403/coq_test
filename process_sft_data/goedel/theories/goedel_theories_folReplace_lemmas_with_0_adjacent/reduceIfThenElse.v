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

Lemma reduceIfThenElse : forall (f1 f2 f3 f4 f5 f6 : Formula) (T : System), SysPrf T (iffH f1 f4) -> SysPrf T (iffH f2 f5) -> SysPrf T (iffH f3 f6) -> SysPrf T (iffH (ifThenElseH f1 f2 f3) (ifThenElseH f4 f5 f6)).
Proof.
intros.
unfold ifThenElseH, fol.ifThenElseH in |- *.
apply reduceAnd; apply reduceImp; auto.
apply reduceNot; auto.
