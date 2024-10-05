Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import ListExt.
Require Import folProp.
Require Import folProof.
Require Export folLogic.
Require Import subProp.
Require Import folReplace.
Require Import Arith.
Section More_Logic_Rules.
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
Let Prf := Prf L.
Let SysPrf := SysPrf L.
End More_Logic_Rules.

Lemma rebindExist : forall (T : System) (a b : nat) (f : Formula), ~ In b (freeVarFormula L (existH a f)) -> SysPrf T (iffH (existH a f) (existH b (substituteFormula L f a (var b)))).
Proof.
intros.
unfold existH in |- *.
unfold fol.existH in |- *.
apply (reduceNot L).
eapply (iffTrans L).
apply (rebindForall T a b (notH f)).
apply H.
rewrite (subFormulaNot L).
apply (iffRefl L).
