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

Lemma reduceSub : forall (T : System) (v : nat) (s : Term) (f g : Formula), ~ In_freeVarSys L v T -> SysPrf T (iffH f g) -> SysPrf T (iffH (substituteFormula L f v s) (substituteFormula L g v s)).
Proof.
assert (forall (T : System) (v : nat) (s : Term) (f g : Formula), ~ In_freeVarSys L v T -> SysPrf T (iffH f g) -> SysPrf T (impH (substituteFormula L f v s) (substituteFormula L g v s))).
intros.
rewrite <- (subFormulaImp L).
apply (forallE L).
apply forallI.
assumption.
apply (iffE1 L).
apply H0.
intros.
apply (iffI L).
apply H; auto.
apply H; auto.
apply (iffSym L).
auto.
