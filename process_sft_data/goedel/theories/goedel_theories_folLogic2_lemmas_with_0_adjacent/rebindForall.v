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

Lemma rebindForall : forall (T : System) (a b : nat) (f : Formula), ~ In b (freeVarFormula L (forallH a f)) -> SysPrf T (iffH (forallH a f) (forallH b (substituteFormula L f a (var b)))).
Proof.
intros.
eapply (sysExtend L) with (Empty_set Formula).
unfold Included in |- *.
intros.
induction H0.
apply (iffI L).
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H0 as (x, H0); induction H0 as (H0, H1).
induction H1 as [x H1| x H1]; [ induction H1 | induction H1 ].
auto.
apply forallE.
apply Axm; right; constructor.
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H0 as (x, H0); induction H0 as (H0, H1).
induction H1 as [x H1| x H1]; [ induction H1 | induction H1 ].
assert (In a (freeVarFormula L (substituteFormula L f a (var b)))).
eapply In_list_remove1.
apply H0.
induction (freeVarSubFormula3 _ _ _ _ _ H1).
elim (In_list_remove2 _ _ _ _ _ H2).
auto.
elim (In_list_remove2 _ _ _ _ _ H0).
induction H2 as [H2| H2].
auto.
elim H2.
set (A1 := forallH b (substituteFormula L f a (var b))) in *.
rewrite <- (subFormulaId L f a).
apply (impE L) with (substituteFormula L (substituteFormula L f a (var b)) b (fol.var L a)).
apply (iffE1 L).
apply (subFormulaTrans L).
apply H.
apply forallE.
apply Axm; right; constructor.
