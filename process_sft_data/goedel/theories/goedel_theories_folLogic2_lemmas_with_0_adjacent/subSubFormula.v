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

Lemma subSubFormula : forall (f : Formula) (v1 v2 : nat) (s1 s2 : Term), v1 <> v2 -> ~ In v1 (freeVarTerm L s2) -> forall T : System, SysPrf T (iffH (substituteFormula L (substituteFormula L f v1 s1) v2 s2) (substituteFormula L (substituteFormula L f v2 s2) v1 (substituteTerm L s1 v2 s2))).
Proof.
intros.
apply (sysExtend L) with (Empty_set Formula).
unfold Included in |- *.
intros.
induction H1.
elim f using Formula_depth_ind2; intros.
repeat rewrite (subFormulaEqual L).
rewrite subSubTerm; auto.
rewrite (subSubTerm t0); auto.
apply (iffRefl L).
repeat rewrite (subFormulaRelation L).
rewrite subSubTerms; auto.
apply (iffRefl L).
repeat rewrite (subFormulaImp L).
apply (reduceImp L); auto.
repeat rewrite (subFormulaNot L).
apply (reduceNot L); auto.
set (v' := newVar (v1 :: v2 :: freeVarFormula L (fol.forallH L v a) ++ freeVarTerm L s1 ++ freeVarTerm L s2)) in *.
assert (v' <> v1).
unfold not in |- *; intros.
elim (newVar1 (v1 :: v2 :: freeVarFormula L (fol.forallH L v a) ++ freeVarTerm L s1 ++ freeVarTerm L s2)).
fold v' in |- *.
simpl in |- *.
auto.
assert (v' <> v2).
unfold not in |- *; intros.
elim (newVar1 (v1 :: v2 :: freeVarFormula L (fol.forallH L v a) ++ freeVarTerm L s1 ++ freeVarTerm L s2)).
fold v' in |- *.
simpl in |- *.
auto.
assert (~ In v' (freeVarFormula L (fol.forallH L v a))).
unfold not in |- *; intros.
elim (newVar1 (v1 :: v2 :: freeVarFormula L (fol.forallH L v a) ++ freeVarTerm L s1 ++ freeVarTerm L s2)).
fold v' in |- *.
simpl in |- *.
auto with datatypes.
assert (~ In v' (freeVarTerm L s1)).
unfold not in |- *; intros.
elim (newVar1 (v1 :: v2 :: freeVarFormula L (fol.forallH L v a) ++ freeVarTerm L s1 ++ freeVarTerm L s2)).
fold v' in |- *.
simpl in |- *.
repeat right.
auto with datatypes.
assert (~ In v' (freeVarTerm L s2)).
unfold not in |- *; intros.
elim (newVar1 (v1 :: v2 :: freeVarFormula L (fol.forallH L v a) ++ freeVarTerm L s1 ++ freeVarTerm L s2)).
fold v' in |- *.
simpl in |- *.
repeat right.
auto with datatypes.
apply impE with (iffH (substituteFormula L (substituteFormula L (fol.forallH L v' (substituteFormula L a v (var v'))) v1 s1) v2 s2) (substituteFormula L (substituteFormula L (fol.forallH L v' (substituteFormula L a v (var v'))) v2 s2) v1 (substituteTerm L s1 v2 s2))).
apply (iffE2 L).
assert (folProof.SysPrf L (Empty_set Formula) (iffH (fol.forallH L v a) (fol.forallH L v' (substituteFormula L a v (var v'))))).
apply rebindForall.
auto.
repeat first [ apply (reduceIff L) | apply (reduceSub L) | apply (notInFreeVarSys L) ]; auto.
assert (forall (f : Formula) (x v : nat) (s : Term), x <> v -> ~ In x (freeVarTerm L s) -> substituteFormula L (forallH x f) v s = forallH x (substituteFormula L f v s)).
intros.
rewrite (subFormulaForall L).
induction (eq_nat_dec x v0).
elim H7; auto.
induction (In_dec eq_nat_dec x (freeVarTerm L s)).
elim H8; auto.
reflexivity.
repeat rewrite H7; auto.
apply (reduceForall L).
apply (notInFreeVarSys L).
apply H1.
apply eqDepth with a.
symmetry in |- *.
apply subFormulaDepth.
apply depthForall.
unfold not in |- *; intros.
induction (freeVarSubTerm3 _ _ _ _ _ H8).
elim H5.
eapply In_list_remove1.
apply H9.
auto.
