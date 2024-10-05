Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import ListExt.
Require Import folProp.
Require Import folProof.
Require Export folLogic2.
Require Import subProp.
Require Import folReplace.
Require Import Arith.
Require Import subAll.
Require Import misc.
Section Equality_Logic_Rules.
Variable L : Language.
Notation Formula := (Formula L) (only parsing).
Notation Formulas := (Formulas L) (only parsing).
Notation System := (System L) (only parsing).
Notation Term := (Term L) (only parsing).
Notation Terms := (Terms L) (only parsing).
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
Fixpoint PairwiseEqual (T : fol.System L) (n : nat) {struct n} : fol.Terms L n -> fol.Terms L n -> Prop := match n return (fol.Terms L n -> fol.Terms L n -> Prop) with | O => fun ts ss : fol.Terms L 0 => True | S x => fun ts ss : fol.Terms L (S x) => let (a, b) := proj1_sig (consTerms L x ts) in let (c, d) := proj1_sig (consTerms L x ss) in SysPrf T (equal a c) /\ PairwiseEqual T x b d end.
Let termsMap (m : nat) (ts ss : fol.Terms L m) : nat -> fol.Term L.
induction m as [| m Hrecm].
exact (fun n : nat => var n).
induction (consTerms L _ ts).
induction x as (a, b).
induction (consTerms L _ ss).
induction x as (a0, b0).
exact (fun n : nat => match eq_nat_dec n (m + m) with | left _ => a | right _ => match eq_nat_dec n (S (m + m)) with | left _ => a0 | right _ => Hrecm b b0 n end end).
Defined.
Remark subAllnVars1 : forall (a : nat) (ts ss : fol.Terms L a), ts = subAllTerms L _ (fst (nVars L a)) (termsMap a ts ss).
Proof.
intros.
induction a as [| a Hreca].
simpl in |- *.
symmetry in |- *.
apply (nilTerms L).
assert (forall v : nat, In v (freeVarTerms L _ (fst (nVars L a))) -> v < a + a).
intros.
clear Hreca ss ts.
induction a as [| a Hreca].
elim H.
simpl in H.
induction (nVars L a).
simpl in H.
induction H as [H| H].
rewrite <- H.
rewrite <- plus_Snm_nSm.
simpl in |- *.
apply lt_S.
apply lt_n_Sn.
rewrite <- plus_Snm_nSm.
apply lt_trans with (a + a).
apply Hreca.
apply H.
simpl in |- *.
apply lt_S.
apply lt_n_Sn.
simpl in |- *.
induction (consTerms L a ts).
induction x as (a0, b).
induction (consTerms L a ss).
induction x as (a1, b0).
simpl in |- *.
simpl in H.
induction (nVars L a).
simpl in |- *.
simpl in Hreca.
induction (eq_nat_dec (a + a) (a + a)).
simpl in p.
rewrite <- p.
replace (subAllTerms L a a2 (fun n : nat => match eq_nat_dec n (a + a) with | left _ => a0 | right _ => match eq_nat_dec n (S (a + a)) with | left _ => a1 | right _ => termsMap a b b0 n end end)) with (subAllTerms L a a2 (termsMap a b b0)).
rewrite <- Hreca.
reflexivity.
apply subAllTerms_ext.
intros.
induction (eq_nat_dec m (a + a)).
elim (lt_not_le m (a + a)).
apply H; auto.
rewrite a4; auto.
induction (eq_nat_dec m (S (a + a))).
elim (lt_not_le m (a + a)).
apply H; auto.
rewrite a4; apply le_n_Sn.
auto.
elim b2; auto.
Remark subAllnVars2 : forall (a : nat) (ts ss : fol.Terms L a), ss = subAllTerms L _ (snd (nVars L a)) (termsMap a ts ss).
Proof.
intros.
induction a as [| a Hreca].
simpl in |- *.
symmetry in |- *.
apply (nilTerms L).
assert (forall v : nat, In v (freeVarTerms L _ (snd (nVars L a))) -> v < a + a).
intros.
clear Hreca ss ts.
induction a as [| a Hreca].
elim H.
simpl in H.
induction (nVars L a).
simpl in H.
induction H as [H| H].
rewrite <- H.
rewrite <- plus_Snm_nSm.
simpl in |- *.
apply lt_n_Sn.
rewrite <- plus_Snm_nSm.
apply lt_trans with (a + a).
apply Hreca.
apply H.
simpl in |- *.
apply lt_S.
apply lt_n_Sn.
simpl in |- *.
induction (consTerms L a ts).
induction x as (a0, b).
induction (consTerms L a ss).
induction x as (a1, b0).
simpl in |- *.
simpl in H.
induction (nVars L a).
Opaque eq_nat_dec.
simpl.
Transparent eq_nat_dec.
destruct (eq_nat_dec (S (a+a)) (a + a)).
elim (n_Sn (a+a)).
auto.
destruct (eq_nat_dec (S (a + a)) (S (a+a))).
replace (subAllTerms L a b1 (fun n : nat => match eq_nat_dec n (a + a) with | left _ => a0 | right _ => match eq_nat_dec n (S (a + a)) with | left _ => a1 | right _ => termsMap a b b0 n end end)) with (subAllTerms L a b1 (termsMap a b b0)).
rewrite <- Hreca.
auto.
apply subAllTerms_ext.
intros.
induction (eq_nat_dec m (a + a)).
elim (lt_not_le m (a + a)).
apply H; auto.
rewrite a3; auto.
induction (eq_nat_dec m (S (a + a))).
elim (lt_not_le m (a + a)).
apply H; auto.
rewrite a3; apply le_n_Sn.
auto.
elim n0; auto.
Remark addPairwiseEquals : forall (T : fol.System L) (n : nat) (ts ss : fol.Terms L n), PairwiseEqual T n ts ss -> forall m0 : nat -> fol.Term L, (forall q : nat, q < n + n -> m0 q = termsMap n ts ss q) -> forall f0 : fol.Formula L, SysPrf T (subAllFormula L (nat_rec (fun _ : nat => fol.Formula L) f0 (fun (n : nat) (Hrecn : fol.Formula L) => fol.impH L (fol.equal L (fol.var L (n + n)) (fol.var L (S (n + n)))) Hrecn) n) m0) -> SysPrf T (subAllFormula L f0 m0).
Proof.
intros T n ts ss H.
set (m := termsMap n ts ss) in *.
induction n as [| n Hrecn].
simpl in |- *.
auto.
simpl in (value of m).
simpl in H.
induction (consTerms L n ts).
induction x as (a, b).
induction (consTerms L n ss).
induction x as (a0, b0).
simpl in H.
simpl in (value of m).
induction H as (H, H0).
simpl in |- *.
intros.
apply (Hrecn b b0).
auto.
intros.
rewrite H1.
unfold m in |- *.
induction (eq_nat_dec q (n + n)).
rewrite <- a1 in H3.
elim (lt_irrefl _ H3).
induction (eq_nat_dec q (S (n + n))).
elim (lt_not_le _ _ H3).
rewrite a1.
apply le_n_Sn.
reflexivity.
rewrite <- plus_Snm_nSm.
simpl in |- *.
repeat apply lt_S.
auto.
apply (impE L) with (fol.equal L (m0 (n + n)) (m0 (S (n + n)))).
apply H2.
rewrite <- plus_Snm_nSm in H1.
repeat rewrite H1.
unfold m in |- *.
induction (eq_nat_dec (n + n) (n + n)).
induction (eq_nat_dec (S (n + n)) (n + n)).
elim (le_not_lt (S (n + n)) (n + n)).
rewrite a2.
auto.
apply lt_n_Sn.
induction (eq_nat_dec (S (n + n)) (S (n + n))).
apply H.
elim b2; auto.
elim b1; auto.
simpl in |- *.
apply lt_n_S.
apply lt_n_Sn.
simpl in |- *.
apply lt_S.
apply lt_n_Sn.
End Equality_Logic_Rules.

Lemma subWithEquals : forall (f : fol.Formula L) (v : nat) (a b : fol.Term L) (T : fol.System L), SysPrf T (equal a b) -> SysPrf T (impH (substituteFormula L f v a) (substituteFormula L f v b)).
Proof.
intro.
elim f using Formula_depth_ind2; intros.
repeat rewrite subFormulaEqual.
apply (impI L).
apply eqTrans with (substituteTerm L t v a).
apply subWithEqualsTerm.
apply (sysWeaken L).
apply eqSym.
auto.
apply eqTrans with (substituteTerm L t0 v a).
apply (Axm L); right; constructor.
apply subWithEqualsTerm.
apply (sysWeaken L).
auto.
apply (iffE1 L).
repeat rewrite subFormulaRelation.
apply equalRelation.
apply subWithEqualsTerms.
auto.
repeat rewrite subFormulaImp.
repeat apply (impI L).
apply impE with (substituteFormula L f1 v a).
apply H0.
repeat apply (sysWeaken L).
auto.
apply impE with (substituteFormula L f0 v a).
apply (Axm L); left; right; constructor.
apply impE with (substituteFormula L f0 v b).
apply H.
repeat apply (sysWeaken L).
apply eqSym.
auto.
apply (Axm L); right; constructor.
repeat rewrite subFormulaNot.
apply (cp2 L).
apply H.
apply eqSym.
auto.
decompose record (subFormulaForall2 L a v v0 a0).
rewrite H5; clear H5.
decompose record (subFormulaForall2 L a v v0 b).
rewrite H8; clear H8.
induction (eq_nat_dec v v0).
apply (impRefl L).
set (nv := v0 :: list_remove nat eq_nat_dec v (freeVarFormula L a) ++ freeVarTerm L a0 ++ freeVarTerm L b) in *.
apply (impTrans L) with (fol.forallH L (newVar nv) (substituteFormula L (substituteFormula L a v (fol.var L (newVar nv))) v0 a0)).
apply sysExtend with (Empty_set (fol.Formula L)).
unfold Included in |- *; intros.
induction H7.
apply (impTrans L) with (fol.forallH L (newVar nv) (substituteFormula L (substituteFormula L (substituteFormula L a v (fol.var L x)) v0 a0) x (var (newVar nv)))).
apply (iffE1 L).
apply (rebindForall L).
unfold not in |- *; intros.
elim (newVar1 nv).
unfold nv at 2 in |- *.
assert (In (newVar nv) (freeVarFormula L (substituteFormula L (substituteFormula L a v (fol.var L x)) v0 a0))).
eapply In_list_remove1.
apply H7.
induction (freeVarSubFormula3 _ _ _ _ _ H8).
assert (In (newVar nv) (freeVarFormula L (substituteFormula L a v (fol.var L x)))).
eapply In_list_remove1.
apply H9.
induction (freeVarSubFormula3 _ _ _ _ _ H10).
right.
apply in_or_app.
auto.
elim (In_list_remove2 _ _ _ _ _ H7).
induction H11 as [H11| H11].
auto.
contradiction.
right.
auto with datatypes.
apply (iffE1 L).
apply (reduceForall L).
apply (notInFreeVarSys L).
apply (iffTrans L) with (substituteFormula L (substituteFormula L (substituteFormula L a v (fol.var L x)) x (var (newVar nv))) v0 a0).
apply (subFormulaExch L); auto.
unfold not in |- *; intros.
elim (newVar1 nv).
unfold nv at 2 in |- *.
simpl in |- *.
left.
induction H7 as [H7| H7].
auto.
contradiction.
apply (reduceSub L).
apply (notInFreeVarSys L).
apply (subFormulaTrans L).
auto.
apply (impTrans L) with (fol.forallH L (newVar nv) (substituteFormula L (substituteFormula L a v (fol.var L (newVar nv))) v0 b)).
apply impE with (equal a0 b).
apply sysExtend with (Empty_set (fol.Formula L)).
unfold Included in |- *; intros.
induction H7.
repeat apply (impI L).
apply forallI.
unfold not in |- *; intros.
induction H7 as (x1, H7); induction H7 as (H7, H8).
induction H8 as [x1 H8| x1 H8]; [ induction H8 as [x1 H8| x1 H8] | induction H8 ].
induction H8; simple induction H8.
induction H8.
simpl in H7.
elim (newVar1 nv).
unfold nv at 2 in |- *.
right.
auto with datatypes.
elim (In_list_remove2 _ _ _ _ _ H7).
reflexivity.
apply impE with (substituteFormula L (substituteFormula L a v (fol.var L (newVar nv))) v0 a0).
apply H.
eapply eqDepth.
symmetry in |- *.
apply (subFormulaDepth L).
apply depthForall.
apply (Axm L); left; right; constructor.
eapply forallSimp.
apply (Axm L); right; constructor.
apply H0.
apply sysExtend with (Empty_set (fol.Formula L)).
unfold Included in |- *; intros.
induction H7.
apply (iffE2 L).
apply (iffTrans L) with (fol.forallH L (newVar nv) (substituteFormula L (substituteFormula L (substituteFormula L a v (fol.var L x0)) v0 b) x0 (var (newVar nv)))).
apply (rebindForall L).
unfold not in |- *; intros.
elim (newVar1 nv).
unfold nv at 2 in |- *.
assert (In (newVar nv) (freeVarFormula L (substituteFormula L (substituteFormula L a v (fol.var L x0)) v0 b))).
eapply In_list_remove1.
apply H7.
induction (freeVarSubFormula3 _ _ _ _ _ H8).
assert (In (newVar nv) (freeVarFormula L (substituteFormula L a v (fol.var L x0)))).
eapply In_list_remove1.
apply H9.
induction (freeVarSubFormula3 _ _ _ _ _ H10).
right.
apply in_or_app.
auto.
elim (In_list_remove2 _ _ _ _ _ H7).
induction H11 as [H11| H11].
auto.
contradiction.
right.
auto with datatypes.
apply (reduceForall L).
apply (notInFreeVarSys L).
apply (iffTrans L) with (substituteFormula L (substituteFormula L (substituteFormula L a v (fol.var L x0)) x0 (var (newVar nv))) v0 b).
apply (subFormulaExch L); auto.
unfold not in |- *; intros.
elim (newVar1 nv).
unfold nv at 2 in |- *.
simpl in |- *.
left.
induction H7 as [H7| H7].
auto.
contradiction.
apply (reduceSub L).
apply (notInFreeVarSys L).
apply (subFormulaTrans L).
auto.
