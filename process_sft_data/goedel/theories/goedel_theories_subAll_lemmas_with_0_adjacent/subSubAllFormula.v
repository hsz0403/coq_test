Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import Peano_dec.
Require Import ListExt.
Require Import Max.
Require Import folProof.
Require Import folLogic2.
Require Import folProp.
Require Import folReplace.
Require Import subProp.
Section SubAllVars.
Variable L : Language.
Notation Formula := (Formula L) (only parsing).
Notation Formulas := (Formulas L) (only parsing).
Notation System := (System L) (only parsing).
Notation Term := (Term L) (only parsing).
Notation Terms := (Terms L) (only parsing).
Notation var := (var L) (only parsing).
Notation apply := (apply L) (only parsing).
Notation equal := (equal L) (only parsing).
Notation atomic := (atomic L) (only parsing).
Notation impH := (impH L) (only parsing).
Notation notH := (notH L) (only parsing).
Notation forallH := (forallH L) (only parsing).
Notation iffH := (iffH L) (only parsing).
Notation SysPrf := (SysPrf L) (only parsing).
Fixpoint subAllTerm (t : fol.Term L) : (nat -> fol.Term L) -> fol.Term L := match t return ((nat -> fol.Term L) -> fol.Term L) with | fol.var x => fun m => m x | fol.apply f ts => fun m => fol.apply L f (subAllTerms _ ts m) end with subAllTerms (n : nat) (ts : fol.Terms L n) {struct ts} : (nat -> fol.Term L) -> fol.Terms L n := match ts in (fol.Terms _ n) return ((nat -> fol.Term L) -> fol.Terms L n) with | Tnil => fun _ => Tnil L | Tcons n' t ss => fun m => Tcons L n' (subAllTerm t m) (subAllTerms _ ss m) end.
Fixpoint freeVarMap (l : list nat) : (nat -> fol.Term L) -> list nat := match l with | nil => fun _ => nil | a :: l' => fun m => freeVarTerm L (m a) ++ freeVarMap l' m end.
Fixpoint subAllFormula (f : Formula) (m : (nat -> Term)) {struct f} : Formula := match f with | fol.equal t s => equal (subAllTerm t m) (subAllTerm s m) | fol.atomic r ts => atomic r (subAllTerms _ ts m) | fol.impH f g => impH (subAllFormula f m) (subAllFormula g m) | fol.notH f => notH (subAllFormula f m) | fol.forallH n f => let nv := newVar (freeVarFormula L f ++ freeVarMap (freeVarFormula L (forallH n f)) m) in forallH nv (subAllFormula f (fun v : nat => match eq_nat_dec v n with | left _ => var nv | right _ => m v end)) end.
Section subAllCloseFrom.
Fixpoint closeFrom (a n : nat) (f : fol.Formula L) {struct n} : fol.Formula L := match n with | O => f | S m => fol.forallH L (a + m) (closeFrom a m f) end.
Opaque le_lt_dec.
End subAllCloseFrom.
End SubAllVars.

Lemma subSubAllFormula : forall (T : fol.System L) (f : fol.Formula L) (m : nat -> fol.Term L) (v : nat) (s : fol.Term L), folProof.SysPrf L T (fol.iffH L (substituteFormula L (subAllFormula f m) v s) (subAllFormula f (fun n : nat => substituteTerm L (m n) v s))).
Proof.
intros T f.
generalize f T.
clear f T.
intro f.
elim f using Formula_depth_ind2; simpl in |- *; intros.
rewrite (subFormulaEqual L).
do 2 rewrite subSubAllTerm.
apply (iffRefl L).
rewrite (subFormulaRelation L).
rewrite subSubAllTerms.
apply (iffRefl L).
rewrite (subFormulaImp L).
apply (reduceImp L).
apply H.
apply H0.
rewrite (subFormulaNot L).
apply (reduceNot L).
apply H.
set (nv1 := newVar (freeVarFormula L a ++ freeVarMap (list_remove nat eq_nat_dec v (freeVarFormula L a)) m)) in *.
set (nv2 := newVar (freeVarFormula L a ++ freeVarMap (list_remove nat eq_nat_dec v (freeVarFormula L a)) (fun n : nat => substituteTerm L (m n) v0 s))) in *.
apply (sysExtend L) with (Empty_set (fol.Formula L)).
unfold Included in |- *.
intros.
induction H0.
decompose record (subFormulaForall2 L (subAllFormula a (fun v1 : nat => match eq_nat_dec v1 v with | left _ => fol.var L nv1 | right _ => m v1 end)) nv1 v0 s).
rewrite H4; clear H4.
induction (eq_nat_dec nv1 v0).
assert (forall n : nat, In n (freeVarFormula L (fol.forallH L v a)) -> substituteTerm L (m n) v0 s = m n).
intros.
apply subTermNil.
unfold not in |- *; intros.
elim (newVar1 (freeVarFormula L a ++ freeVarMap (list_remove nat eq_nat_dec v (freeVarFormula L a)) m)).
fold nv1 in |- *.
rewrite a0.
apply in_or_app.
right.
eapply freeVarMap1.
apply H4.
apply H3.
assert (nv1 = nv2).
unfold nv1, nv2 in |- *.
rewrite (freeVarMap_ext (list_remove nat eq_nat_dec v (freeVarFormula L a)) (fun n : nat => substituteTerm L (m n) v0 s) m) .
reflexivity.
apply H3.
rewrite H4.
rewrite (subAllFormula_ext a (fun v1 : nat => match eq_nat_dec v1 v with | left _ => fol.var L nv2 | right _ => substituteTerm L (m v1) v0 s end) (fun v1 : nat => match eq_nat_dec v1 v with | left _ => fol.var L nv2 | right _ => m v1 end)).
apply (iffRefl L).
intros.
induction (eq_nat_dec m0 v).
reflexivity.
apply H3.
simpl in |- *.
apply In_list_remove3; auto.
apply (iffTrans L) with (fol.forallH L x (substituteFormula L (subAllFormula a (fun v1 : nat => match eq_nat_dec v1 v with | left _ => fol.var L x | right _ => m v1 end)) v0 s)).
apply (reduceForall L).
apply (notInFreeVarSys L).
apply (reduceSub L).
apply (notInFreeVarSys L).
apply (iffTrans L) with (subAllFormula a (fun v1 : nat => substituteTerm L match eq_nat_dec v1 v with | left _ => fol.var L nv1 | right _ => m v1 end nv1 (fol.var L x))).
fold (folProof.SysPrf L) in |- *.
fold (fol.iffH L) in |- *.
apply H with (b := a) (v := nv1) (s := fol.var L x) (m := fun v1 : nat => match eq_nat_dec v1 v with | left _ => fol.var L nv1 | right _ => m v1 end).
apply depthForall.
rewrite (subAllFormula_ext a (fun v1 : nat => match eq_nat_dec v1 v with | left _ => fol.var L x | right _ => m v1 end) (fun v1 : nat => substituteTerm L match eq_nat_dec v1 v with | left _ => fol.var L nv1 | right _ => m v1 end nv1 (fol.var L x))).
apply (iffRefl L).
intros.
induction (eq_nat_dec m0 v).
rewrite (subTermVar1 L).
reflexivity.
rewrite (subTermNil L).
reflexivity.
unfold not in |- *; intros.
elim (newVar1 (freeVarFormula L a ++ freeVarMap (list_remove nat eq_nat_dec v (freeVarFormula L a)) m)).
fold nv1 in |- *.
apply in_or_app.
right.
eapply freeVarMap1.
apply H4.
apply In_list_remove3; auto.
apply (iffTrans L) with (fol.forallH L x (subAllFormula a (fun v1 : nat => match eq_nat_dec v1 v with | left _ => fol.var L x | right _ => substituteTerm L (m v1) v0 s end))).
apply (reduceForall L).
apply (notInFreeVarSys L).
eapply (iffTrans L).
apply H with (b := a) (v := v0) (s := s) (m := fun v1 : nat => match eq_nat_dec v1 v with | left _ => fol.var L x | right _ => m v1 end).
apply depthForall.
rewrite (subAllFormula_ext a (fun v1 : nat => match eq_nat_dec v1 v with | left _ => fol.var L x | right _ => substituteTerm L (m v1) v0 s end) (fun n : nat => substituteTerm L match eq_nat_dec n v with | left _ => fol.var L x | right _ => m n end v0 s)).
apply (iffRefl L).
intros.
induction (eq_nat_dec m0 v).
rewrite subTermNil.
reflexivity.
simpl in |- *.
tauto.
reflexivity.
apply (iffTrans L) with (fol.forallH L nv2 (substituteFormula L (subAllFormula a (fun v1 : nat => match eq_nat_dec v1 v with | left _ => fol.var L x | right _ => substituteTerm L (m v1) v0 s end)) x (fol.var L nv2))).
apply (rebindForall L).
unfold not in |- *; intros.
simpl in H3.
assert (In nv2 (freeVarFormula L (subAllFormula a (fun v1 : nat => match eq_nat_dec v1 v with | left _ => fol.var L x | right _ => substituteTerm L (m v1) v0 s end)))).
eapply In_list_remove1.
apply H3.
decompose record (freeVarSubAllFormula1 _ _ _ H4).
induction (eq_nat_dec x0 v).
induction H7 as [H5| H5].
elim (In_list_remove2 _ _ _ _ _ H3).
auto.
contradiction.
elim (newVar1 (freeVarFormula L a ++ freeVarMap (list_remove nat eq_nat_dec v (freeVarFormula L a)) (fun n : nat => substituteTerm L (m n) v0 s))).
fold nv2 in |- *.
apply in_or_app.
right.
eapply freeVarMap1.
apply H7.
apply In_list_remove3; auto.
apply (reduceForall L).
apply (notInFreeVarSys L).
eapply (iffTrans L).
apply H.
apply depthForall.
simpl in |- *.
rewrite (subAllFormula_ext a (fun v1 : nat => match eq_nat_dec v1 v with | left _ => fol.var L nv2 | right _ => substituteTerm L (m v1) v0 s end) (fun n : nat => substituteTerm L match eq_nat_dec n v with | left _ => fol.var L x | right _ => substituteTerm L (m n) v0 s end x (fol.var L nv2))).
apply (iffRefl L).
intros.
induction (eq_nat_dec m0 v).
rewrite (subTermVar1 L).
reflexivity.
rewrite (subTermNil L (substituteTerm L (m m0) v0 s)).
reflexivity.
unfold not in |- *.
intros.
induction (freeVarSubTerm3 _ _ _ _ _ H4).
elim H2.
apply In_list_remove3.
eapply freeVarSubAllFormula2.
apply H3.
induction (eq_nat_dec m0 v).
elim b0; auto.
eapply In_list_remove1.
apply H5.
unfold not in |- *; intros.
elim (newVar1 (freeVarFormula L a ++ freeVarMap (list_remove nat eq_nat_dec v (freeVarFormula L a)) m)).
fold nv1 in |- *.
rewrite <- H6.
apply in_or_app.
right.
eapply freeVarMap1.
eapply In_list_remove1.
apply H5.
apply In_list_remove3; auto.
auto.
