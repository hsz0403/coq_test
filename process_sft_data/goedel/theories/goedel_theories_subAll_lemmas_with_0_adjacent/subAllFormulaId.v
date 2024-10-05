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

Lemma subAllFormulaId : forall (T : fol.System L) (f : fol.Formula L), folProof.SysPrf L T (fol.iffH L (subAllFormula f (fun x : nat => fol.var L x)) f).
Proof.
intros.
apply (sysExtend L) with (Empty_set (fol.Formula L)).
unfold Included in |- *.
intros.
induction H.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf]; simpl in |- *.
repeat rewrite subAllTermId.
apply (iffRefl L).
rewrite subAllTermsId.
apply (iffRefl L).
apply (reduceImp L).
apply Hrecf1.
apply Hrecf0.
apply (reduceNot L).
apply Hrecf.
set (nv := newVar (freeVarFormula L f ++ freeVarMap (list_remove nat eq_nat_dec n (freeVarFormula L f)) (fun x : nat => fol.var L x))) in *.
apply (iffTrans L) with (fol.forallH L n (subAllFormula f (fun x : nat => fol.var L x))).
apply (iffTrans L) with (fol.forallH L nv (substituteFormula L (subAllFormula f (fun x : nat => fol.var L x)) n (fol.var L nv))).
replace (subAllFormula f (fun v : nat => match eq_nat_dec v n with | left _ => fol.var L nv | right _ => fol.var L v end)) with (subAllFormula f (fun x : nat => substituteTerm L (fol.var L x) n (fol.var L nv))).
apply (reduceForall L).
apply (notInFreeVarSys L).
apply (iffSym L).
apply subSubAllFormula with (m := fun x : nat => fol.var L x).
apply subAllFormula_ext.
intros.
simpl in |- *.
induction (eq_nat_dec n m); induction (eq_nat_dec m n); reflexivity || (elimtype False; auto).
apply (iffSym L).
apply (rebindForall L).
unfold not in |- *; intros.
assert (In nv (freeVarFormula L (subAllFormula f (fun x : nat => fol.var L x)))).
eapply In_list_remove1.
apply H.
decompose record (freeVarSubAllFormula1 _ _ _ H0).
elim (newVar1 (freeVarFormula L f ++ freeVarMap (list_remove nat eq_nat_dec n (freeVarFormula L f)) (fun x : nat => fol.var L x))).
fold nv in |- *.
apply in_or_app.
right.
eapply freeVarMap1.
apply H3.
apply In_list_remove3.
apply H2.
induction H3 as [H1| H1].
rewrite H1.
eapply In_list_remove2.
apply H.
contradiction.
apply (reduceForall L).
apply (notInFreeVarSys L).
apply Hrecf.
