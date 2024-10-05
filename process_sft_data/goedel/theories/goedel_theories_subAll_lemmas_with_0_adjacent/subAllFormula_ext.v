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

Lemma subAllFormula_ext : forall (f : fol.Formula L) (m1 m2 : nat -> fol.Term L), (forall m : nat, In m (freeVarFormula L f) -> m1 m = m2 m) -> subAllFormula f m1 = subAllFormula f m2.
Proof.
intro.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf]; simpl in |- *; intros.
rewrite (subAllTerm_ext t m1 m2).
rewrite (subAllTerm_ext t0 m1 m2).
reflexivity.
intros.
apply H.
apply in_or_app.
auto.
intros.
apply H.
apply in_or_app.
auto.
rewrite (subAllTerms_ext _ t m1 m2).
reflexivity.
apply H.
rewrite (Hrecf1 m1 m2).
rewrite (Hrecf0 m1 m2).
reflexivity.
intros.
apply H.
apply in_or_app.
auto.
intros.
apply H.
apply in_or_app.
auto.
rewrite (Hrecf m1 m2).
reflexivity.
apply H.
rewrite (freeVarMap_ext (list_remove nat eq_nat_dec n (freeVarFormula L f)) m1 m2) .
set (m1' := fun v : nat => match eq_nat_dec v n with | left _ => fol.var L (newVar (freeVarFormula L f ++ freeVarMap (list_remove nat eq_nat_dec n (freeVarFormula L f)) m2)) | right _ => m1 v end) in *.
set (m2' := fun v : nat => match eq_nat_dec v n with | left _ => fol.var L (newVar (freeVarFormula L f ++ freeVarMap (list_remove nat eq_nat_dec n (freeVarFormula L f)) m2)) | right _ => m2 v end) in *.
rewrite (Hrecf m1' m2').
reflexivity.
intros.
unfold m1', m2' in |- *; clear m1' m2'.
induction (eq_nat_dec m n).
reflexivity.
apply H.
apply In_list_remove3; auto.
intros.
apply H.
auto.
