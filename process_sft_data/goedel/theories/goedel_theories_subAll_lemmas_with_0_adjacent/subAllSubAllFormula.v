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

Lemma subAllSubAllFormula : forall (T : fol.System L) (f : fol.Formula L) (m1 m2 : nat -> fol.Term L), folProof.SysPrf L T (fol.iffH L (subAllFormula (subAllFormula f m1) m2) (subAllFormula f (fun n : nat => subAllTerm (m1 n) m2))).
Proof.
intros T f.
generalize f T.
clear f T.
intro f.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf]; intros.
simpl in |- *.
repeat rewrite subAllSubAllTerm.
apply (iffRefl L).
simpl in |- *.
rewrite subAllSubAllTerms.
apply (iffRefl L).
simpl in |- *.
apply (reduceImp L).
apply Hrecf1.
apply Hrecf0.
simpl in |- *.
apply (reduceNot L).
apply Hrecf.
simpl in |- *.
set (nv1 := freeVarFormula L f ++ freeVarMap (list_remove nat eq_nat_dec n (freeVarFormula L f)) m1) in *.
set (nv2 := freeVarFormula L f ++ freeVarMap (list_remove nat eq_nat_dec n (freeVarFormula L f)) (fun n0 : nat => subAllTerm (m1 n0) m2)) in *.
set (nv3 := freeVarFormula L (subAllFormula f (fun v : nat => match eq_nat_dec v n with | left _ => fol.var L (newVar nv1) | right _ => m1 v end)) ++ freeVarMap (list_remove nat eq_nat_dec (newVar nv1) (freeVarFormula L (subAllFormula f (fun v : nat => match eq_nat_dec v n with | left _ => fol.var L (newVar nv1) | right _ => m1 v end)))) m2) in *.
apply (iffTrans L) with (fol.forallH L (newVar nv3) (substituteFormula L (subAllFormula f (fun v : nat => match eq_nat_dec v n with | left _ => fol.var L (newVar nv2) | right _ => subAllTerm (m1 v) m2 end)) (newVar nv2) (fol.var L (newVar nv3)))).
eapply (sysExtend L) with (Empty_set (fol.Formula L)).
unfold Included in |- *.
intros.
induction H.
apply (reduceForall L).
apply (notInFreeVarSys L).
eapply (iffTrans L).
apply Hrecf.
set (a1 := fun v : nat => match eq_nat_dec v n with | left _ => fol.var L (newVar nv2) | right _ => subAllTerm (m1 v) m2 end) in *.
simpl in |- *.
set (a2 := fun n0 : nat => subAllTerm match eq_nat_dec n0 n with | left _ => fol.var L (newVar nv1) | right _ => m1 n0 end (fun v : nat => match eq_nat_dec v (newVar nv1) with | left _ => fol.var L (newVar nv3) | right _ => m2 v end)) in *.
replace (subAllFormula f a2) with (subAllFormula f (fun x : nat => substituteTerm L (a1 x) (newVar nv2) (fol.var L (newVar nv3)))).
apply (iffSym L).
apply subSubAllFormula.
apply subAllFormula_ext.
intros.
unfold a1, a2 in |- *.
induction (eq_nat_dec m n).
rewrite (subTermVar1 L).
simpl in |- *.
induction (eq_nat_dec (newVar nv1) (newVar nv1)).
reflexivity.
elim b.
auto.
rewrite subSubAllTerm.
apply subAllTerm_ext.
intros.
induction (eq_nat_dec m0 (newVar nv1)).
elim (newVar1 nv1).
rewrite <- a.
unfold nv1 in |- *.
apply in_or_app.
right.
eapply freeVarMap1.
apply H0.
apply In_list_remove3; auto.
apply (subTermNil L).
unfold not in |- *; intros.
elim (newVar1 nv2).
unfold nv2 at 2 in |- *.
apply in_or_app.
right.
eapply freeVarMap1.
eapply freeVarSubAllTerm2.
apply H0.
apply H1.
apply In_list_remove3; auto.
apply (iffSym L).
apply (rebindForall L).
unfold not in |- *; intros.
assert (In (newVar nv3) (freeVarFormula L (subAllFormula f (fun v : nat => match eq_nat_dec v n with | left _ => fol.var L (newVar nv2) | right _ => subAllTerm (m1 v) m2 end)))).
eapply In_list_remove1.
apply H.
decompose record (freeVarSubAllFormula1 _ _ _ H0).
induction (eq_nat_dec x n).
induction H3 as [H1| H1].
elim (In_list_remove2 _ _ _ _ _ H).
auto.
contradiction.
decompose record (freeVarSubAllTerm1 _ _ _ H3).
elim (newVar1 nv3).
unfold nv3 at 2 in |- *.
apply in_or_app.
right.
eapply freeVarMap1.
apply H5.
apply In_list_remove3.
eapply freeVarSubAllFormula2.
apply H2.
induction (eq_nat_dec x n).
elim b.
auto.
auto.
unfold not in |- *; intros.
elim (newVar1 nv1).
rewrite <- H1.
unfold nv1 in |- *.
apply in_or_app.
right.
eapply freeVarMap1.
apply H4.
apply In_list_remove3; auto.
