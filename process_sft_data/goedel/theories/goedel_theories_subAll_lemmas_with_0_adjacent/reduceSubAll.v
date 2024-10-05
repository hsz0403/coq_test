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

Lemma reduceSubAll : forall (T : fol.System L) (map : nat -> fol.Term L) (A B : fol.Formula L), (forall v : nat, ~ In_freeVarSys L v T) -> folProof.SysPrf L T (fol.iffH L A B) -> folProof.SysPrf L T (fol.iffH L (subAllFormula A map) (subAllFormula B map)).
Proof.
assert (forall (T : fol.System L) (map : nat -> fol.Term L) (A B : fol.Formula L), (forall v : nat, ~ In_freeVarSys L v T) -> folProof.SysPrf L T (fol.iffH L A B) -> folProof.SysPrf L T (fol.impH L (subAllFormula A map) (subAllFormula B map))).
intros.
replace (fol.impH L (subAllFormula A map) (subAllFormula B map)) with (subAllFormula (fol.impH L A B) map).
set (n := newVar (freeVarFormula L (fol.impH L A B))) in *.
replace (subAllFormula (fol.impH L A B) map) with (subAllFormula (fol.impH L A B) (fun x : nat => match le_lt_dec n x with | left _ => fol.var L x | right _ => map x end)).
apply subAllCloseFrom.
induction n as [| n Hrecn].
simpl in |- *.
apply (iffE1 L).
auto.
simpl in |- *.
apply (forallI L).
auto.
auto.
apply subAllFormula_ext.
intros.
induction (le_lt_dec n m).
elim (le_not_lt _ _ a).
unfold n in |- *.
apply newVar2.
auto.
auto.
reflexivity.
intros.
apply (iffI L).
apply H; auto.
apply H.
auto.
apply (iffSym L).
auto.
