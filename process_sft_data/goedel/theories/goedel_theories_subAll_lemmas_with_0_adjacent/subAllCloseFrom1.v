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

Lemma subAllCloseFrom1 : forall (n m : nat) (map : nat -> fol.Term L) (f : fol.Formula L) (T : fol.System L), (forall v : nat, v < n -> forall w : nat, In w (freeVarTerm L (map (m + v))) -> w < m) -> folProof.SysPrf L T (closeFrom m n f) -> folProof.SysPrf L T (subAllFormula f (fun x : nat => match le_lt_dec m x with | left _ => match le_lt_dec (m + n) x with | left _ => fol.var L x | right _ => map x end | right _ => fol.var L x end)).
Proof.
intro.
induction n as [| n Hrecn]; simpl in |- *; intros.
replace (subAllFormula f (fun x : nat => match le_lt_dec m x with | left _ => match le_lt_dec (m + 0) x with | left _ => fol.var L x | right _ => map x end | right _ => fol.var L x end)) with (subAllFormula f (fun x : nat => fol.var L x)).
apply (impE L) with f.
apply (iffE2 L).
apply subAllFormulaId.
apply H0.
apply subAllFormula_ext.
intros.
rewrite <- plus_n_O.
induction (le_lt_dec m m0).
auto.
auto.
apply (impE L) with (substituteFormula L (subAllFormula f (fun x : nat => match le_lt_dec m x with | left _ => match le_lt_dec (m + n) x with | left _ => fol.var L x | right _ => map x end | right _ => fol.var L x end)) (m + n) (map (m + n))).
replace (subAllFormula f (fun x : nat => match le_lt_dec m x with | left _ => match le_lt_dec (m + S n) x with | left _ => fol.var L x | right _ => map x end | right _ => fol.var L x end)) with (subAllFormula f (fun x : nat => substituteTerm L match le_lt_dec m x with | left _ => match le_lt_dec (m + n) x with | left _ => fol.var L x | right _ => map x end | right _ => fol.var L x end (m + n) (map (m + n)))).
apply (iffE1 L).
apply subSubAllFormula with (m := fun x : nat => match le_lt_dec m x with | left _ => match le_lt_dec (m + n) x with | left _ => fol.var L x | right _ => map x end | right _ => fol.var L x end).
apply subAllFormula_ext.
intros.
induction (le_lt_dec m m0).
rewrite <- plus_Snm_nSm.
induction (le_lt_dec (S m + n) m0).
simpl in a0.
induction (le_lt_dec (m + n) m0).
apply (subTermVar2 L).
unfold not in |- *; intros.
rewrite H2 in a0.
apply (le_not_lt _ _ a0).
apply lt_n_Sn.
elim (le_not_lt (S (m + n)) (m + n)).
eapply le_trans.
apply a0.
apply lt_le_weak.
auto.
apply lt_n_Sn.
induction (le_lt_dec (m + n) m0).
replace (m + n) with m0.
apply (subTermVar1 L).
simpl in b.
induction (le_lt_or_eq _ _ a0).
elim (lt_not_le _ _ H2).
apply lt_n_Sm_le.
auto.
auto.
apply (subTermNil L).
unfold not in |- *; intros.
assert (m + (m0 - m) = m0).
apply le_plus_minus_r.
auto.
elim (lt_not_le (m + n) m).
apply H with (m0 - m).
apply plus_lt_reg_l with m.
rewrite H3.
rewrite <- plus_Snm_nSm.
apply b.
rewrite H3.
apply H2.
apply le_plus_l.
apply (subTermVar2 L).
unfold not in |- *; intros.
rewrite <- H2 in b.
elim (lt_not_le _ _ b).
apply le_plus_l.
apply (forallE L).
apply (impE L) with (fol.forallH L (m + n) (closeFrom m n f)).
apply sysExtend with (Empty_set (fol.Formula L)).
unfold Included in |- *.
intros.
induction H1.
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H1 as (x, H1); induction H1 as (H1, H2).
induction H2 as [x H2| x H2]; [ induction H2 | induction H2 ].
elim (In_list_remove2 _ _ _ _ _ H1).
auto.
apply Hrecn.
intros.
eapply H.
apply lt_S.
apply H1.
auto.
eapply (forallSimp L).
apply Axm; right; constructor.
apply H0.
