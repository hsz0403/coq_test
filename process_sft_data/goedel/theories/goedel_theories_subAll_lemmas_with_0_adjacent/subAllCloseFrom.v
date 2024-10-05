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

Lemma subAllCloseFrom : forall (n : nat) (m : nat -> fol.Term L) (f : fol.Formula L) (T : fol.System L), folProof.SysPrf L T (closeFrom 0 n f) -> folProof.SysPrf L T (subAllFormula f (fun x : nat => match le_lt_dec n x with | left _ => fol.var L x | right _ => m x end)).
Proof.
intros.
assert (exists r : nat, (forall v : nat, v < n -> newVar (freeVarTerm L (m v)) <= r)).
clear H T f.
induction n as [| n Hrecn].
exists 0.
intros.
elim (lt_n_O _ H).
induction Hrecn as (x, H).
exists (max (newVar (freeVarTerm L (m n))) x).
intros.
assert (v <= n).
apply lt_n_Sm_le.
auto.
induction (le_lt_or_eq _ _ H1).
apply le_trans with x.
apply H; auto.
apply le_max_r.
rewrite H2.
apply le_max_l.
induction H0 as (x, H0).
set (r := max (max n (newVar (freeVarFormula L f))) x) in *.
set (f' := subAllFormula f (fun x : nat => match le_lt_dec n x with | left _ => fol.var L x | right _ => fol.var L (r + x) end)) in *.
set (m' := fun x : nat => m (x - r)) in *.
apply (impE L) with (subAllFormula f' (fun x : nat => match le_lt_dec r x with | left _ => match le_lt_dec (r + n) x with | left _ => fol.var L x | right _ => m' x end | right _ => fol.var L x end)).
replace (subAllFormula f (fun x0 : nat => match le_lt_dec n x0 with | left _ => fol.var L x0 | right _ => m x0 end)) with (subAllFormula f (fun x : nat => subAllTerm match le_lt_dec n x with | left _ => fol.var L x | right _ => fol.var L (r + x) end (fun x0 : nat => match le_lt_dec r x0 with | left _ => match le_lt_dec (r + n) x0 with | left _ => fol.var L x0 | right _ => m' x0 end | right _ => fol.var L x0 end))).
apply (iffE1 L).
unfold f' in |- *.
apply subAllSubAllFormula with (m1 := fun x0 : nat => match le_lt_dec n x0 with | left _ => fol.var L x0 | right _ => fol.var L (r + x0) end) (m2 := fun x0 : nat => match le_lt_dec r x0 with | left _ => match le_lt_dec (r + n) x0 with | left _ => fol.var L x0 | right _ => m' x0 end | right _ => fol.var L x0 end).
unfold m' in |- *.
apply subAllFormula_ext; intros.
induction (le_lt_dec n m0).
simpl in |- *.
induction (le_lt_dec r m0).
elim (le_not_lt _ _ a0).
apply lt_le_trans with (newVar (freeVarFormula L f)).
apply newVar2.
auto.
unfold r in |- *.
eapply le_trans.
apply le_max_r.
apply le_max_l.
auto.
simpl in |- *.
induction (le_lt_dec r (r + m0)).
induction (le_lt_dec (r + n) (r + m0)).
elim (lt_not_le _ _ b).
eapply (fun p n m : nat => plus_le_reg_l n m p).
apply a0.
rewrite minus_plus.
auto.
elim (lt_not_le _ _ b0).
apply le_plus_l.
apply subAllCloseFrom1.
intros.
apply lt_le_trans with (newVar (freeVarTerm L (m v))).
apply newVar2.
unfold m' in H2.
rewrite minus_plus in H2.
auto.
apply le_trans with x.
apply H0.
auto.
unfold r in |- *.
apply le_max_r.
unfold f' in |- *.
clear f'.
apply liftCloseFrom.
intros.
apply lt_le_trans with (newVar (freeVarFormula L f)).
apply newVar2.
auto.
unfold r in |- *.
eapply le_trans.
apply le_max_r.
apply le_max_l.
unfold r in |- *.
eapply le_trans.
apply le_max_l.
apply le_max_l.
apply H.
