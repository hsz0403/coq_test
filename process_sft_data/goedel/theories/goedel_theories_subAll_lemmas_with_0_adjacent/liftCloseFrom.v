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

Lemma liftCloseFrom : forall (n : nat) (f : fol.Formula L) (T : fol.System L) (m : nat), (forall v : nat, In v (freeVarFormula L f) -> v < m) -> n <= m -> folProof.SysPrf L T (closeFrom 0 n f) -> folProof.SysPrf L T (closeFrom m n (subAllFormula f (fun x : nat => match le_lt_dec n x with | left _ => fol.var L x | right _ => fol.var L (m + x) end))).
Proof.
intro.
induction n as [| n Hrecn]; simpl in |- *; intros.
replace (subAllFormula f (fun x : nat => match le_lt_dec 0 x with | left _ => fol.var L x | right _ => fol.var L (m + x) end)) with (subAllFormula f (fun x : nat => fol.var L x)).
apply (impE L) with f.
apply (iffE2 L).
apply subAllFormulaId.
apply H1.
apply subAllFormula_ext.
intros.
induction (le_lt_dec 0 m0).
auto.
elim (lt_n_O _ b).
apply (impE L) with (fol.forallH L n (closeFrom 0 n f)).
apply sysExtend with (Empty_set (fol.Formula L)).
unfold Included in |- *.
intros.
induction H2.
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H2 as (x, H2); induction H2 as (H2, H3).
induction H3 as [x H3| x H3]; [ induction H3 | induction H3 ].
assert (forall q : nat, n <= q -> m <= q -> ~ In q (freeVarFormula L (fol.forallH L n (closeFrom 0 n f)))).
clear H2 H1 T Hrecn.
induction n as [| n Hrecn]; simpl in |- *; unfold not in |- *; intros.
elim (lt_not_le q m).
apply H.
eapply In_list_remove1.
apply H3.
auto.
elim Hrecn with (q := q).
apply le_S_n.
apply le_S.
auto.
apply le_S_n.
apply le_S.
auto.
auto.
simpl in |- *.
eapply In_list_remove1.
apply H3.
apply H3 with (q := m + n).
apply le_plus_r.
apply le_plus_l.
apply H2.
apply (impE L) with (closeFrom m n (substituteFormula L (subAllFormula f (fun x : nat => match le_lt_dec n x with | left _ => fol.var L x | right _ => fol.var L (m + x) end)) n (fol.var L (m + n)))).
apply sysWeaken.
clear H1 H T Hrecn.
cut (folProof.SysPrf L (Empty_set (fol.Formula L)) (fol.impH L (substituteFormula L (subAllFormula f (fun x : nat => match le_lt_dec n x with | left _ => fol.var L x | right _ => fol.var L (m + x) end)) n (fol.var L (m + n))) (subAllFormula f (fun x : nat => match le_lt_dec (S n) x with | left _ => fol.var L x | right _ => fol.var L (m + x) end)))).
generalize (substituteFormula L (subAllFormula f (fun x : nat => match le_lt_dec n x with | left _ => fol.var L x | right _ => fol.var L (m + x) end)) n (fol.var L (m + n))).
generalize (subAllFormula f (fun x : nat => match le_lt_dec (S n) x with | left _ => fol.var L x | right _ => fol.var L (m + x) end)).
clear f H0.
intros.
induction n as [| n Hrecn]; simpl in |- *.
apply H.
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H0 as (x, H0); induction H0 as (H0, H1).
induction H1 as [x H1| x H1]; [ induction H1 | induction H1 ].
elim (In_list_remove2 _ _ _ _ _ H0).
auto.
apply impE with (closeFrom m n f0).
apply sysWeaken.
apply Hrecn.
eapply forallSimp.
apply Axm; right; constructor.
replace (subAllFormula f (fun x : nat => match le_lt_dec (S n) x with | left _ => fol.var L x | right _ => fol.var L (m + x) end)) with (subAllFormula f (fun x : nat => substituteTerm L match le_lt_dec n x with | left _ => fol.var L x | right _ => fol.var L (m + x) end n (fol.var L (m + n)))).
apply (iffE1 L).
apply subSubAllFormula with (m := fun x : nat => match le_lt_dec n x with | left _ => fol.var L x | right _ => fol.var L (m + x) end).
apply subAllFormula_ext.
intros.
induction (le_lt_dec n m0).
induction (le_lt_dec (S n) m0).
apply (subTermVar2 L).
unfold not in |- *; intros.
elim (lt_not_le m0 (S m0)).
apply lt_n_Sn.
rewrite H1 in a0.
auto.
induction (le_lt_or_eq _ _ a).
elim (lt_not_le m0 (S n)).
auto.
apply lt_n_Sm_le.
apply lt_n_S.
auto.
rewrite H1.
apply (subTermVar1 L).
induction (le_lt_dec (S n) m0).
elim (le_not_lt (S n) m0).
auto.
apply lt_S.
auto.
apply (subTermVar2 L).
unfold not in |- *; intros.
rewrite H1 in H0.
apply (le_not_lt (S (m + m0)) m).
apply H0.
apply le_lt_n_Sm.
apply le_plus_l.
assert (forall (f : fol.Formula L) (s r m p : nat), m < s -> s + r <= p -> folProof.SysPrf L (Empty_set (fol.Formula L)) (fol.impH L (substituteFormula L (closeFrom s r f) m (fol.var L p)) (closeFrom s r (substituteFormula L f m (fol.var L p))))).
clear H0 H H1 m T f n Hrecn.
intros f s n.
induction n as [| n Hrecn]; simpl in |- *; intros.
apply (impRefl L).
rewrite (subFormulaForall L).
induction (eq_nat_dec (s + n) m).
rewrite <- a in H.
elim (le_not_lt s (s + n)).
apply le_plus_l.
auto.
induction (In_dec eq_nat_dec (s + n) (freeVarTerm L (fol.var L p))).
induction a as [H1| H1].
rewrite <- plus_Snm_nSm in H0.
simpl in H0.
rewrite <- H1 in H0.
elim (le_not_lt (S p) p).
auto.
apply lt_n_Sn.
contradiction.
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H1 as (x, H1); induction H1 as (H1, H2).
induction H2 as [x H2| x H2]; [ induction H2 | induction H2 ].
elim (In_list_remove2 _ _ _ _ _ H1).
auto.
apply impE with (substituteFormula L (closeFrom s n f) m (fol.var L p)).
apply sysWeaken.
apply Hrecn.
auto.
apply le_S_n.
apply le_S.
rewrite <- plus_Snm_nSm in H0.
auto.
eapply (forallSimp L).
apply Axm; right; constructor.
apply (impE L) with (substituteFormula L (closeFrom m n (subAllFormula f (fun x : nat => match le_lt_dec n x with | left _ => fol.var L x | right _ => fol.var L (m + x) end))) n (fol.var L (m + n))).
apply sysWeaken.
apply H2.
apply lt_S_n.
apply le_lt_n_Sm.
auto.
auto.
apply (forallE L).
apply (impE L) with (fol.forallH L n (closeFrom 0 n f)).
apply sysExtend with (Empty_set (fol.Formula L)).
unfold Included in |- *.
intros.
induction H3.
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H3 as (x, H3); induction H3 as (H3, H4).
induction H4 as [x H4| x H4]; [ induction H4 | induction H4 ].
elim (In_list_remove2 _ _ _ _ _ H3).
auto.
apply Hrecn.
apply H.
apply le_S_n.
apply le_S.
auto.
eapply (forallSimp L).
apply Axm; right; constructor.
apply Axm; right; constructor.
apply H1.
