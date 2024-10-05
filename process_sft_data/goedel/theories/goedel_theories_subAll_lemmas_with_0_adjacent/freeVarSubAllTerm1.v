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

Lemma freeVarSubAllTerm1 : forall (t : fol.Term L) (m : nat -> fol.Term L) (v : nat), In v (freeVarTerm L (subAllTerm t m)) -> exists n : nat, In n (freeVarTerm L t) /\ In v (freeVarTerm L (m n)).
Proof.
intros t m v.
elim t using Term_Terms_ind with (P0 := fun (n : nat) (ts : fol.Terms L n) => In v (freeVarTerms L n (subAllTerms n ts m)) -> exists a : nat, In a (freeVarTerms L n ts) /\ In v (freeVarTerm L (m a))).
intros.
simpl in H.
exists n.
simpl in |- *.
auto.
intros.
simpl in H0.
auto.
intros.
contradiction.
intros.
simpl in H1.
unfold freeVarTerms in H1.
fold (freeVarTerm L (subAllTerm t0 m)) in H1.
fold (freeVarTerms L n (subAllTerms n t1 m)) in H1.
induction (in_app_or _ _ _ H1).
induction (H H2).
exists x.
split.
unfold freeVarTerms in |- *.
fold (freeVarTerm L t0) in |- *.
fold (freeVarTerms L n t1) in |- *.
apply in_or_app.
tauto.
tauto.
induction (H0 H2).
exists x.
split.
unfold freeVarTerms in |- *.
fold (freeVarTerm L t0) in |- *.
fold (freeVarTerms L n t1) in |- *.
apply in_or_app.
tauto.
tauto.
