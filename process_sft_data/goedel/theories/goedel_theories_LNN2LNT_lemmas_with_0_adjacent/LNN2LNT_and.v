Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import misc.
Require Import ListExt.
Require Import folProp.
Require Import folProof.
Require Import Languages.
Require Import subAll.
Require Import subProp.
Require Import folLogic3.
Require Import folReplace.
Require Import LNT.
Require Import Max.
Require Import codeNatToTerm.
Fixpoint LNN2LNT_term (t : fol.Term LNN) : Term := match t with | fol.var v => var v | apply f ts => apply LNT f (LNN2LNT_terms _ ts) end with LNN2LNT_terms (n : nat) (ts : fol.Terms LNN n) {struct ts} : Terms n := match ts in (fol.Terms _ n0) return (Terms n0) with | Tnil => Tnil LNT | Tcons m s ss => Tcons LNT m (LNN2LNT_term s) (LNN2LNT_terms m ss) end.
Definition LTFormula := existH 2 (equal (Plus (var 0) (Succ (var 2))) (var 1)).
Definition translateLT (ts : fol.Terms LNN (arity LNN (inl _ LT))) : Formula.
simpl in ts.
induction (consTerms _ _ ts).
induction x as (a, b).
induction (consTerms _ _ b).
induction x as (a0, b0).
set (x := LNN2LNT_term a) in *.
set (y := LNN2LNT_term a0) in *.
apply (subAllFormula LNT LTFormula).
intro.
induction H as [| H HrecH].
exact x.
induction H as [| H HrecH0].
exact y.
exact (var H).
Defined.
Fixpoint LNN2LNT_formula (f : fol.Formula LNN) : Formula := match f with | fol.equal t1 t2 => equal (LNN2LNT_term t1) (LNN2LNT_term t2) | atomic r ts => match r as l return (fol.Terms LNN (arity LNN (inl _ l)) -> Formula) with | LT => fun t0 : fol.Terms LNN (arity LNN (inl _ LT)) => translateLT t0 end ts | fol.impH A B => impH (LNN2LNT_formula A) (LNN2LNT_formula B) | fol.notH A => notH (LNN2LNT_formula A) | fol.forallH v A => forallH v (LNN2LNT_formula A) end.
Fixpoint LNT2LNN_term (t : Term) : fol.Term LNN := match t with | fol.var v => fol.var LNN v | apply f ts => apply LNN f (LNT2LNN_terms _ ts) end with LNT2LNN_terms (n : nat) (ts : Terms n) {struct ts} : fol.Terms LNN n := match ts in (fol.Terms _ n0) return (fol.Terms LNN n0) with | Tnil => Tnil LNN | Tcons m s ss => Tcons LNN m (LNT2LNN_term s) (LNT2LNN_terms m ss) end.
Fixpoint LNT2LNN_formula (f : Formula) : fol.Formula LNN := match f with | fol.equal t1 t2 => fol.equal LNN (LNT2LNN_term t1) (LNT2LNN_term t2) | atomic r ts => match r with end | fol.impH A B => fol.impH LNN (LNT2LNN_formula A) (LNT2LNN_formula B) | fol.notH A => fol.notH LNN (LNT2LNN_formula A) | fol.forallH v A => fol.forallH LNN v (LNT2LNN_formula A) end.
Section Translate_Proof.
Variable U : fol.System LNN.
Variable V : System.
Hypothesis AxiomsOK : forall f : fol.Formula LNN, mem _ U f -> exists Axm : Formulas, (exists prf : Prf LNT Axm (LNN2LNT_formula f), (forall g : Formula, In g Axm -> mem _ V g)) /\ forall v, In v (freeVarListFormula LNT Axm) -> (In v (freeVarFormula LNN f)).
End Translate_Proof.

Lemma LNN2LNT_and : forall a b : fol.Formula LNN, LNN2LNT_formula (fol.andH LNN a b) = andH (LNN2LNT_formula a) (LNN2LNT_formula b).
Proof.
reflexivity.
