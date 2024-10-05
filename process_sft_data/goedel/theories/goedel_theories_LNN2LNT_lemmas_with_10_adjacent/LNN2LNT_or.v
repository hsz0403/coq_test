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
Admitted.

Lemma LNN2LNT_natToTerm : forall n : nat, LNN2LNT_term (natToTermLNN n) = natToTerm n.
Proof.
intros.
induction n as [| n Hrecn].
reflexivity.
simpl in |- *.
rewrite Hrecn.
Admitted.

Lemma translateLT1 : forall a a0 b0, translateLT (Tcons LNN 1 a (Tcons LNN 0 a0 b0)) = subAllFormula LNT LTFormula (fun H : nat => nat_rec (fun _ : nat => fol.Term LNT) (LNN2LNT_term a) (fun (H0 : nat) (_ : fol.Term LNT) => nat_rec (fun _ : nat => fol.Term LNT) (LNN2LNT_term a0) (fun (H1 : nat) (_ : fol.Term LNT) => var H1) H0) H).
Proof.
intros.
unfold translateLT in |- *.
induction (consTerms LNN 1 (Tcons LNN 1 a (Tcons LNN 0 a0 b0))).
induction x as (a1, b).
simpl in |- *.
induction (consTerms LNN 0 b).
induction x as (a2, b1).
simpl in |- *.
simpl in p.
inversion p.
assert (b = Tcons LNN 0 a0 b0).
refine (inj_right_pair2 _ eq_nat_dec _ _ _ _ H1).
rewrite H in p0.
simpl in p0.
inversion p0.
clear H4 H3 H H1 H0.
Admitted.

Lemma LNN2LNT_and : forall a b : fol.Formula LNN, LNN2LNT_formula (fol.andH LNN a b) = andH (LNN2LNT_formula a) (LNN2LNT_formula b).
Proof.
Admitted.

Lemma LNN2LNT_iff : forall a b : fol.Formula LNN, LNN2LNT_formula (fol.iffH LNN a b) = iffH (LNN2LNT_formula a) (LNN2LNT_formula b).
Proof.
Admitted.

Lemma LNN2LNT_exist : forall (v : nat) (a : fol.Formula LNN), LNN2LNT_formula (fol.existH LNN v a) = existH v (LNN2LNT_formula a).
Proof.
Admitted.

Lemma LNN2LNT_freeVarTerm : forall t : fol.Term LNN, freeVarTerm LNT (LNN2LNT_term t) = freeVarTerm LNN t.
Proof.
intros.
elim t using Term_Terms_ind with (P0 := fun (n : nat) (ts : fol.Terms LNN n) => freeVarTerms LNT n (LNN2LNT_terms n ts) = freeVarTerms LNN n ts).
intros.
reflexivity.
intros.
simpl in |- *.
repeat rewrite freeVarTermApply.
apply H.
reflexivity.
intros.
simpl in |- *.
transitivity (freeVarTerm LNN t0 ++ freeVarTerms LNN n t1).
rewrite <- H0.
rewrite <- H.
reflexivity.
Admitted.

Lemma LNN2LNT_freeVarTerms : forall (n : nat) (ts : fol.Terms LNN n), freeVarTerms LNT n (LNN2LNT_terms n ts) = freeVarTerms LNN n ts.
Proof.
intros.
induction ts as [| n t ts Hrects].
reflexivity.
intros.
simpl in |- *.
transitivity (freeVarTerm LNN t ++ freeVarTerms LNN n ts).
rewrite <- Hrects.
rewrite <- LNN2LNT_freeVarTerm.
reflexivity.
Admitted.

Lemma LNN2LNT_freeVarFormula : forall (f : fol.Formula LNN) (v : nat), In v (freeVarFormula LNT (LNN2LNT_formula f)) <-> In v (freeVarFormula LNN f).
Proof.
intros.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf].
simpl in |- *.
repeat rewrite LNN2LNT_freeVarTerm.
tauto.
induction r.
simpl in |- *.
induction (consTerms _ _ t).
induction x as (a, b).
simpl in p.
rewrite <- p.
induction (consTerms _ _ b).
induction x as (a0, b0).
simpl in p0.
rewrite <- p0.
rewrite translateLT1.
rewrite <- (nilTerms _ b0).
unfold freeVarTerms in |- *.
fold (freeVarTerm LNN) in |- *.
rewrite <- app_nil_end.
split.
intros.
decompose record (freeVarSubAllFormula1 _ _ _ _ H).
simpl in H1.
induction H1 as [H0| H0].
rewrite <- H0 in H2.
simpl in H2.
rewrite LNN2LNT_freeVarTerm in H2.
auto with datatypes.
induction H0 as [H0| H0].
rewrite <- H0 in H2.
simpl in H2.
rewrite LNN2LNT_freeVarTerm in H2.
auto with datatypes.
contradiction.
intros.
induction (in_app_or _ _ _ H).
eapply freeVarSubAllFormula2.
simpl in |- *.
left.
reflexivity.
simpl in |- *.
rewrite LNN2LNT_freeVarTerm.
auto.
eapply freeVarSubAllFormula2.
simpl in |- *.
right.
left.
reflexivity.
simpl in |- *.
rewrite LNN2LNT_freeVarTerm.
auto.
simpl in |- *.
induction Hrecf1 as (H, H0).
induction Hrecf0 as (H1, H2).
split.
intros.
apply in_or_app.
induction (in_app_or _ _ _ H3); tauto.
intros.
apply in_or_app.
induction (in_app_or _ _ _ H3); tauto.
assumption.
simpl in |- *.
induction Hrecf as (H, H0).
split.
intros.
apply In_list_remove3.
apply H.
eapply In_list_remove1.
apply H1.
eapply In_list_remove2.
apply H1.
intros.
apply In_list_remove3.
apply H0.
eapply In_list_remove1.
apply H1.
eapply In_list_remove2.
Admitted.

Lemma LNN2LNT_freeVarFormula1 : forall (f : fol.Formula LNN) (v : nat), In v (freeVarFormula LNT (LNN2LNT_formula f)) -> In v (freeVarFormula LNN f).
Proof.
intros.
induction (LNN2LNT_freeVarFormula f v).
Admitted.

Lemma LNN2LNT_freeVarFormula2 : forall (f : fol.Formula LNN) (v : nat), In v (freeVarFormula LNN f) -> In v (freeVarFormula LNT (LNN2LNT_formula f)).
Proof.
intros.
induction (LNN2LNT_freeVarFormula f v).
Admitted.

Lemma LNN2LNT_subTerm : forall (t : fol.Term LNN) (v : nat) (s : fol.Term LNN), LNN2LNT_term (substituteTerm LNN t v s) = substituteTerm LNT (LNN2LNT_term t) v (LNN2LNT_term s).
Proof.
intros.
elim t using Term_Terms_ind with (P0 := fun (n : nat) (ts : fol.Terms LNN n) => LNN2LNT_terms n (substituteTerms LNN n ts v s) = substituteTerms LNT n (LNN2LNT_terms n ts) v (LNN2LNT_term s)).
intros.
simpl in |- *.
induction (eq_nat_dec v n); auto.
simpl in |- *.
intros.
rewrite H.
reflexivity.
reflexivity.
simpl in |- *.
intros.
rewrite H.
rewrite H0.
Admitted.

Lemma LNN2LNT_subTerms : forall (n : nat) (ts : fol.Terms LNN n) (v : nat) (s : fol.Term LNN), LNN2LNT_terms n (substituteTerms LNN n ts v s) = substituteTerms LNT n (LNN2LNT_terms n ts) v (LNN2LNT_term s).
Proof.
intros.
induction ts as [| n t ts Hrects].
reflexivity.
simpl in |- *.
rewrite Hrects.
rewrite LNN2LNT_subTerm.
Admitted.

Lemma LNN2LNT_or : forall a b : fol.Formula LNN, LNN2LNT_formula (fol.orH LNN a b) = orH (LNN2LNT_formula a) (LNN2LNT_formula b).
Proof.
reflexivity.
