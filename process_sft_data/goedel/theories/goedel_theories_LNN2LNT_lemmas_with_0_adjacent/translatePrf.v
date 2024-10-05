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

Lemma translatePrf : forall f, forall axm, Prf LNN axm f -> (forall g, In g axm -> mem _ U g) -> exists Axm : Formulas, (exists prf : Prf LNT Axm (LNN2LNT_formula f), (forall g : Formula, In g Axm -> mem _ V g)) /\ forall v, In v (freeVarListFormula LNT Axm) -> (In v (freeVarListFormula LNN axm)).
Proof.
intros f x x0 H.
induction x0 as [A| Axm1 Axm2 A B x0_1 Hrecx0_1 x0_0 Hrecx0_0| Axm A v n x0 Hrecx0| A B| A B C| A B| A v t| A v n| A B v| | | | R| f].
destruct (AxiomsOK A).
auto with *.
exists x.
destruct H0.
split.
apply H0.
intros.
simpl.
rewrite <- app_nil_end.
apply H1.
apply H2.
assert (forall g : fol.Formula LNN, In g Axm2 -> mem (fol.Formula LNN) U g).
intros.
apply H.
apply in_or_app.
auto.
assert (forall g : fol.Formula LNN, In g Axm1 -> mem (fol.Formula LNN) U g).
intros.
apply H.
apply in_or_app.
auto.
destruct (Hrecx0_0 H0) as [x [[x0 I0] Z0]].
destruct (Hrecx0_1 H1) as [x1 [[x2 I1] Z1]].
clear H0 H1.
rename I0 into H0.
rename I1 into H1.
exists (x1 ++ x).
simpl in x2.
split.
exists (MP LNT _ _ _ _ x2 x0).
intros.
induction (in_app_or _ _ _ H2); auto.
intros.
rewrite freeVarListFormulaApp.
rewrite freeVarListFormulaApp in H2.
apply in_or_app.
destruct (in_app_or _ _ _ H2); auto with *.
destruct (Hrecx0 H) as [x [[x1 H0] Z]].
exists x.
assert (~ In v (freeVarListFormula LNT x)).
firstorder.
split.
exists (GEN LNT _ _ _ H1 x1).
assumption.
assumption.
exists (nil (A:=Formula)).
split.
exists (IMP1 LNT (LNN2LNT_formula A) (LNN2LNT_formula B)).
contradiction.
contradiction.
exists (nil (A:=Formula)).
split.
exists (IMP2 LNT (LNN2LNT_formula A) (LNN2LNT_formula B) (LNN2LNT_formula C)).
contradiction.
contradiction.
exists (nil (A:=Formula)).
split.
exists (CP LNT (LNN2LNT_formula A) (LNN2LNT_formula B)).
contradiction.
contradiction.
assert (SysPrf (Empty_set _) (LNN2LNT_formula (fol.impH LNN (fol.forallH LNN v A) (substituteFormula LNN A v t)))).
simpl in |- *.
apply impE with (impH (forallH v (LNN2LNT_formula A)) (substituteFormula LNT (LNN2LNT_formula A) v (LNN2LNT_term t))).
apply iffE1.
apply (reduceImp LNT).
apply iffRefl.
apply iffSym.
apply LNN2LNT_subFormula.
exists (nil (A:=Formula)).
exists (FA1 LNT (LNN2LNT_formula A) v (LNN2LNT_term t)).
contradiction.
destruct H0.
exists x.
split.
destruct H0.
exists x0.
intros.
elim (H0 g H1).
intros.
destruct H0.
destruct x.
assumption.
assert (In f (f::x)).
auto with *.
elim (H0 f H2).
exists (nil (A:=Formula)).
assert (~ In v (freeVarFormula LNT (LNN2LNT_formula A))).
unfold not in |- *; intros; elim n.
apply LNN2LNT_freeVarFormula1.
auto.
split.
exists (FA2 LNT (LNN2LNT_formula A) v H0).
contradiction.
contradiction.
exists (nil (A:=Formula)).
split.
exists (FA3 LNT (LNN2LNT_formula A) (LNN2LNT_formula B) v).
contradiction.
contradiction.
exists (nil (A:=Formula)).
split.
exists (EQ1 LNT).
contradiction.
contradiction.
exists (nil (A:=Formula)).
split.
exists (EQ2 LNT).
contradiction.
contradiction.
exists (nil (A:=Formula)).
split.
exists (EQ3 LNT).
contradiction.
contradiction.
assert (SysPrf (Empty_set _) (LNN2LNT_formula (AxmEq4 LNN R))).
induction R.
simpl in |- *.
repeat apply impI.
unfold notH, impH in |- *.
apply impE with (iffH (translateLT (Tcons LNN 1 (fol.var LNN 2) (Tcons LNN 0 (fol.var LNN 0) (Tnil LNN)))) (translateLT (Tcons LNN 1 (fol.var LNN 3) (Tcons LNN 0 (fol.var LNN 1) (Tnil LNN))))).
apply impRefl.
repeat rewrite translateLT1.
simpl in |- *.
unfold newVar in |- *.
simpl in |- *.
apply impE with (iffH (existH 3 (equal (Plus (var 2) (Succ (var 3))) (var 0))) (existH 4 (equal (Plus (var 3) (Succ (var 4))) (var 1)))).
apply impRefl.
eapply iffTrans with (existH 4 (substituteFormula LNT (equal (Plus (var 2) (Succ (var 3))) (var 0)) 3 (var 4))).
apply (rebindExist LNT).
simpl in |- *.
unfold not in |- *; intros.
decompose sum H0.
discriminate H1.
discriminate H2.
apply (reduceExist LNT).
unfold not in |- *; intros.
induction H0 as (x, H0); induction H0 as (H0, H1).
induction H1 as [x H1| x H1]; [ induction H1 as [x H1| x H1] | induction H1 ].
elim H1.
induction H1.
simpl in H0.
decompose sum H0.
discriminate H1.
discriminate H2.
simpl in H0.
decompose sum H0.
discriminate H1.
discriminate H2.
repeat rewrite (subFormulaEqual LNT).
simpl in |- *.
apply iffI.
apply impI.
apply eqTrans with (var 0).
apply eqTrans with (Plus (var 2) (Succ (var 4))).
apply eqPlus.
apply eqSym.
apply Axm.
left.
left.
right.
constructor.
apply eqRefl.
apply Axm.
right; constructor.
apply Axm; left; right; constructor.
apply impI.
apply eqTrans with (var 1).
apply eqTrans with (Plus (var 3) (Succ (var 4))).
fold (Succ (var 4)) in |- *.
fold (Plus (fol.var LNT 2) (Succ (var 4))) in |- *.
apply eqPlus.
apply Axm.
left.
left.
right.
constructor.
apply eqRefl.
apply Axm.
right; constructor.
apply eqSym.
apply Axm; left; right; constructor.
destruct H0.
exists x.
destruct H0.
split.
exists x0.
intros.
elim (H0 g H1).
intros.
destruct x.
assumption.
assert (In f (f::x)).
auto with *.
elim (H0 _ H2).
replace (LNN2LNT_formula (AxmEq5 LNN f)) with (AxmEq5 LNT f).
exists (nil (A:=Formula)).
split.
exists (EQ5 LNT f).
contradiction.
contradiction.
induction f; reflexivity.
