Require Import Arith.
Require Import Coq.Lists.List.
Require Import ListExt.
Require Import folProp.
Require Import subProp.
Require Import extEqualNat.
Require Import LNN.
Section RepresentableExpressible.
Variable T : System.
Hypothesis closedT1: (ClosedSystem LNN T).
Fixpoint RepresentableHalf1 (n : nat) : naryFunc n -> Formula -> Prop := match n return (naryFunc n -> Formula -> Prop) with | O => fun (f : naryFunc 0) (A : Formula) => SysPrf T (impH A (equal (var 0) (natToTerm f))) | S m => fun (f : naryFunc (S m)) (A : Formula) => forall a : nat, RepresentableHalf1 m (f a) (substituteFormula LNN A (S m) (natToTerm a)) end.
Fixpoint RepresentableHalf2 (n : nat) : naryFunc n -> Formula -> Prop := match n return (naryFunc n -> Formula -> Prop) with | O => fun (f : naryFunc 0) (A : Formula) => SysPrf T (impH (equal (var 0) (natToTerm f)) A) | S m => fun (f : naryFunc (S m)) (A : Formula) => forall a : nat, RepresentableHalf2 m (f a) (substituteFormula LNN A (S m) (natToTerm a)) end.
Fixpoint RepresentableHelp (n : nat) : naryFunc n -> Formula -> Prop := match n return (naryFunc n -> Formula -> Prop) with | O => fun (f : naryFunc 0) (A : Formula) => SysPrf T (iffH A (equal (var 0) (natToTerm f))) | S m => fun (f : naryFunc (S m)) (A : Formula) => forall a : nat, RepresentableHelp m (f a) (substituteFormula LNN A (S m) (natToTerm a)) end.
Definition Representable (n : nat) (f : naryFunc n) (A : Formula) : Prop := (forall v : nat, In v (freeVarFormula LNN A) -> v <= n) /\ RepresentableHelp n f A.
Fixpoint ExpressibleHelp (n : nat) : naryRel n -> Formula -> Prop := match n return (naryRel n -> Formula -> Prop) with | O => fun (R : naryRel 0) (A : Formula) => match R with | true => SysPrf T A | false => SysPrf T (notH A) end | S m => fun (R : naryRel (S m)) (A : Formula) => forall a : nat, ExpressibleHelp m (R a) (substituteFormula LNN A (S m) (natToTerm a)) end.
Definition Expressible (n : nat) (R : naryRel n) (A : Formula) : Prop := (forall v : nat, In v (freeVarFormula LNN A) -> v <= n /\ v <> 0) /\ ExpressibleHelp n R A.
Hypothesis nn1:(SysPrf T (notH (equal (natToTerm 1) (natToTerm 0)))).
End RepresentableExpressible.

Lemma RepresentableAlternate : forall (n : nat) (f : naryFunc n) (A B : Formula), SysPrf T (iffH A B) -> RepresentableHelp n f A -> RepresentableHelp n f B.
Proof.
intros n.
induction n as [| n Hrecn]; intros.
simpl in |- *.
simpl in H0.
apply iffTrans with A.
apply iffSym.
auto.
auto.
simpl in |- *.
simpl in H0.
intros.
apply Hrecn with (substituteFormula LNN A (S n) (natToTerm a)).
rewrite <- (subFormulaIff LNN).
apply forallE.
apply forallI.
apply closedT.
auto.
apply H0.
