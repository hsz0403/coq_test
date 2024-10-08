Require Import Arith.
Require Import Ensembles.
Require Import folProp.
Require Import subAll.
Require Import folLogic3.
Require Export Languages.
Require Export LNT.
Section PA.
Definition PA1 := forallH 0 (notH (equal (Succ (var 0)) Zero)).
Definition PA2 := forallH 1 (forallH 0 (impH (equal (Succ (var 0)) (Succ (var 1))) (equal (var 0) (var 1)))).
Definition PA3 := forallH 0 (equal (Plus (var 0) Zero) (var 0)).
Definition PA4 := forallH 1 (forallH 0 (equal (Plus (var 0) (Succ (var 1))) (Succ (Plus (var 0) (var 1))))).
Definition PA5 := forallH 0 (equal (Times (var 0) Zero) Zero).
Definition PA6 := forallH 1 (forallH 0 (equal (Times (var 0) (Succ (var 1))) (Plus (Times (var 0) (var 1)) (var 0)))).
Definition PA7 (f : Formula) (v : nat) : Formula := close LNT (impH (substituteFormula LNT f v Zero) (impH (forallH v (impH f (substituteFormula LNT f v (Succ (var v))))) (forallH v f))).
Definition InductionSchema (f : Formula) : Prop := exists g : Formula, (exists v : nat, f = PA7 g v).
Definition PA := Ensembles.Add _ (Ensembles.Add _ (Ensembles.Add _ (Ensembles.Add _ (Ensembles.Add _ (Ensembles.Add _ InductionSchema PA1) PA2) PA3) PA4) PA5) PA6.
Definition open := Formula_rec LNT (fun _ => Formula) (fun t t0 : Term => equal t t0) (fun (r : Relations LNT) (ts : Terms (arity LNT (inl (Functions LNT) r))) => atomic LNT r ts) (fun (f : Formula) _ (f0 : Formula) _ => impH f f0) (fun (f : Formula) _ => notH f) (fun (n : nat) _ (recf : Formula) => recf).
End PA.

Lemma PAdec : forall x : Formula, In _ PA x \/ ~ In _ PA x.
intros.
unfold PA in |- *.
induction (formula_dec LNT LNT_dec x PA6).
rewrite a.
left.
right.
constructor.
induction (formula_dec LNT LNT_dec x PA5).
rewrite a.
left.
left; right.
constructor.
induction (formula_dec LNT LNT_dec x PA4).
rewrite a.
left.
do 2 left; right.
constructor.
induction (formula_dec LNT LNT_dec x PA3).
rewrite a.
left.
do 3 left; right.
constructor.
induction (formula_dec LNT LNT_dec x PA2).
rewrite a.
left.
do 4 left; right.
constructor.
induction (formula_dec LNT LNT_dec x PA1).
rewrite a.
left.
do 5 left; right.
constructor.
cut (In Formula InductionSchema x \/ ~ In Formula InductionSchema x).
intros.
induction H as [H| H].
left.
do 6 left.
assumption.
right.
unfold not in |- *; intros.
repeat tauto || induction H0.
clear b b0 b1 b2 b3 b4.
assert (forall y : Formula, (exists f : Formula, (exists v : nat, impH (substituteFormula LNT f v Zero) (impH (forallH v (impH f (substituteFormula LNT f v (Succ (var v))))) (forallH v f)) = y)) \/ ~ (exists f : Formula, (exists v : nat, impH (substituteFormula LNT f v Zero) (impH (forallH v (impH f (substituteFormula LNT f v (Succ (var v))))) (forallH v f)) = y))).
intros.
destruct y as [t t0| r t| f f0| f| n f]; try (right; unfold not in |- *; intros; decompose record H; discriminate H1).
destruct f0 as [t t0| r t| f0 f1| f0| n f0]; try (right; unfold not in |- *; intros; decompose record H; discriminate H1).
destruct f0 as [t t0| r t| f0 f2| f0| n f0]; try (right; unfold not in |- *; intros; decompose record H; discriminate H1).
destruct f1 as [t t0| r t| f1 f2| f1| n0 f1]; try (right; unfold not in |- *; intros; decompose record H; discriminate H1).
do 4 fold impH in |- *.
do 4 fold forallH in |- *.
induction (formula_dec LNT LNT_dec (substituteFormula LNT f1 n0 Zero) f).
rewrite <- a.
clear a f.
destruct f0 as [t t0| r t| f f0| f| n1 f]; try (right; unfold not in |- *; intros; decompose record H; discriminate H1).
induction (formula_dec LNT LNT_dec f1 f).
rewrite <- a.
clear a f.
induction (formula_dec LNT LNT_dec (substituteFormula LNT f1 n0 (Succ (var n0))) f0).
rewrite <- a.
clear a f0.
induction (eq_nat_dec n n0).
rewrite a.
left.
exists f1.
exists n0.
reflexivity.
right; unfold not in |- *; intros; apply b; decompose record H.
inversion H1.
auto.
right; unfold not in |- *; intros; apply b; decompose record H.
inversion H1.
auto.
right; unfold not in |- *; intros; apply b; decompose record H.
inversion H1.
auto.
right; unfold not in |- *; intros; apply b; decompose record H.
inversion H1.
auto.
induction (formula_dec LNT LNT_dec x (close LNT (open x))).
induction (H (open x)).
left.
unfold In, InductionSchema, PA7 in |- *.
decompose record H0.
exists x0.
exists x1.
rewrite H2.
assumption.
right.
unfold not in |- *; intros; apply H0.
unfold In, InductionSchema, PA7 in H1.
decompose record H1.
exists x0.
exists x1.
rewrite H3.
unfold close in |- *.
induction (ListExt.no_dup nat eq_nat_dec (freeVarFormula LNT (impH (substituteFormula LNT x0 x1 Zero) (impH (forallH x1 (impH x0 (substituteFormula LNT x0 x1 (Succ (var x1))))) (forallH x1 x0))))).
simpl in |- *.
reflexivity.
simpl in |- *.
assumption.
right.
unfold not in |- *; intros; apply b.
unfold In, InductionSchema, PA7 in H0.
decompose record H0.
rewrite H2.
replace (open (close LNT (impH (substituteFormula LNT x0 x1 Zero) (impH (forallH x1 (impH x0 (substituteFormula LNT x0 x1 (Succ (var x1))))) (forallH x1 x0))))) with (impH (substituteFormula LNT x0 x1 Zero) (impH (forallH x1 (impH x0 (substituteFormula LNT x0 x1 (Succ (var x1))))) (forallH x1 x0))).
reflexivity.
unfold close in |- *.
induction (ListExt.no_dup nat eq_nat_dec (freeVarFormula LNT (impH (substituteFormula LNT x0 x1 Zero) (impH (forallH x1 (impH x0 (substituteFormula LNT x0 x1 (Succ (var x1))))) (forallH x1 x0))))).
simpl in |- *.
reflexivity.
simpl in |- *.
auto.
