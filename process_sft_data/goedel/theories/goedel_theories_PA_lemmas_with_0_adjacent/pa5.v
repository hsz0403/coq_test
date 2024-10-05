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

Lemma pa5 : forall a : Term, SysPrf PA (equal (Times a Zero) Zero).
Proof.
intros.
replace (equal (Times a Zero) Zero) with (substituteFormula LNT (equal (Times (var 0) Zero) Zero) 0 a).
apply forallE.
apply Axm; repeat (try right; constructor) || left.
reflexivity.
