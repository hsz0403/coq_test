Require Import folProof.
Require Import Arith.
Require Import folProp.
Require Import LNN.
Require Import Coq.Lists.List.
Definition wConsistent (T : System) := forall (f : Formula) (v : nat), (forall x : nat, In x (freeVarFormula LNN f) -> v = x) -> SysPrf T (existH v (notH f)) -> exists n : nat, ~ SysPrf T (substituteFormula LNN f v (natToTerm n)).
Definition wInconsistent (T : System) := exists f : Formula, (exists v : nat, (forall x : nat, In x (freeVarFormula LNN f) -> v = x) /\ SysPrf T (existH v (notH f)) /\ (forall n : nat, SysPrf T (substituteFormula LNN f v (natToTerm n)))).

Lemma notCon2wNotCon : forall T : System, Inconsistent LNN T -> wInconsistent T.
Proof.
intros.
unfold wInconsistent in |- *.
exists (equal Zero Zero).
exists 0.
split.
intros.
elim H0.
split.
apply H.
intros.
apply H.
