Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Peano_dec.
Require Import ListExt.
Require Import folProof.
Require Import folLogic.
Require Import folProp.
Section Replacement.
Variable L : Language.
Let Formula := Formula L.
Let Formulas := Formulas L.
Let System := System L.
Let Term := Term L.
Let Terms := Terms L.
Let var := var L.
Let apply := apply L.
Let equal := equal L.
Let atomic := atomic L.
Let impH := impH L.
Let notH := notH L.
Let forallH := forallH L.
Let orH := orH L.
Let andH := andH L.
Let existH := existH L.
Let iffH := iffH L.
Let ifThenElseH := ifThenElseH L.
Let SysPrf := SysPrf L.
End Replacement.

Lemma reduceCloseList : forall (l : list nat) (f1 f2 : Formula) (T : System), (forall v : nat, In v l -> ~ In_freeVarSys _ v T) -> SysPrf T (iffH f1 f2) -> SysPrf T (iffH (closeList L l f1) (closeList L l f2)).
Proof.
intro.
induction l as [| a l Hrecl]; simpl in |- *; intros.
apply H0.
apply reduceForall.
apply H.
auto.
apply Hrecl; auto.
