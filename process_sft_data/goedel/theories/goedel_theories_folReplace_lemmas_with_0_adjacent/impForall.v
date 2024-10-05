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

Lemma impForall : forall (f1 f2 : Formula) (v : nat) (T : System), ~ In_freeVarSys _ v T -> SysPrf T (impH f1 f2) -> SysPrf T (impH (forallH v f1) (forallH v f2)).
Proof.
intros.
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H1 as (x, H1); induction H1 as (H1, H2).
induction H2 as [x H2| x H2]; [ idtac | induction H2 ].
apply H.
unfold In_freeVarSys in |- *.
exists x.
auto.
apply (In_list_remove2 _ _ _ _ _ H1).
auto.
apply impE with f1.
apply sysWeaken.
apply H0.
eapply forallSimp.
apply Axm; right; constructor.
