Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import ListExt.
Require Import folProof.
Require Import folProp.
Require Import Deduction.
Section Logic_Rules.
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
Let Prf := Prf L.
Let SysPrf := SysPrf L.
Section Not_Rules.
End Not_Rules.
Section Other_Rules.
End Other_Rules.
End Logic_Rules.

Lemma openClosed : forall (T : System) (f : Formula), SysPrf T (close L f) -> SysPrf T f.
Proof.
intros T f.
unfold close in |- *.
generalize (no_dup nat Peano_dec.eq_nat_dec (freeVarFormula L f)).
intros.
induction l as [| a l Hrecl].
apply H.
simpl in H.
apply Hrecl.
eapply forallSimp.
apply H.
