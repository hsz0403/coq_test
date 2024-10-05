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

Lemma orE : forall (T : System) (f g h : Formula), SysPrf T (orH f g) -> SysPrf T (impH f h) -> SysPrf T (impH g h) -> SysPrf T h.
Proof.
intros.
unfold orH, fol.orH in H.
apply impE with (impH h h).
apply cp1.
apply impE with (impH (notH h) h).
apply impI.
apply impI.
apply contradiction with h.
apply impE with (notH h).
apply Axm; left; right; constructor.
apply Axm; right; constructor.
apply Axm; right; constructor.
apply impI.
apply impE with g.
apply sysWeaken; assumption.
apply impE with (notH f).
apply sysWeaken; assumption.
apply impE with (notH h).
apply cp2.
apply sysWeaken; assumption.
apply Axm; right; constructor.
apply impI.
apply Axm; right; constructor.
