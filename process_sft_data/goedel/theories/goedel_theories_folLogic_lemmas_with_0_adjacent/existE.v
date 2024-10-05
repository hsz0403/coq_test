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

Lemma existE : forall (T : System) (f g : Formula) (v : nat), ~ In_freeVarSys L v T -> ~ In v (freeVarFormula L g) -> SysPrf T (existH v f) -> SysPrf T (impH f g) -> SysPrf T g.
Proof.
intros.
unfold existH, fol.existH in H1.
apply nnE.
apply impE with (fol.notH L (fol.forallH L v (fol.notH L f))).
apply cp2.
apply impI.
apply impE with (forallH v (notH g)).
apply impE with (forallH v (impH (notH g) (notH f))).
exists (nil (A:=Formula)).
exists (FA3 L (notH g) (notH f) v).
contradiction.
apply sysWeaken.
apply forallI.
auto.
apply cp2.
assumption.
apply impE with (notH g).
exists (nil (A:=Formula)).
exists (FA2 L (notH g) v H0).
contradiction.
apply Axm; right; constructor.
assumption.
