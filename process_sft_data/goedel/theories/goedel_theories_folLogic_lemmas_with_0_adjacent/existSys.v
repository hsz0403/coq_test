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

Lemma existSys : forall (T : System) (f g : Formula) (v : nat), ~ In_freeVarSys L v T -> ~ In v (freeVarFormula L g) -> SysPrf (Ensembles.Add _ T f) g -> SysPrf (Ensembles.Add _ T (existH v f)) g.
Proof.
intros.
eapply existE.
unfold not in |- *; intros; elim H.
induction H2 as (x, H2).
exists x.
induction H2 as (H2, H3).
split.
apply H2.
induction H3 as [x H3| x H3].
assumption.
induction H3.
simpl in H2.
absurd (v = v).
eapply In_list_remove2.
apply H2.
auto.
assumption.
apply Axm; right; constructor.
apply sysWeaken.
apply impI.
assumption.
