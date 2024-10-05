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

Lemma nForall : forall (T : System) (f : Formula) (v : nat), SysPrf T (existH v (notH f)) -> SysPrf T (notH (forallH v f)).
Proof.
intros.
apply impE with (existH v (notH f)).
apply sysExtend with (Empty_set Formula).
unfold Included in |- *.
intros.
induction H0.
apply impI.
apply existSys.
unfold not in |- *; intros.
induction H0 as (x, H0); induction H0 as (H0, H1).
induction H1.
simpl in |- *.
unfold not in |- *; intro.
absurd (v = v).
eapply In_list_remove2.
apply H0.
reflexivity.
apply impE with (notH f).
apply cp2.
apply sysWeaken.
apply impI.
eapply forallSimp.
apply Axm; right; constructor.
apply Axm; right; constructor.
assumption.
